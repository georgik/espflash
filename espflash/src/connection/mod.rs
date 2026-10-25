//! Establish a connection with a target device.
//!
//! The [Connection] struct abstracts over the serial connection and
//! sending/decoding of commands, and provides higher-level operations with the
//! device.

use std::{
    collections::HashMap,
    fmt,
    io::{Read, Write},
    iter::zip,
    time::{Duration, Instant},
};

use log::{debug, info};
use regex::Regex;
use serde::{Deserialize, Serialize};
use serialport::{SerialPort, UsbPortInfo};
use slip_codec::SlipDecoder;

#[cfg(unix)]
use self::reset::UnixTightReset;
use self::{
    encoder::SlipEncoder,
    reset::{
        ClassicReset, ResetStrategy, UsbJtagSerialReset, construct_reset_strategy_sequence,
        hard_reset, reset_after_flash, soft_reset,
    },
};
use crate::{
    command::{Command, CommandResponse, CommandResponseValue, CommandType, DEFAULT_MAX_LEN},
    error::{ConnectionError, Error, ResultExt, RomError, RomErrorKind},
    flasher::stubs::CHIP_DETECT_MAGIC_REG_ADDR,
    target::Chip,
};

pub(crate) mod reset;

pub use reset::{ResetAfterOperation, ResetBeforeOperation};

const MAX_CONNECT_ATTEMPTS: usize = 7;
const MAX_SYNC_ATTEMPTS: usize = 5;
const USB_SERIAL_JTAG_PID: u16 = 0x1001;

#[cfg(unix)]
/// Alias for the serial TTYPort.
pub type Port = serialport::TTYPort;
#[cfg(windows)]
/// Alias for the serial COMPort.
pub type Port = serialport::COMPort;

/// Security Info Response containing chip security information
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize, Serialize)]
pub struct SecurityInfo {
    /// 32 bits flags
    pub flags: u32,
    /// 1 byte flash_crypt_cnt
    pub flash_crypt_cnt: u8,
    /// 7 bytes key purposes
    pub key_purposes: [u8; 7],
    /// 32-bit word chip id
    pub chip_id: Option<u32>,
    /// 32-bit word eco version
    pub eco_version: Option<u32>,
}

impl SecurityInfo {
    fn security_flag_map() -> HashMap<&'static str, u32> {
        HashMap::from([
            ("SECURE_BOOT_EN", 1 << 0),
            ("SECURE_BOOT_AGGRESSIVE_REVOKE", 1 << 1),
            ("SECURE_DOWNLOAD_ENABLE", 1 << 2),
            ("SECURE_BOOT_KEY_REVOKE0", 1 << 3),
            ("SECURE_BOOT_KEY_REVOKE1", 1 << 4),
            ("SECURE_BOOT_KEY_REVOKE2", 1 << 5),
            ("SOFT_DIS_JTAG", 1 << 6),
            ("HARD_DIS_JTAG", 1 << 7),
            ("DIS_USB", 1 << 8),
            ("DIS_DOWNLOAD_DCACHE", 1 << 9),
            ("DIS_DOWNLOAD_ICACHE", 1 << 10),
        ])
    }

    pub(crate) fn security_flag_status(&self, flag_name: &str) -> bool {
        if let Some(&flag) = Self::security_flag_map().get(flag_name) {
            (self.flags & flag) != 0
        } else {
            false
        }
    }
}

impl TryFrom<&[u8]> for SecurityInfo {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let esp32s2 = bytes.len() == 12;

        if bytes.len() < 12 {
            return Err(Error::InvalidResponse(format!(
                "expected response of at least 12 bytes, received {} bytes",
                bytes.len()
            )));
        }

        // Parse response bytes
        let flags = u32::from_le_bytes(bytes[0..4].try_into()?);
        let flash_crypt_cnt = bytes[4];
        let key_purposes: [u8; 7] = bytes[5..12].try_into()?;

        let (chip_id, eco_version) = if esp32s2 {
            (None, None) // ESP32-S2 doesn't have these values
        } else {
            if bytes.len() < 20 {
                return Err(Error::InvalidResponse(format!(
                    "expected response of at least 20 bytes, received {} bytes",
                    bytes.len()
                )));
            }
            let chip_id = u32::from_le_bytes(bytes[12..16].try_into()?);
            let eco_version = u32::from_le_bytes(bytes[16..20].try_into()?);
            (Some(chip_id), Some(eco_version))
        };

        Ok(SecurityInfo {
            flags,
            flash_crypt_cnt,
            key_purposes,
            chip_id,
            eco_version,
        })
    }
}

impl fmt::Display for SecurityInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let key_purposes_str = self
            .key_purposes
            .iter()
            .map(|b| format!("{b}"))
            .collect::<Vec<_>>()
            .join(", ");

        writeln!(f, "\nSecurity Information:")?;
        writeln!(f, "=====================")?;
        writeln!(f, "Flags: {:#010x} ({:b})", self.flags, self.flags)?;
        writeln!(f, "Key Purposes: [{key_purposes_str}]")?;

        // Only print Chip ID if it's Some(value)
        if let Some(chip_id) = self.chip_id {
            writeln!(f, "Chip ID: {chip_id}")?;
        }

        // Only print API Version if it's Some(value)
        if let Some(api_version) = self.eco_version {
            writeln!(f, "API Version: {api_version}")?;
        }

        // Secure Boot
        if self.security_flag_status("SECURE_BOOT_EN") {
            writeln!(f, "Secure Boot: Enabled")?;
            if self.security_flag_status("SECURE_BOOT_AGGRESSIVE_REVOKE") {
                writeln!(f, "Secure Boot Aggressive key revocation: Enabled")?;
            }

            let revoked_keys: Vec<_> = [
                "SECURE_BOOT_KEY_REVOKE0",
                "SECURE_BOOT_KEY_REVOKE1",
                "SECURE_BOOT_KEY_REVOKE2",
            ]
            .iter()
            .enumerate()
            .filter(|(_, key)| self.security_flag_status(key))
            .map(|(i, _)| format!("Secure Boot Key{i} is Revoked"))
            .collect();

            if !revoked_keys.is_empty() {
                writeln!(
                    f,
                    "Secure Boot Key Revocation Status:\n  {}",
                    revoked_keys.join("\n  ")
                )?;
            }
        } else {
            writeln!(f, "Secure Boot: Disabled")?;
        }

        // Flash Encryption
        if !self.flash_crypt_cnt.count_ones().is_multiple_of(2) {
            writeln!(f, "Flash Encryption: Enabled")?;
        } else {
            writeln!(f, "Flash Encryption: Disabled")?;
        }

        let crypt_cnt_str = "SPI Boot Crypt Count (SPI_BOOT_CRYPT_CNT)";
        writeln!(f, "{}: 0x{:x}", crypt_cnt_str, self.flash_crypt_cnt)?;

        // Cache Disabling
        if self.security_flag_status("DIS_DOWNLOAD_DCACHE") {
            writeln!(f, "Dcache in UART download mode: Disabled")?;
        }
        if self.security_flag_status("DIS_DOWNLOAD_ICACHE") {
            writeln!(f, "Icache in UART download mode: Disabled")?;
        }

        // JTAG Status
        if self.security_flag_status("HARD_DIS_JTAG") {
            writeln!(f, "JTAG: Permanently Disabled")?;
        } else if self.security_flag_status("SOFT_DIS_JTAG") {
            writeln!(f, "JTAG: Software Access Disabled")?;
        }

        // USB Access
        if self.security_flag_status("DIS_USB") {
            writeln!(f, "USB Access: Disabled")?;
        }

        Ok(())
    }
}

/// An established connection with a target device.
#[derive(Debug)]
pub struct Connection {
    serial: Port,
    port_info: UsbPortInfo,
    decoder: SlipDecoder,
    after_operation: ResetAfterOperation,
    before_operation: ResetBeforeOperation,
    pub(crate) secure_download_mode: bool,
    pub(crate) baud: u32,
    /// Whether the RAM flash stub is currently loaded and serving commands.
    /// The P4 ROM bootloader defers command replies until the next command is
    /// received (one-command pipeline lag), so a follow-up "poke" Sync is
    /// required in ROM mode. The stub replies immediately, so the poke is
    /// unnecessary and actually disrupts it. See
    /// wiki/esp32-p4-slip-attach-failure-report.md.
    pub(crate) stub_mode: bool,
}

impl Connection {
    /// Creates a new connection with a target device.
    pub fn new(
        serial: Port,
        port_info: UsbPortInfo,
        after_operation: ResetAfterOperation,
        before_operation: ResetBeforeOperation,
        baud: u32,
    ) -> Self {
        Connection {
            serial,
            port_info,
            decoder: SlipDecoder::new(),
            after_operation,
            before_operation,
            secure_download_mode: false,
            baud,
            stub_mode: false,
        }
    }

    /// Initializes a connection with a device.
    pub fn begin(&mut self) -> Result<(), Error> {
        let port_name = self.serial.name().unwrap_or_default();
        let reset_sequence = construct_reset_strategy_sequence(
            &port_name,
            self.port_info.pid,
            self.before_operation,
        );

        for (_, reset_strategy) in zip(0..MAX_CONNECT_ATTEMPTS, reset_sequence.iter().cycle()) {
            match self.connect_attempt(reset_strategy.as_ref()) {
                Ok(_) => {
                    return Ok(());
                }
                Err(e) => {
                    debug!("Failed to reset, error {e:#?}, retrying");
                }
            }
        }

        Err(Error::Connection(Box::new(
            ConnectionError::ConnectionFailed,
        )))
    }

    /// Connects to a device.
    fn connect_attempt(&mut self, reset_strategy: &dyn ResetStrategy) -> Result<(), Error> {
        // If we're doing no_sync, we're likely communicating as a pass through
        // with an intermediate device to the ESP32
        if self.before_operation == ResetBeforeOperation::NoResetNoSync {
            return Ok(());
        }
        let mut download_mode: bool = false;
        let mut boot_mode = String::new();
        let mut boot_log_detected = false;
        let mut buff: Vec<u8>;
        if self.before_operation != ResetBeforeOperation::NoReset {
            // Reset the chip to bootloader (download mode)
            reset_strategy.reset(&mut self.serial)?;

            // S2 in USB download mode responds with 0 available bytes here
            let available_bytes = self.serial.bytes_to_read()?;

            buff = vec![0; available_bytes as usize];
            let read_bytes = if available_bytes > 0 {
                let read_bytes = self.serial.read(&mut buff)? as u32;

                if read_bytes != available_bytes {
                    return Err(Error::Connection(Box::new(ConnectionError::ReadMismatch(
                        available_bytes,
                        read_bytes,
                    ))));
                }
                read_bytes
            } else {
                0
            };

            let read_slice = String::from_utf8_lossy(&buff[..read_bytes as usize]).into_owned();

            let pattern =
                Regex::new(r"boot:(0x[0-9a-fA-F]+)([\s\S]*waiting for download)?").unwrap();

            // Search for the pattern in the read data
            if let Some(data) = pattern.captures(&read_slice) {
                boot_log_detected = true;
                // Boot log detected
                boot_mode = data
                    .get(1)
                    .map(|m| m.as_str())
                    .unwrap_or_default()
                    .to_string();
                download_mode = data.get(2).is_some();

                // Further processing or printing the results
                debug!("Boot Mode: {boot_mode}");
                debug!("Download Mode: {download_mode}");
            };
        }

        for _ in 0..MAX_SYNC_ATTEMPTS {
            self.flush()?;

            if self.sync().is_ok() {
                return Ok(());
            }
        }

        if boot_log_detected {
            if download_mode {
                return Err(Error::Connection(Box::new(ConnectionError::NoSyncReply)));
            } else {
                return Err(Error::Connection(Box::new(ConnectionError::WrongBootMode(
                    boot_mode.to_string(),
                ))));
            }
        }

        Err(Error::Connection(Box::new(
            ConnectionError::ConnectionFailed,
        )))
    }

    /// Syncs with a device.
    pub(crate) fn sync(&mut self) -> Result<(), Error> {
        // `command` already sends the command + a Sync "poke", then reads and
        // validates the deferred reply (handles the P4 one-command pipeline lag).
        self.with_timeout(CommandType::Sync.timeout(), |connection| {
            connection.command(Command::Sync)
        })?;

        Ok(())
    }

    /// Resets the device.
    pub fn reset(&mut self) -> Result<(), Error> {
        reset_after_flash(&mut self.serial, self.port_info.pid)?;

        Ok(())
    }

    /// Resets the device taking into account the reset after argument.
    pub fn reset_after(&mut self, is_stub: bool, chip: Chip) -> Result<(), Error> {
        let pid = self.usb_pid();

        match self.after_operation {
            ResetAfterOperation::HardReset => hard_reset(&mut self.serial, pid),
            ResetAfterOperation::NoReset => {
                info!("Staying in bootloader");
                soft_reset(self, true, is_stub)?;

                Ok(())
            }
            ResetAfterOperation::NoResetNoStub => {
                info!("Staying in flasher stub");
                Ok(())
            }
            ResetAfterOperation::WatchdogReset => {
                info!("Resetting device with watchdog");

                match chip {
                    Chip::Esp32c3 | Chip::Esp32c5 => {
                        if self.is_using_usb_serial_jtag() {
                            chip.rtc_wdt_reset(self)?;
                        }
                    }
                    Chip::Esp32p4 => {
                        // Check if the connection is USB OTG
                        if chip.is_using_usb_otg(self)? {
                            chip.rtc_wdt_reset(self)?;
                        }
                    }
                    Chip::Esp32s2 => {
                        // Check if the connection is USB OTG
                        if chip.is_using_usb_otg(self)? {
                            // Check the strapping register to see if we can
                            // perform RTC WDT reset
                            if chip.can_rtc_wdt_reset(self)? {
                                chip.rtc_wdt_reset(self)?;
                            }
                        }
                    }
                    Chip::Esp32s3 => {
                        if self.is_using_usb_serial_jtag() || chip.is_using_usb_otg(self)? {
                            // Check the strapping register to see if we can
                            // perform RTC WDT reset
                            if chip.can_rtc_wdt_reset(self)? {
                                chip.rtc_wdt_reset(self)?;
                            }
                        }
                    }
                    _ => {
                        return Err(Error::UnsupportedFeature {
                            chip,
                            feature: "watchdog reset".into(),
                        });
                    }
                }

                Ok(())
            }
        }
    }

    /// Resets the device to flash mode.
    pub fn reset_to_flash(&mut self, extra_delay: bool) -> Result<(), Error> {
        if self.is_using_usb_serial_jtag() {
            UsbJtagSerialReset.reset(&mut self.serial)
        } else {
            #[cfg(unix)]
            if UnixTightReset::new(extra_delay)
                .reset(&mut self.serial)
                .is_ok()
            {
                return Ok(());
            }

            ClassicReset::new(extra_delay).reset(&mut self.serial)
        }
    }

    /// Sets the timeout for the serial port.
    pub fn set_timeout(&mut self, timeout: Duration) -> Result<(), Error> {
        self.serial.set_timeout(timeout)?;
        Ok(())
    }

    /// Sets the baud rate for the serial port.
    pub fn set_baud(&mut self, baud: u32) -> Result<(), Error> {
        self.serial.set_baud_rate(baud)?;
        self.baud = baud;
        Ok(())
    }

    /// Returns the current baud rate of the serial port.
    pub fn baud(&self) -> Result<u32, Error> {
        Ok(self.serial.baud_rate()?)
    }

    /// Runs a command with a timeout defined by the command type.
    pub fn with_timeout<T, F>(&mut self, timeout: Duration, mut f: F) -> Result<T, Error>
    where
        F: FnMut(&mut Connection) -> Result<T, Error>,
    {
        let old_timeout = {
            let mut binding = Box::new(&mut self.serial);
            let serial = binding.as_mut();
            let old_timeout = serial.timeout();
            serial.set_timeout(timeout)?;
            old_timeout
        };

        let result = f(self);

        self.serial.set_timeout(old_timeout)?;

        result
    }

    /// Reads the response from a serial port.
    pub fn read_flash_response(&mut self) -> Result<Option<CommandResponse>, Error> {
        let mut response = Vec::new();

        self.decoder.decode(&mut self.serial, &mut response)?;

        if response.is_empty() {
            return Ok(None);
        }
        let value = CommandResponseValue::Vector(response.clone());

        let header = CommandResponse {
            resp: 1_u8,
            return_op: CommandType::ReadFlash as u8,
            return_length: response.len() as u16,
            value,
            error: 0_u8,
            status: 0_u8,
        };

        Ok(Some(header))
    }

    /// Reads the response from a serial port for a [`CommandType`].
    pub fn read_response_for_command(
        &mut self,
        ty: CommandType,
    ) -> Result<Option<CommandResponse>, Error> {
        self.read_response_bounded(ty.max_response_len())
            .for_command(ty)
    }

    /// Reads the response from a serial port.
    #[deprecated = "May halt on unexpected input from the port --please use `read_response_for_command` instead. Deprecated in https://github.com/esp-rs/espflash/pull/1007"]
    pub fn read_response(&mut self) -> Result<Option<CommandResponse>, Error> {
        // don't know the command to expect a response for -- use the default
        // max length (the entire flash size)
        self.read_response_bounded(DEFAULT_MAX_LEN)
    }

    fn read_response_bounded(&mut self, max_len: u64) -> Result<Option<CommandResponse>, Error> {
        match self.read_bounded(10, max_len)? {
            None => Ok(None),
            Some(response) => {
                // Here is what esptool does: https://github.com/espressif/esptool/blob/81b2eaee261aed0d3d754e32c57959d6b235bfed/esptool/loader.py#L518
                // from esptool: things are a bit weird here, bear with us

                // We rely on the known and expected response sizes which should
                // be fine for now
                // - if that changes we need to pass the command type we are
                //   parsing the
                // response for.
                //
                // For most commands the response length is 10 (for the stub) or
                // 12 (for ROM code). The MD5 command response
                // is 44 for ROM loader, 26 for the stub.
                //
                // See:
                // - https://docs.espressif.com/projects/esptool/en/latest/esp32/advanced-topics/serial-protocol.html?highlight=md5#response-packet
                // - https://docs.espressif.com/projects/esptool/en/latest/esp32/advanced-topics/serial-protocol.html?highlight=md5#status-bytes
                // - https://docs.espressif.com/projects/esptool/en/latest/esp32/advanced-topics/serial-protocol.html?highlight=md5#verifying-uploaded-data

                let status_len = if response.len() == 10 || response.len() == 26 {
                    2
                } else {
                    4
                };

                let value = match response.len() {
                    10 | 12 => CommandResponseValue::ValueU32(u32::from_le_bytes(
                        response[4..][..4].try_into()?,
                    )),
                    // MD5 is in ASCII
                    44 => CommandResponseValue::ValueU128(u128::from_str_radix(
                        std::str::from_utf8(&response[8..][..32])?,
                        16,
                    )?),
                    // MD5 is BE bytes
                    26 => CommandResponseValue::ValueU128(u128::from_be_bytes(
                        response[8..][..16].try_into()?,
                    )),
                    _ => CommandResponseValue::Vector(response.clone()),
                };

                let header = CommandResponse {
                    resp: response[0],
                    return_op: response[1],
                    return_length: u16::from_le_bytes(response[2..][..2].try_into()?),
                    value,
                    error: response[response.len() - status_len + 1],
                    status: response[response.len() - status_len],
                };

                Ok(Some(header))
            }
        }
    }

    /// Writes raw data to the serial port.
    pub fn write_raw(&mut self, data: u32) -> Result<(), Error> {
        // Same stub-mode caveat as write_command: skip tcdrain in stub mode so we
        // never block on the not-yet-draining RAM flash stub RX endpoint.
        let use_flush = !self.stub_mode;
        let serial = &mut self.serial;

        serial.clear(serialport::ClearBuffer::Input)?;
        let mut buf = Vec::new();
        {
            let mut encoder = SlipEncoder::new(&mut buf)?;
            encoder.write_all(&data.to_le_bytes())?;
            encoder.finish()?;
        }
        serial.write_all(&buf)?;
        if use_flush {
            serial.flush()?;
        }
        Ok(())
    }

    /// Writes a command to the serial port.
    pub fn write_command(&mut self, command: Command<'_>) -> Result<(), Error> {
        debug!("Writing command: {command:02x?}");
        let serial = &mut self.serial;

        serial.clear(serialport::ClearBuffer::Input)?;
        // Encode the full SLIP frame into a Vec so a single write_all() pushes it
        // out. We flush (tcdrain) so the bytes are physically transmitted and we
        // know the chip received them. In ROM mode the ROM bootloader drains the
        // endpoint so tcdrain returns quickly. In stub mode tcdrain only returns
        // once the RAM flash stub has read the bytes -- if it never reads, this
        // hangs, which is itself the diagnostic that the stub is not serving.
        let mut buf = Vec::new();
        {
            let mut encoder = SlipEncoder::new(&mut buf)?;
            command.write(&mut encoder)?;
            encoder.finish()?;
        }
        serial.write_all(&buf)?;
        serial.flush()?;
        debug!("write_command: wrote+flushed OK");
        std::io::stderr().flush().ok();
        Ok(())
    }

    /// Writes a command and reads the response.
    ///
    /// The ESP32-P4 ROM bootloader (and, apparently, its RAM flash stub) defers
    /// the response to a command until the NEXT command is received (one-command
    /// pipeline lag). Sending a follow-up Sync "poke" flushes the queued reply.
    /// A wall-clock deadline guards against a silent chip so we fail fast
    /// instead of blocking forever. See
    /// wiki/esp32-p4-slip-attach-failure-report.md.
    pub fn command(&mut self, command: Command<'_>) -> Result<CommandResponseValue, Error> {
        let ty = command.command_type();
        debug!("command() ty={ty:?} stub_mode={}", self.stub_mode);
        self.write_command(command).for_command(ty)?;
        // The ESP32-P4 ROM defers each reply until the NEXT command is received
        // (one-command pipeline lag), so we send a follow-up Sync "poke" to
        // flush the queued reply. We send the poke in BOTH modes: the P4 RAM
        // flash stub appears to defer replies like the ROM, so without the poke
        // the reply never arrives (stub looked silent). In stub mode we skip the
        // trailing flush() (tcdrain) to avoid the hang, but the poke write is
        // fine. See wiki/esp32-p4-slip-attach-failure-report.md.
        self.write_command(Command::Sync)
            .for_command(CommandType::Sync)?;
        // In ROM mode we flush so the command is fully transmitted before we
        // read. In stub mode we must NOT flush(): right after the OHAI
        // handshake the RAM flash stub is not yet reading commands, so
        // flush() -> tcdrain() blocks forever waiting for the chip to consume
        // the command we just wrote. The stub answers once it is in its command
        // loop; see wiki/esp32-p4-slip-attach-failure-report.md.
        {
            use std::os::unix::fs::OpenOptionsExt;
            if let Ok(mut _f) = std::fs::OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .open("/tmp/dbg_stubmode.txt")
            {
                use std::io::Write;
                let _ = _f.write_all(
                    format!("DBG post-write ty={:?} stub_mode={}\n", ty, self.stub_mode).as_bytes(),
                );
            }
            if !self.stub_mode {
                self.flush()?;
            }
        }

        // A generous wall-clock deadline. The P4 ROM defers each reply until the
        // next command, so after the "poke" the real reply can be delayed; and a
        // priming-sync backlog can leave many stale frames to drain first.
        let deadline = Instant::now() + Duration::from_secs(8);

        let stub_mode = self.stub_mode;
        self.with_timeout(Duration::from_secs(1), |connection| {
            debug!("command() entering read loop for {ty:?} (stub_mode={stub_mode})");
            std::io::stderr().flush().ok();
            let mut stale = 0usize;
            loop {
                match connection.read_response_for_command(ty) {
                    Ok(Some(response)) if response.return_op == ty as u8 => {
                        debug!(
                            "matched {ty:?} response: resp={:#04x} len={}",
                            response.resp, response.return_length
                        );
                        if response.status != 0 {
                            return Err(Error::RomError(Box::new(RomError::new(
                                ty,
                                RomErrorKind::from(response.error),
                            ))));
                        }
                        let value = match response.value {
                            CommandResponseValue::Vector(vec) if vec.len() >= 8 => {
                                let vec = vec[8..][..response.return_length as usize].to_vec();
                                CommandResponseValue::Vector(vec)
                            }
                            _ => response.value,
                        };
                        return Ok(value);
                    }
                    // Stale frame (poke reply / priming-sync leftovers).
                    Ok(_) => {
                        stale += 1;
                        if stale > 256 {
                            break;
                        }
                    }
                    // Timeout on this read -> the reply may just be late.
                    Err(Error::Connection(boxed_ce)) => {
                        match boxed_ce.downcast::<ConnectionError>() {
                            Ok(boxed) if matches!(*boxed, ConnectionError::Timeout(_)) => {
                                stale += 1;
                                if stale > 256 {
                                    break;
                                }
                            }
                            Ok(boxed) => {
                                return Err(Error::Connection(boxed));
                            }
                            Err(original) => {
                                return Err(Error::Connection(original));
                            }
                        }
                    }
                    Err(other) => {
                        return Err(other);
                    }
                }
                if Instant::now() > deadline {
                    debug!("command {ty:?} timed out after poke (no matching reply)");
                    break;
                }
            }
            Err(Error::Connection(Box::new(
                ConnectionError::ConnectionFailed,
            )))
        })
        .for_command(ty)
    }

    /// Reads a register command with a timeout.
    pub fn read_reg(&mut self, addr: u32) -> Result<u32, Error> {
        let resp = self.with_timeout(CommandType::ReadReg.timeout(), |connection| {
            connection.command(Command::ReadReg { address: addr })
        })?;

        resp.try_into()
    }

    /// Writes a register command with a timeout.
    pub fn write_reg(&mut self, addr: u32, value: u32, mask: Option<u32>) -> Result<(), Error> {
        self.with_timeout(CommandType::WriteReg.timeout(), |connection| {
            connection.command(Command::WriteReg {
                address: addr,
                value,
                mask,
            })
        })?;

        Ok(())
    }

    /// Updates a register by applying the new value to the masked out portion
    /// of the old value.
    pub(crate) fn update_reg(&mut self, addr: u32, mask: u32, new_value: u32) -> Result<(), Error> {
        let masked_new_value = new_value.checked_shl(mask.trailing_zeros()).unwrap_or(0) & mask;

        let masked_old_value = self.read_reg(addr)? & !mask;

        self.write_reg(addr, masked_old_value | masked_new_value, None)
    }

    /// Reads a register command.
    pub(crate) fn read(&mut self, len: usize) -> Result<Option<Vec<u8>>, Error> {
        self.read_bounded(len, u64::MAX)
    }

    /// Reads a register command at most `max_len` bytes long.
    pub(crate) fn read_bounded(
        &mut self,
        len: usize,
        max_len: u64,
    ) -> Result<Option<Vec<u8>>, Error> {
        // Grab the raw fd up front (immutable borrow) so we can poll it without
        // conflicting with the mutable borrow of `serial` below.
        #[cfg(unix)]
        let raw_fd = {
            use std::os::fd::AsRawFd;
            self.serial.as_raw_fd()
        };
        let mut tmp = Vec::with_capacity(1024);
        let mut serial = (&mut self.serial).take(max_len);
        // Wall-clock deadline so a silent device fails fast instead of
        // blocking forever. The serialport read timeout does NOT reliably
        // interrupt the kernel read on this USB-JTAG/serial device (a read can
        // block past the configured timeout when the chip is momentarily
        // silent), so gating decode() on the deadline alone is not enough --
        // decode() can hang before the deadline is ever checked. We therefore
        // poll the raw fd with the *remaining* time before every decode(): this
        // guarantees we never block longer than the deadline and fail fast on
        // POLLERR/POLLHUP. Raised to match command()'s deadline: draining a
        // priming-sync backlog can take a moment before the delayed reply.
        let deadline = Instant::now() + Duration::from_secs(8);
        loop {
            let remaining = deadline
                .checked_duration_since(Instant::now())
                .unwrap_or_default();
            if remaining.is_zero() {
                return Ok(None);
            }
            let timeout_ms = remaining.as_millis().min(i32::MAX as u128) as i32;
            #[cfg(unix)]
            {
                let mut pfd = libc::pollfd {
                    fd: raw_fd,
                    events: libc::POLLIN,
                    revents: 0,
                };
                let rc = unsafe { libc::poll(&mut pfd, 1, timeout_ms) };
                if rc < 0 {
                    let err = std::io::Error::last_os_error();
                    if err.kind() != std::io::ErrorKind::Interrupted {
                        return Err(Error::Connection(Box::new(ConnectionError::from(err))));
                    }
                    continue; // EINTR: re-poll
                }
                if pfd.revents & (libc::POLLERR | libc::POLLHUP | libc::POLLNVAL) != 0 {
                    return Err(Error::Connection(Box::new(ConnectionError::from(
                        std::io::Error::new(
                            std::io::ErrorKind::UnexpectedEof,
                            "serial device hangup",
                        ),
                    ))));
                }
                if pfd.revents & libc::POLLIN == 0 {
                    // Timed out waiting for data -> silent device.
                    debug!("poll: no data within deadline (timeout_ms={timeout_ms})");
                    std::io::stderr().flush().ok();
                    return Ok(None);
                }
            }
            // Data is ready -> decode the next frame's worth.
            self.decoder.decode(&mut serial, &mut tmp)?;
            debug!("RX {:02x?}", tmp);
            if tmp.len() >= len {
                return Ok(Some(tmp));
            }
        }
    }

    /// Flushes  the serial port.
    pub fn flush(&mut self) -> Result<(), Error> {
        debug!("flush() called");
        std::io::stderr().flush().ok();
        self.serial.flush()?;
        debug!("flush() done");
        std::io::stderr().flush().ok();
        Ok(())
    }

    /// Turns a serial port into a [Port].
    pub fn into_serial(self) -> Port {
        self.serial
    }

    /// Returns the USB PID of the serial port.
    pub fn usb_pid(&self) -> u16 {
        self.port_info.pid
    }

    /// Returns if the connection is using USB serial JTAG.
    pub(crate) fn is_using_usb_serial_jtag(&self) -> bool {
        self.port_info.pid == USB_SERIAL_JTAG_PID
    }

    /// Returns the reset after operation.
    pub fn after_operation(&self) -> ResetAfterOperation {
        self.after_operation
    }

    /// Returns the reset before operation.
    pub fn before_operation(&self) -> ResetBeforeOperation {
        self.before_operation
    }

    /// Gets security information from the chip.
    #[cfg(feature = "serialport")]
    pub fn security_info(&mut self, use_stub: bool) -> Result<SecurityInfo, crate::error::Error> {
        self.with_timeout(CommandType::GetSecurityInfo.timeout(), |connection| {
            let response = connection.command(Command::GetSecurityInfo)?;
            // Extract raw bytes and convert them into `SecurityInfo`
            if let crate::command::CommandResponseValue::Vector(data) = response {
                // The payload ends with the status bytes: 2 for the stub, 4 for
                // the ROM loader.
                let status_len = if use_stub { 2 } else { 4 };
                SecurityInfo::try_from(&data[..data.len().saturating_sub(status_len)])
            } else {
                Err(Error::InvalidResponse(
                    "response was not a vector of bytes".into(),
                ))
            }
        })
    }

    /// Detects which chip is connected to this connection.
    #[cfg(feature = "serialport")]
    pub fn detect_chip(
        &mut self,
        use_stub: bool,
    ) -> Result<crate::target::Chip, crate::error::Error> {
        match self.security_info(use_stub) {
            Ok(info) if info.chip_id.is_some() => {
                let chip_id = info.chip_id.unwrap() as u16;
                let chip = Chip::try_from(chip_id)?;

                Ok(chip)
            }
            _ => {
                // Fall back to reading the magic value from the chip
                let magic = if use_stub {
                    self.with_timeout(CommandType::ReadReg.timeout(), |connection| {
                        connection.command(Command::ReadReg {
                            address: CHIP_DETECT_MAGIC_REG_ADDR,
                        })
                    })?
                    .try_into()?
                } else {
                    self.read_reg(CHIP_DETECT_MAGIC_REG_ADDR)?
                };
                debug!("Read chip magic value: 0x{magic:08x}");
                Chip::from_magic(magic)
            }
        }
    }
}

impl From<Connection> for Port {
    fn from(conn: Connection) -> Self {
        conn.into_serial()
    }
}

mod encoder {
    use std::io::Write;

    use serde::Serialize;

    const END: u8 = 0xC0;
    const ESC: u8 = 0xDB;
    const ESC_END: u8 = 0xDC;
    const ESC_ESC: u8 = 0xDD;

    /// Encoder for the SLIP protocol.
    #[derive(Debug, PartialEq, Eq, Serialize, Hash)]
    pub struct SlipEncoder<'a, W: Write> {
        writer: &'a mut W,
        len: usize,
    }

    impl<'a, W: Write> SlipEncoder<'a, W> {
        /// Creates a new encoder context.
        pub fn new(writer: &'a mut W) -> std::io::Result<Self> {
            let len = writer.write(&[END])?;
            Ok(Self { writer, len })
        }

        /// Finishes the encoding.
        pub fn finish(mut self) -> std::io::Result<usize> {
            self.len += self.writer.write(&[END])?;
            Ok(self.len)
        }
    }

    impl<W: Write> Write for SlipEncoder<'_, W> {
        /// Writes the given buffer replacing the END and ESC bytes.
        ///
        /// See <https://docs.espressif.com/projects/esptool/en/latest/esp32c3/advanced-topics/serial-protocol.html#low-level-protocol>
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            for value in buf.iter() {
                match *value {
                    END => {
                        self.len += self.writer.write(&[ESC, ESC_END])?;
                    }
                    ESC => {
                        self.len += self.writer.write(&[ESC, ESC_ESC])?;
                    }
                    _ => {
                        self.len += self.writer.write(&[*value])?;
                    }
                }
            }

            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            self.writer.flush()
        }
    }
}
