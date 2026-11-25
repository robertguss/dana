//! Pure-Rust PKZIP reader/writer and IEEE CRC-32 (`0xEDB88320`) with strict path-traversal
//! validation, CRC-32 + uncompressed-length verification, and zip-bomb size caps.
//!
//! Uses only [`crate::ffi::raw_deflate`] and [`crate::ffi::raw_inflate`] for `DEFLATED (8)`
//! entries; compiles under `#[forbid(unsafe_code)]` via `src/lib.rs`.

use std::fmt;

use crate::ffi::{raw_deflate, raw_inflate};

const LOCAL_FILE_HEADER_SIG: u32 = 0x0403_4B50;
const CENTRAL_DIR_HEADER_SIG: u32 = 0x0201_4B50;
const EOCD_SIG: u32 = 0x0605_4B50;

const METHOD_STORED: u16 = 0;
const METHOD_DEFLATED: u16 = 8;

/// General-purpose bit flag: entry is encrypted.
const FLAG_ENCRYPTED: u16 = 0x0001;
/// General-purpose bit flag: CRC/sizes appear in a trailing data descriptor (true sizes live in Central Directory).
const FLAG_DATA_DESCRIPTOR: u16 = 0x0008;
/// General-purpose bit flag: UTF-8 filename encoding.
const FLAG_UTF8: u16 = 0x0800;

/// Default maximum decompressed size of any single ZIP entry (64 MiB).
pub const DEFAULT_MAX_ZIP_ENTRY_BYTES: usize = 64 * 1024 * 1024;
/// Default maximum cumulative decompressed size across an entire ZIP archive (64 MiB).
pub const DEFAULT_MAX_ZIP_TOTAL_BYTES: usize = 64 * 1024 * 1024;
/// Default maximum number of entries permitted in a ZIP archive.
pub const DEFAULT_MAX_ZIP_ENTRIES: usize = 10_000;

/// Compile-time IEEE 802.3 CRC-32 lookup table (reversed polynomial `0xEDB88320`).
const CRC32_TABLE: [u32; 256] = {
    let mut table = [0u32; 256];
    let mut i = 0usize;
    while i < 256 {
        let mut crc = i as u32;
        let mut bit = 0;
        while bit < 8 {
            if (crc & 1) != 0 {
                crc = (crc >> 1) ^ 0xEDB8_8320;
            } else {
                crc >>= 1;
            }
            bit += 1;
        }
        table[i] = crc;
        i += 1;
    }
    table
};

/// Compute the IEEE 802.3 CRC-32 (`0xEDB88320`) checksum of `bytes`.
#[must_use]
pub fn crc32(bytes: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &b in bytes {
        let idx = ((crc ^ u32::from(b)) & 0xFF) as usize;
        crc = (crc >> 8) ^ CRC32_TABLE[idx];
    }
    !crc
}

/// Typed error for PKZIP archive parsing, validation, and writing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZipError {
    pub message: String,
}

impl ZipError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for ZipError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ZipError {}

/// Security limits enforced while reading a PKZIP archive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZipLimits {
    pub max_entry_bytes: usize,
    pub max_total_bytes: usize,
    pub max_entries: usize,
}

impl Default for ZipLimits {
    fn default() -> Self {
        Self {
            max_entry_bytes: DEFAULT_MAX_ZIP_ENTRY_BYTES,
            max_total_bytes: DEFAULT_MAX_ZIP_TOTAL_BYTES,
            max_entries: DEFAULT_MAX_ZIP_ENTRIES,
        }
    }
}

/// Supported PKZIP entry compression methods.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZipCompression {
    Stored,
    Deflated,
}

/// Validate a PKZIP entry name against path-traversal and malformed-path attacks.
///
/// Rejects empty names, NUL bytes, leading `/`, any `\`, Windows drive prefixes (`C:`),
/// and any `..` path segment.
///
/// # Errors
/// Returns [`ZipError`] if the entry path is unsafe.
pub fn validate_zip_entry_name(name: &str) -> Result<(), ZipError> {
    if name.is_empty() {
        return Err(ZipError::new("ZIP entry name cannot be empty"));
    }
    if name.contains('\0') {
        return Err(ZipError::new("ZIP entry name contains NUL byte"));
    }
    if name.starts_with('/') {
        return Err(ZipError::new(format!(
            "ZIP entry `{name}` has forbidden leading `/`"
        )));
    }
    if name.contains('\\') {
        return Err(ZipError::new(format!(
            "ZIP entry `{name}` contains forbidden backslash `\\`"
        )));
    }
    let bytes = name.as_bytes();
    if bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
        return Err(ZipError::new(format!(
            "ZIP entry `{name}` contains forbidden drive prefix"
        )));
    }
    for seg in name.split('/') {
        if seg == ".." {
            return Err(ZipError::new(format!(
                "ZIP entry `{name}` contains forbidden `..` path traversal"
            )));
        }
    }
    Ok(())
}

/// Decoded, CRC-verified in-memory PKZIP archive.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ZipArchive {
    entries: Vec<(String, Vec<u8>)>,
}

impl ZipArchive {
    /// Parse and verify a PKZIP archive from `bytes` using [`ZipLimits::default`].
    ///
    /// # Errors
    /// Returns [`ZipError`] on malformed headers, unsupported compression/encryption,
    /// path traversal, CRC-32 mismatch, uncompressed size mismatch, or size-limit breach.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ZipError> {
        Self::from_bytes_with_limits(bytes, ZipLimits::default())
    }

    /// Parse and verify a PKZIP archive from `bytes` enforcing explicit [`ZipLimits`].
    ///
    /// # Errors
    /// Returns [`ZipError`] on malformed headers, path traversal, CRC-32 / size mismatch,
    /// or zip-bomb limit violation.
    pub fn from_bytes_with_limits(bytes: &[u8], limits: ZipLimits) -> Result<Self, ZipError> {
        let eocd_pos = find_eocd(bytes)?;
        let disk_no = read_u16_le(bytes, eocd_pos + 4)?;
        let cd_disk = read_u16_le(bytes, eocd_pos + 6)?;
        let disk_entries = read_u16_le(bytes, eocd_pos + 8)?;
        let total_entries = read_u16_le(bytes, eocd_pos + 10)?;
        let cd_size = read_u32_le(bytes, eocd_pos + 12)?;
        let cd_offset = read_u32_le(bytes, eocd_pos + 16)?;

        if disk_no != 0 || cd_disk != 0 || disk_entries != total_entries {
            return Err(ZipError::new("multi-disk ZIP archives are not supported"));
        }
        if total_entries == u16::MAX || cd_size == u32::MAX || cd_offset == u32::MAX {
            return Err(ZipError::new("ZIP64 archives are not supported"));
        }
        let entry_count = usize::from(total_entries);
        if entry_count > limits.max_entries {
            return Err(ZipError::new(format!(
                "ZIP archive entry count ({entry_count}) exceeds limit ({})",
                limits.max_entries
            )));
        }

        let cd_start = usize::try_from(cd_offset)
            .map_err(|_| ZipError::new("ZIP central directory offset overflow"))?;
        let cd_len = usize::try_from(cd_size)
            .map_err(|_| ZipError::new("ZIP central directory size overflow"))?;
        let cd_end = cd_start
            .checked_add(cd_len)
            .ok_or_else(|| ZipError::new("ZIP central directory bounds overflow"))?;
        if cd_end > eocd_pos || cd_end > bytes.len() {
            return Err(ZipError::new(
                "ZIP central directory extends past EOCD record",
            ));
        }

        let mut entries = Vec::with_capacity(entry_count);
        let mut cursor = cd_start;
        let mut total_uncompressed: usize = 0;

        for _ in 0..entry_count {
            if cursor + 46 > cd_end {
                return Err(ZipError::new("truncated ZIP central directory header"));
            }
            let sig = read_u32_le(bytes, cursor)?;
            if sig != CENTRAL_DIR_HEADER_SIG {
                return Err(ZipError::new(format!(
                    "invalid ZIP central directory signature at offset {cursor}"
                )));
            }
            let flags = read_u16_le(bytes, cursor + 8)?;
            let method = read_u16_le(bytes, cursor + 10)?;
            let expected_crc = read_u32_le(bytes, cursor + 16)?;
            let comp_size = read_u32_le(bytes, cursor + 20)? as usize;
            let uncomp_size = read_u32_le(bytes, cursor + 24)? as usize;
            let name_len = usize::from(read_u16_le(bytes, cursor + 28)?);
            let extra_len = usize::from(read_u16_le(bytes, cursor + 30)?);
            let comment_len = usize::from(read_u16_le(bytes, cursor + 32)?);
            let local_offset = read_u32_le(bytes, cursor + 42)? as usize;

            let name_start = cursor + 46;
            let name_end = name_start
                .checked_add(name_len)
                .ok_or_else(|| ZipError::new("ZIP entry name bounds overflow"))?;
            let next_cursor = name_end
                .checked_add(extra_len)
                .and_then(|v| v.checked_add(comment_len))
                .ok_or_else(|| ZipError::new("ZIP central directory record overflow"))?;
            if next_cursor > cd_end {
                return Err(ZipError::new("truncated ZIP central directory entry"));
            }

            if (flags & FLAG_ENCRYPTED) != 0 {
                return Err(ZipError::new("encrypted ZIP entries are not supported"));
            }

            let name = std::str::from_utf8(&bytes[name_start..name_end])
                .map_err(|_| ZipError::new("ZIP entry name is not valid UTF-8"))?
                .to_string();
            validate_zip_entry_name(&name)?;

            if uncomp_size > limits.max_entry_bytes {
                return Err(ZipError::new(format!(
                    "ZIP entry `{name}` declared size ({uncomp_size}) exceeds limit ({})",
                    limits.max_entry_bytes
                )));
            }
            let remaining_budget = limits.max_total_bytes.saturating_sub(total_uncompressed);
            if uncomp_size > remaining_budget {
                return Err(ZipError::new(format!(
                    "ZIP archive total decompressed size exceeds limit ({})",
                    limits.max_total_bytes
                )));
            }

            // Inspect matching Local File Header
            if local_offset + 30 > bytes.len() {
                return Err(ZipError::new(format!(
                    "ZIP local file header for `{name}` out of bounds"
                )));
            }
            let lf_sig = read_u32_le(bytes, local_offset)?;
            if lf_sig != LOCAL_FILE_HEADER_SIG {
                return Err(ZipError::new(format!(
                    "invalid ZIP local file header signature for `{name}`"
                )));
            }
            let lf_flags = read_u16_le(bytes, local_offset + 6)?;
            let lf_method = read_u16_le(bytes, local_offset + 8)?;
            let lf_crc = read_u32_le(bytes, local_offset + 14)?;
            let lf_comp_size = read_u32_le(bytes, local_offset + 18)? as usize;
            let lf_uncomp_size = read_u32_le(bytes, local_offset + 22)? as usize;
            let lf_name_len = usize::from(read_u16_le(bytes, local_offset + 26)?);
            let lf_extra_len = usize::from(read_u16_le(bytes, local_offset + 28)?);

            if lf_method != method {
                return Err(ZipError::new(format!(
                    "ZIP local/central compression method mismatch for `{name}`"
                )));
            }
            let lf_name_start = local_offset + 30;
            let lf_name_end = lf_name_start
                .checked_add(lf_name_len)
                .ok_or_else(|| ZipError::new("ZIP local header name overflow"))?;
            let data_start = lf_name_end
                .checked_add(lf_extra_len)
                .ok_or_else(|| ZipError::new("ZIP local header extra overflow"))?;
            if data_start > bytes.len() {
                return Err(ZipError::new(format!(
                    "truncated ZIP local header for `{name}`"
                )));
            }
            if &bytes[lf_name_start..lf_name_end] != name.as_bytes() {
                return Err(ZipError::new(format!(
                    "ZIP local/central filename mismatch for `{name}`"
                )));
            }
            if (lf_flags & FLAG_DATA_DESCRIPTOR) == 0
                && (lf_crc != expected_crc
                    || lf_comp_size != comp_size
                    || lf_uncomp_size != uncomp_size)
            {
                return Err(ZipError::new(format!(
                    "ZIP local/central header metadata mismatch for `{name}`"
                )));
            }

            let data_end = data_start
                .checked_add(comp_size)
                .ok_or_else(|| ZipError::new("ZIP entry data bounds overflow"))?;
            if data_end > bytes.len() {
                return Err(ZipError::new(format!(
                    "truncated compressed data for ZIP entry `{name}`"
                )));
            }
            let raw_payload = &bytes[data_start..data_end];

            let entry_cap = limits.max_entry_bytes.min(remaining_budget);
            let decoded = match method {
                METHOD_STORED => {
                    if comp_size != uncomp_size {
                        return Err(ZipError::new(format!(
                            "STORED ZIP entry `{name}` has mismatched compressed/uncompressed sizes"
                        )));
                    }
                    if comp_size > entry_cap {
                        return Err(ZipError::new(format!(
                            "ZIP entry `{name}` exceeds size limit ({entry_cap})"
                        )));
                    }
                    raw_payload.to_vec()
                }
                METHOD_DEFLATED => raw_inflate(raw_payload, entry_cap).map_err(|e| {
                    ZipError::new(format!("failed to inflate ZIP entry `{name}`: {e}"))
                })?,
                other => {
                    return Err(ZipError::new(format!(
                        "unsupported ZIP compression method {other} for `{name}`"
                    )));
                }
            };

            if decoded.len() != uncomp_size {
                return Err(ZipError::new(format!(
                    "ZIP entry `{name}` uncompressed length mismatch: header={uncomp_size}, actual={}",
                    decoded.len()
                )));
            }
            let actual_crc = crc32(&decoded);
            if actual_crc != expected_crc {
                return Err(ZipError::new(format!(
                    "ZIP entry `{name}` CRC-32 mismatch: expected={expected_crc:#010x}, actual={actual_crc:#010x}"
                )));
            }

            total_uncompressed = total_uncompressed
                .checked_add(decoded.len())
                .ok_or_else(|| ZipError::new("ZIP total size overflow"))?;
            if total_uncompressed > limits.max_total_bytes {
                return Err(ZipError::new(format!(
                    "ZIP archive total decompressed size exceeds limit ({})",
                    limits.max_total_bytes
                )));
            }

            entries.push((name, decoded));
            cursor = next_cursor;
        }

        Ok(Self { entries })
    }

    /// Look up an archive entry by exact relative path.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&[u8]> {
        self.entries
            .iter()
            .find(|(k, _)| k == name)
            .map(|(_, v)| v.as_slice())
    }

    /// Look up an archive entry by ASCII case-insensitive relative path (fallback for OOXML generators).
    #[must_use]
    pub fn get_case_insensitive(&self, name: &str) -> Option<&[u8]> {
        if let Some(exact) = self.get(name) {
            return Some(exact);
        }
        self.entries
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_slice())
    }

    /// Return all decoded `(path, bytes)` entries in archive order.
    #[must_use]
    pub fn entries(&self) -> &[(String, Vec<u8>)] {
        &self.entries
    }
}

/// Encode `entries` into a deterministic, standard PKZIP archive.
///
/// # Errors
/// Returns [`ZipError`] if any entry name fails path validation, exceeds ZIP32 limits,
/// or fails raw DEFLATE compression.
pub fn write_zip_bytes(
    entries: &[(&str, &[u8])],
    compression: ZipCompression,
) -> Result<Vec<u8>, ZipError> {
    if entries.len() > usize::from(u16::MAX - 1) {
        return Err(ZipError::new("too many ZIP entries for standard ZIP32"));
    }

    struct CdRecord {
        name: Vec<u8>,
        method: u16,
        crc: u32,
        comp_size: u32,
        uncomp_size: u32,
        local_offset: u32,
    }

    let mut out = Vec::new();
    let mut cd_records = Vec::with_capacity(entries.len());

    for &(name, data) in entries {
        validate_zip_entry_name(name)?;
        let name_bytes = name.as_bytes();
        let name_len = u16::try_from(name_bytes.len())
            .map_err(|_| ZipError::new(format!("ZIP entry name `{name}` too long")))?;
        let uncomp_size = u32::try_from(data.len())
            .map_err(|_| ZipError::new(format!("ZIP entry `{name}` exceeds 4 GiB ZIP32 limit")))?;
        let crc = crc32(data);
        let (method, compressed) = match compression {
            ZipCompression::Stored => (METHOD_STORED, data.to_vec()),
            ZipCompression::Deflated => {
                let def = raw_deflate(data).map_err(|e| {
                    ZipError::new(format!("failed to deflate ZIP entry `{name}`: {e}"))
                })?;
                (METHOD_DEFLATED, def)
            }
        };
        let comp_size = u32::try_from(compressed.len()).map_err(|_| {
            ZipError::new(format!(
                "compressed ZIP entry `{name}` exceeds 4 GiB ZIP32 limit"
            ))
        })?;
        let local_offset = u32::try_from(out.len())
            .map_err(|_| ZipError::new("ZIP archive offset exceeds 4 GiB ZIP32 limit"))?;

        // Local File Header (30 bytes + name)
        out.extend_from_slice(&LOCAL_FILE_HEADER_SIG.to_le_bytes());
        out.extend_from_slice(&20u16.to_le_bytes()); // version needed (2.0)
        out.extend_from_slice(&FLAG_UTF8.to_le_bytes());
        out.extend_from_slice(&method.to_le_bytes());
        out.extend_from_slice(&0u16.to_le_bytes()); // DOS time (deterministic)
        out.extend_from_slice(&0x0021u16.to_le_bytes()); // DOS date (1980-01-01)
        out.extend_from_slice(&crc.to_le_bytes());
        out.extend_from_slice(&comp_size.to_le_bytes());
        out.extend_from_slice(&uncomp_size.to_le_bytes());
        out.extend_from_slice(&name_len.to_le_bytes());
        out.extend_from_slice(&0u16.to_le_bytes()); // extra len
        out.extend_from_slice(name_bytes);
        out.extend_from_slice(&compressed);

        cd_records.push(CdRecord {
            name: name_bytes.to_vec(),
            method,
            crc,
            comp_size,
            uncomp_size,
            local_offset,
        });
    }

    let cd_offset = u32::try_from(out.len())
        .map_err(|_| ZipError::new("ZIP central directory offset exceeds 4 GiB"))?;

    for rec in &cd_records {
        let name_len = u16::try_from(rec.name.len())
            .map_err(|_| ZipError::new("ZIP entry name length overflow"))?;
        // Central Directory Header (46 bytes + name)
        out.extend_from_slice(&CENTRAL_DIR_HEADER_SIG.to_le_bytes());
        out.extend_from_slice(&20u16.to_le_bytes()); // version made by
        out.extend_from_slice(&20u16.to_le_bytes()); // version needed
        out.extend_from_slice(&FLAG_UTF8.to_le_bytes());
        out.extend_from_slice(&rec.method.to_le_bytes());
        out.extend_from_slice(&0u16.to_le_bytes()); // DOS time
        out.extend_from_slice(&0x0021u16.to_le_bytes()); // DOS date
        out.extend_from_slice(&rec.crc.to_le_bytes());
        out.extend_from_slice(&rec.comp_size.to_le_bytes());
        out.extend_from_slice(&rec.uncomp_size.to_le_bytes());
        out.extend_from_slice(&name_len.to_le_bytes());
        out.extend_from_slice(&0u16.to_le_bytes()); // extra len
        out.extend_from_slice(&0u16.to_le_bytes()); // comment len
        out.extend_from_slice(&0u16.to_le_bytes()); // disk number start
        out.extend_from_slice(&0u16.to_le_bytes()); // internal attrs
        out.extend_from_slice(&0u32.to_le_bytes()); // external attrs
        out.extend_from_slice(&rec.local_offset.to_le_bytes());
        out.extend_from_slice(&rec.name);
    }

    let cd_size = u32::try_from(out.len() - cd_offset as usize)
        .map_err(|_| ZipError::new("ZIP central directory size exceeds 4 GiB"))?;
    let entry_count = u16::try_from(cd_records.len())
        .map_err(|_| ZipError::new("ZIP entry count exceeds u16"))?;

    // End of Central Directory (22 bytes)
    out.extend_from_slice(&EOCD_SIG.to_le_bytes());
    out.extend_from_slice(&0u16.to_le_bytes()); // disk number
    out.extend_from_slice(&0u16.to_le_bytes()); // cd start disk
    out.extend_from_slice(&entry_count.to_le_bytes());
    out.extend_from_slice(&entry_count.to_le_bytes());
    out.extend_from_slice(&cd_size.to_le_bytes());
    out.extend_from_slice(&cd_offset.to_le_bytes());
    out.extend_from_slice(&0u16.to_le_bytes()); // comment len

    Ok(out)
}

fn find_eocd(bytes: &[u8]) -> Result<usize, ZipError> {
    if bytes.len() < 22 {
        return Err(ZipError::new("ZIP archive too short for EOCD record"));
    }
    let min_pos = bytes.len().saturating_sub(22 + 65_535);
    let mut pos = bytes.len() - 22;
    loop {
        if read_u32_le(bytes, pos)? == EOCD_SIG {
            let comment_len = usize::from(read_u16_le(bytes, pos + 20)?);
            if pos + 22 + comment_len == bytes.len() {
                return Ok(pos);
            }
        }
        if pos == min_pos {
            break;
        }
        pos -= 1;
    }
    Err(ZipError::new(
        "ZIP End-of-Central-Directory (EOCD) signature not found",
    ))
}

fn read_u16_le(bytes: &[u8], offset: usize) -> Result<u16, ZipError> {
    let slice = bytes
        .get(offset..offset + 2)
        .ok_or_else(|| ZipError::new("unexpected EOF reading ZIP u16"))?;
    let arr: [u8; 2] = slice
        .try_into()
        .map_err(|_| ZipError::new("ZIP u16 slice mismatch"))?;
    Ok(u16::from_le_bytes(arr))
}

fn read_u32_le(bytes: &[u8], offset: usize) -> Result<u32, ZipError> {
    let slice = bytes
        .get(offset..offset + 4)
        .ok_or_else(|| ZipError::new("unexpected EOF reading ZIP u32"))?;
    let arr: [u8; 4] = slice
        .try_into()
        .map_err(|_| ZipError::new("ZIP u32 slice mismatch"))?;
    Ok(u32::from_le_bytes(arr))
}
