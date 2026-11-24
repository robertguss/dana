//! Zero-crate proleptic Gregorian calendar (`Date`), UTC `Timestamp`, `Duration`,
//! exact fixed-point `Decimal` parsing, `date_trunc`, and `months_between`.
//!
//! Civil/days conversions follow Howard Hinnant's algorithms, matching `Eval.lean`
//! and `src/oracle/eval.rs:date_trunc_month_days` identically.

use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, OnceLock};

use crate::core::bigint::{BigInt, DEC_MAX, DEC_MIN, DEC_SCALE};

pub const MICROS_PER_SECOND: i64 = 1_000_000;
pub const MICROS_PER_MINUTE: i64 = 60 * MICROS_PER_SECOND;
pub const MICROS_PER_HOUR: i64 = 60 * MICROS_PER_MINUTE;
pub const MICROS_PER_DAY: i64 = 24 * MICROS_PER_HOUR;

/// Typed error for temporal and fixed-point numeric parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseFormatError {
    pub message: String,
}

impl ParseFormatError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for ParseFormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ParseFormatError {}

#[must_use]
pub const fn is_leap_year(year: i64) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

#[must_use]
pub const fn days_in_month(year: i64, month: u32) -> u32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        _ => 0,
    }
}

/// Convert proleptic Gregorian `(year, month 1..=12, day 1..=31)` to days since `1970-01-01`.
#[must_use]
pub const fn days_from_civil(year: i64, month: u32, day: u32) -> i64 {
    let y = if month <= 2 { year - 1 } else { year };
    let era = y.div_euclid(400);
    let yoe = y - era * 400; // [0, 399]
    let m = month as i64;
    let d = day as i64;
    let doy = (153 * (m + if m > 2 { -3 } else { 9 }) + 2) / 5 + d - 1; // [0, 365]
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy; // [0, 146096]
    era * 146_097 + doe - 719_468
}

/// Convert days since `1970-01-01` to proleptic Gregorian `(year, month 1..=12, day 1..=31)`.
#[must_use]
pub const fn civil_from_days(days: i64) -> (i64, u32, u32) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097; // [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // [0, 365]
    let mp = (5 * doy + 2) / 153; // [0, 11]
    let d = doy - (153 * mp + 2) / 5 + 1; // [1, 31]
    let m = if mp < 10 { mp + 3 } else { mp - 9 }; // [1, 12]
    let year = if m <= 2 { y + 1 } else { y };
    (year, m as u32, d as u32)
}

/// Parse strict ISO-8601 date `YYYY-MM-DD` to days since `1970-01-01`.
///
/// # Errors
/// Returns [`ParseFormatError`] on malformed syntax or invalid calendar dates.
pub fn parse_iso_date(s: &str) -> Result<i64, ParseFormatError> {
    let b = s.as_bytes();
    if b.len() != 10 || b[4] != b'-' || b[7] != b'-' {
        return Err(ParseFormatError::new(format!(
            "invalid ISO date `{s}` (expected YYYY-MM-DD)"
        )));
    }
    let year: i64 = s[0..4]
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid year in date `{s}`")))?;
    let month: u32 = s[5..7]
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid month in date `{s}`")))?;
    let day: u32 = s[8..10]
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid day in date `{s}`")))?;
    if !(1..=12).contains(&month) {
        return Err(ParseFormatError::new(format!(
            "month out of range in date `{s}`"
        )));
    }
    let max_d = days_in_month(year, month);
    if day < 1 || day > max_d {
        return Err(ParseFormatError::new(format!(
            "day out of range in date `{s}`"
        )));
    }
    Ok(days_from_civil(year, month, day))
}

/// Format days since `1970-01-01` as `YYYY-MM-DD`.
#[must_use]
pub fn format_iso_date(days: i64) -> String {
    let (y, m, d) = civil_from_days(days);
    format!("{y:04}-{m:02}-{d:02}")
}

/// Parse strict ISO-8601 timestamp `YYYY-MM-DDTHH:MM:SS(.frac)?(Z|±HH:MM)` to UTC microseconds.
///
/// # Errors
/// Returns [`ParseFormatError`] on malformed syntax or out-of-range fields.
pub fn parse_iso_timestamp(s: &str) -> Result<i64, ParseFormatError> {
    if s.len() < 20 {
        return Err(ParseFormatError::new(format!(
            "invalid ISO timestamp `{s}`"
        )));
    }
    let b = s.as_bytes();
    if b[10] != b'T' && b[10] != b' ' {
        return Err(ParseFormatError::new(format!(
            "invalid ISO timestamp separator in `{s}`"
        )));
    }
    let days = parse_iso_date(&s[0..10])?;
    if b[13] != b':' || b[16] != b':' {
        return Err(ParseFormatError::new(format!(
            "invalid time syntax in timestamp `{s}`"
        )));
    }
    let hour: i64 = s[11..13]
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid hour in `{s}`")))?;
    let minute: i64 = s[14..16]
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid minute in `{s}`")))?;
    let second: i64 = s[17..19]
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid second in `{s}`")))?;
    if !(0..=23).contains(&hour) || !(0..=59).contains(&minute) || !(0..=59).contains(&second) {
        return Err(ParseFormatError::new(format!(
            "time component out of range in `{s}`"
        )));
    }

    let mut rest = &s[19..];
    let mut micros: i64 = 0;
    if let Some(after_dot) = rest.strip_prefix('.') {
        let digit_len = after_dot.bytes().take_while(u8::is_ascii_digit).count();
        if digit_len == 0 {
            return Err(ParseFormatError::new(format!(
                "missing fractional digits in `{s}`"
            )));
        }
        let frac_str = &after_dot[..digit_len];
        let mut scaled = 0i64;
        for (i, ch) in frac_str.bytes().take(6).enumerate() {
            let d = i64::from(ch - b'0');
            scaled = scaled * 10 + d;
            let _ = i;
        }
        for _ in frac_str.len()..6 {
            scaled *= 10;
        }
        micros = scaled;
        rest = &after_dot[digit_len..];
    }

    let tz_offset_secs: i64 = if rest == "Z" || rest == "z" {
        0
    } else if rest.len() == 6 && (rest.starts_with('+') || rest.starts_with('-')) {
        let sign: i64 = if rest.starts_with('-') { -1 } else { 1 };
        if rest.as_bytes()[3] != b':' {
            return Err(ParseFormatError::new(format!(
                "invalid timezone offset in `{s}`"
            )));
        }
        let oh: i64 = rest[1..3]
            .parse()
            .map_err(|_| ParseFormatError::new(format!("invalid tz hour in `{s}`")))?;
        let om: i64 = rest[4..6]
            .parse()
            .map_err(|_| ParseFormatError::new(format!("invalid tz minute in `{s}`")))?;
        if !(0..=23).contains(&oh) || !(0..=59).contains(&om) {
            return Err(ParseFormatError::new(format!(
                "tz offset out of range in `{s}`"
            )));
        }
        sign * (oh * 3600 + om * 60)
    } else {
        return Err(ParseFormatError::new(format!(
            "missing or invalid timezone suffix in `{s}` (expected Z or ±HH:MM)"
        )));
    };

    let day_us = days
        .checked_mul(MICROS_PER_DAY)
        .ok_or_else(|| ParseFormatError::new("timestamp overflow"))?;
    let tod_us = (hour * 3600 + minute * 60 + second) * MICROS_PER_SECOND + micros;
    day_us
        .checked_add(tod_us)
        .and_then(|t| t.checked_sub(tz_offset_secs * MICROS_PER_SECOND))
        .ok_or_else(|| ParseFormatError::new("timestamp overflow"))
}

/// Format UTC microseconds since epoch as ISO-8601 `YYYY-MM-DDTHH:MM:SS(.ffffff)?Z`.
#[must_use]
pub fn format_iso_timestamp(micros: i64) -> String {
    let days = micros.div_euclid(MICROS_PER_DAY);
    let rem = micros.rem_euclid(MICROS_PER_DAY);
    let secs = rem / MICROS_PER_SECOND;
    let frac = rem % MICROS_PER_SECOND;
    let hour = secs / 3600;
    let minute = (secs % 3600) / 60;
    let second = secs % 60;
    let (y, m, d) = civil_from_days(days);
    if frac == 0 {
        format!("{y:04}-{m:02}-{d:02}T{hour:02}:{minute:02}:{second:02}Z")
    } else {
        let frac_str = format!("{frac:06}");
        let trimmed = frac_str.trim_end_matches('0');
        format!("{y:04}-{m:02}-{d:02}T{hour:02}:{minute:02}:{second:02}.{trimmed}Z")
    }
}

/// Truncate a `Date` (days since 1970-01-01) to a calendar unit (`year`, `quarter`, `month`, `week`, `day`).
///
/// # Errors
/// Returns [`ParseFormatError`] for unsupported units.
pub fn date_trunc_date(days: i64, unit: &str) -> Result<i64, ParseFormatError> {
    let (y, m, _) = civil_from_days(days);
    match unit {
        "year" => Ok(days_from_civil(y, 1, 1)),
        "quarter" => {
            let qm = ((m - 1) / 3) * 3 + 1;
            Ok(days_from_civil(y, qm, 1))
        }
        "month" => Ok(days_from_civil(y, m, 1)),
        "week" => {
            // ISO Monday-based week: 1970-01-01 was Thursday (offset 3 from Monday).
            let dow = (days + 3).rem_euclid(7);
            Ok(days - dow)
        }
        "day" => Ok(days),
        _ => Err(ParseFormatError::new(format!(
            "unsupported date_trunc unit `:{unit}` for Date"
        ))),
    }
}

/// Truncate a `Timestamp` (UTC microseconds) to a calendar unit.
///
/// # Errors
/// Returns [`ParseFormatError`] for unsupported units.
pub fn date_trunc_timestamp_unit(micros: i64, unit: &str) -> Result<i64, ParseFormatError> {
    match unit {
        "year" | "quarter" | "month" | "week" | "day" => {
            let days = micros.div_euclid(MICROS_PER_DAY);
            let trunc_days = date_trunc_date(days, unit)?;
            Ok(trunc_days * MICROS_PER_DAY)
        }
        "hour" => Ok(micros.div_euclid(MICROS_PER_HOUR) * MICROS_PER_HOUR),
        "minute" => Ok(micros.div_euclid(MICROS_PER_MINUTE) * MICROS_PER_MINUTE),
        "second" => Ok(micros.div_euclid(MICROS_PER_SECOND) * MICROS_PER_SECOND),
        _ => Err(ParseFormatError::new(format!(
            "unsupported date_trunc unit `:{unit}` for Timestamp"
        ))),
    }
}

/// Truncate a `Timestamp` (UTC microseconds) to an arbitrary positive `Duration` bucket.
///
/// # Errors
/// Returns [`ParseFormatError`] if `step_micros <= 0`.
pub fn date_trunc_timestamp_duration(
    micros: i64,
    step_micros: i64,
) -> Result<i64, ParseFormatError> {
    if step_micros <= 0 {
        return Err(ParseFormatError::new(
            "date_trunc duration step must be positive",
        ));
    }
    Ok(micros.div_euclid(step_micros) * step_micros)
}

/// Signed whole calendar months between two dates: `(y2 - y1) * 12 + (m2 - m1)`.
#[must_use]
pub const fn months_between_days(d1: i64, d2: i64) -> i64 {
    let (y1, m1, _) = civil_from_days(d1);
    let (y2, m2, _) = civil_from_days(d2);
    (y2 - y1) * 12 + (m2 as i64 - m1 as i64)
}

/// Parse an exact fixed-point `Decimal` string (e.g., `"-12.50"`, `"900"`, `"0.0001"`)
/// into a `10^-18`-scaled [`BigInt`] checked against `[DEC_MIN, DEC_MAX]`.
///
/// # Errors
/// Returns [`ParseFormatError`] on syntax errors, >18 fractional digits, or range overflow.
pub fn parse_decimal_bigint(raw: &str) -> Result<BigInt, ParseFormatError> {
    let cleaned: String = raw.trim().chars().filter(|&c| c != '_').collect();
    if cleaned.is_empty() {
        return Err(ParseFormatError::new("empty decimal literal"));
    }
    let (neg, rest) = if let Some(r) = cleaned.strip_prefix('-') {
        (true, r)
    } else if let Some(r) = cleaned.strip_prefix('+') {
        (false, r)
    } else {
        (false, cleaned.as_str())
    };
    if rest.is_empty() {
        return Err(ParseFormatError::new(format!("invalid decimal `{raw}`")));
    }

    let (int_part, frac_part) = match rest.split_once('.') {
        Some((i, f)) => (i, f),
        None => (rest, ""),
    };
    if int_part.is_empty()
        || !int_part.bytes().all(|b| b.is_ascii_digit())
        || !frac_part.bytes().all(|b| b.is_ascii_digit())
    {
        return Err(ParseFormatError::new(format!("invalid decimal `{raw}`")));
    }
    if frac_part.len() > 18 {
        return Err(ParseFormatError::new(format!(
            "decimal `{raw}` exceeds 18 fractional digits"
        )));
    }

    let int_val: BigInt = int_part
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid integer part in `{raw}`")))?;
    let mut scaled = &int_val * &BigInt::from(DEC_SCALE);
    if !frac_part.is_empty() {
        let mut padded = frac_part.to_string();
        while padded.len() < 18 {
            padded.push('0');
        }
        let frac_val: BigInt = padded
            .parse()
            .map_err(|_| ParseFormatError::new(format!("invalid fractional part in `{raw}`")))?;
        scaled = &scaled + &frac_val;
    }
    if neg {
        scaled = -scaled;
    }
    if scaled < BigInt::from(DEC_MIN) || scaled > BigInt::from(DEC_MAX) {
        return Err(ParseFormatError::new(format!(
            "decimal `{raw}` out of fixed-point range"
        )));
    }
    Ok(scaled)
}

/// Round a `10^-18`-scaled [`BigInt`] decimal to `places` decimal digits (half away from zero).
#[must_use]
pub fn round_decimal_bigint(val: &BigInt, places: i64) -> BigInt {
    let p = places.clamp(0, 18) as u32;
    if p == 18 {
        return val.clone();
    }
    let exp = 18 - p;
    let factor_i128 = 10i128.pow(exp);
    let factor = BigInt::from(factor_i128);
    let half = BigInt::from(factor_i128 / 2);
    if val.is_negative() {
        let abs = val.abs();
        let rounded = (&abs + &half)
            .div_euclid(&factor)
            .map_or(BigInt::ZERO, |q| &q * &factor);
        -rounded
    } else {
        (val + &half)
            .div_euclid(&factor)
            .map_or(BigInt::ZERO, |q| &q * &factor)
    }
}

// ---------------------------------------------------------------------------
// RFC 8536 TZif v1/v2/v3 Parser, POSIX TZ Footer Evaluator & `in_tz`
// ---------------------------------------------------------------------------

/// A single local time type record (`ttinfo`) from a TZif file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalTimeType {
    /// Offset in seconds east of UTC (e.g., `-18000` for EST, `+3600` for CET).
    pub ut_offset_secs: i32,
    pub is_dst: bool,
}

/// Parsed POSIX TZ transition date rule (`Mm.w.d`, `Jn`, or `n`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PosixDateRule {
    /// `Mm.w.d`: month `1..=12`, week `1..=5` (`5` = last `weekday` of month), weekday `0=Sun..=6=Sat`.
    MonthWeekDay { month: u32, week: u32, weekday: u32 },
    /// `Jn`: 1-based Julian day `1..=365`, never counting Feb 29.
    JulianNoLeap(u32),
    /// `n`: 0-based Julian day `0..=365`, counting Feb 29 in leap years.
    JulianZeroBased(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PosixTransition {
    date: PosixDateRule,
    /// Transition time in seconds from local midnight (RFC 8536 v3 allows `-167..=167` hours).
    time_secs: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PosixTzRule {
    std_offset_secs: i32,
    dst: Option<(i32, PosixTransition, PosixTransition)>,
}

/// Parsed RFC 8536 TZif timezone database entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TzData {
    transitions: Vec<i64>,
    type_indices: Vec<u8>,
    types: Vec<LocalTimeType>,
    footer: Option<PosixTzRule>,
}

impl TzData {
    /// Parse a binary RFC 8536 TZif v1/v2/v3 file.
    ///
    /// # Errors
    /// Returns [`ParseFormatError`] if the header magic is invalid or the payload is truncated.
    pub fn parse(bytes: &[u8]) -> Result<Self, ParseFormatError> {
        if bytes.len() < 44 || &bytes[0..4] != b"TZif" {
            return Err(ParseFormatError::new("invalid TZif header magic"));
        }
        let version = bytes[4];
        let hdr1 = read_tzif_header(&bytes[0..44])?;
        let body1_len = tzif_body_len(&hdr1, false)?;
        let v2_start = 44usize
            .checked_add(body1_len)
            .ok_or_else(|| ParseFormatError::new("TZif v1 body size overflow"))?;

        if version == 0 {
            if bytes.len() < v2_start {
                return Err(ParseFormatError::new("truncated TZif v1 body"));
            }
            return parse_tzif_body(&bytes[44..v2_start], &hdr1, false, None);
        }

        if bytes.len() < v2_start + 44 || &bytes[v2_start..v2_start + 4] != b"TZif" {
            return Err(ParseFormatError::new(
                "missing or invalid TZif v2/v3 header",
            ));
        }
        let hdr2 = read_tzif_header(&bytes[v2_start..v2_start + 44])?;
        let body2_len = tzif_body_len(&hdr2, true)?;
        let body2_start = v2_start + 44;
        let body2_end = body2_start
            .checked_add(body2_len)
            .ok_or_else(|| ParseFormatError::new("TZif v2 body size overflow"))?;
        if bytes.len() < body2_end {
            return Err(ParseFormatError::new("truncated TZif v2/v3 body"));
        }

        let footer_bytes = &bytes[body2_end..];
        let footer = if footer_bytes.len() >= 2
            && footer_bytes[0] == b'\n'
            && footer_bytes[footer_bytes.len() - 1] == b'\n'
        {
            let inner = std::str::from_utf8(&footer_bytes[1..footer_bytes.len() - 1])
                .map_err(|_| ParseFormatError::new("non-UTF-8 TZif POSIX footer"))?
                .trim();
            if inner.is_empty() {
                None
            } else {
                Some(parse_posix_tz(inner)?)
            }
        } else {
            None
        };

        parse_tzif_body(&bytes[body2_start..body2_end], &hdr2, true, footer)
    }

    /// Compute the UTC offset in seconds (east of UTC) active at `utc_secs` (seconds since Unix epoch).
    #[must_use]
    pub fn offset_secs_at_unix_secs(&self, utc_secs: i64) -> i32 {
        if self.transitions.is_empty() {
            if let Some(footer) = &self.footer {
                return eval_posix_tz(footer, utc_secs);
            }
            return self.types.first().map_or(0, |t| t.ut_offset_secs);
        }

        // If `utc_secs` is at or after the last explicit transition, prefer the POSIX TZ footer rule
        // (essential for post-2038 dates!).
        if let Some(&last_t) = self.transitions.last()
            && utc_secs >= last_t
        {
            if let Some(footer) = &self.footer {
                return eval_posix_tz(footer, utc_secs);
            }
            let idx = usize::from(*self.type_indices.last().unwrap_or(&0));
            return self.types.get(idx).map_or(0, |t| t.ut_offset_secs);
        }

        match self.transitions.binary_search(&utc_secs) {
            Ok(pos) => {
                let idx = usize::from(self.type_indices.get(pos).copied().unwrap_or(0));
                self.types.get(idx).map_or(0, |t| t.ut_offset_secs)
            }
            Err(0) => {
                // Before the first transition: RFC 8536 uses the first standard-time type (or type 0).
                self.types
                    .iter()
                    .find(|t| !t.is_dst)
                    .or_else(|| self.types.first())
                    .map_or(0, |t| t.ut_offset_secs)
            }
            Err(pos) => {
                let idx = usize::from(self.type_indices.get(pos - 1).copied().unwrap_or(0));
                self.types.get(idx).map_or(0, |t| t.ut_offset_secs)
            }
        }
    }

    /// Compute the UTC offset in seconds active at `utc_micros` (microseconds since Unix epoch).
    #[must_use]
    pub fn offset_secs_at(&self, utc_micros: i64) -> i32 {
        self.offset_secs_at_unix_secs(utc_micros.div_euclid(MICROS_PER_SECOND))
    }
}

struct TzifHeader {
    isutcnt: usize,
    isstdcnt: usize,
    leapcnt: usize,
    timecnt: usize,
    typecnt: usize,
    charcnt: usize,
}

fn read_be_u32(slice: &[u8]) -> Result<u32, ParseFormatError> {
    let arr: [u8; 4] = slice
        .try_into()
        .map_err(|_| ParseFormatError::new("unexpected EOF in TZif u32"))?;
    Ok(u32::from_be_bytes(arr))
}

fn read_be_i32(slice: &[u8]) -> Result<i32, ParseFormatError> {
    let arr: [u8; 4] = slice
        .try_into()
        .map_err(|_| ParseFormatError::new("unexpected EOF in TZif i32"))?;
    Ok(i32::from_be_bytes(arr))
}

fn read_be_i64(slice: &[u8]) -> Result<i64, ParseFormatError> {
    let arr: [u8; 8] = slice
        .try_into()
        .map_err(|_| ParseFormatError::new("unexpected EOF in TZif i64"))?;
    Ok(i64::from_be_bytes(arr))
}

fn read_tzif_header(hdr: &[u8]) -> Result<TzifHeader, ParseFormatError> {
    let isutcnt = read_be_u32(&hdr[20..24])? as usize;
    let isstdcnt = read_be_u32(&hdr[24..28])? as usize;
    let leapcnt = read_be_u32(&hdr[28..32])? as usize;
    let timecnt = read_be_u32(&hdr[32..36])? as usize;
    let typecnt = read_be_u32(&hdr[36..40])? as usize;
    let charcnt = read_be_u32(&hdr[40..44])? as usize;
    if typecnt == 0 {
        return Err(ParseFormatError::new("TZif typecnt cannot be 0"));
    }
    Ok(TzifHeader {
        isutcnt,
        isstdcnt,
        leapcnt,
        timecnt,
        typecnt,
        charcnt,
    })
}

fn tzif_body_len(h: &TzifHeader, is_64: bool) -> Result<usize, ParseFormatError> {
    let time_sz: usize = if is_64 { 8 } else { 4 };
    let leap_sz: usize = if is_64 { 12 } else { 8 };
    let mut total = 0usize;
    let add = |acc: &mut usize, n: usize| -> Result<(), ParseFormatError> {
        *acc = acc
            .checked_add(n)
            .ok_or_else(|| ParseFormatError::new("TZif size overflow"))?;
        Ok(())
    };
    add(
        &mut total,
        h.timecnt
            .checked_mul(time_sz)
            .ok_or_else(|| ParseFormatError::new("TZif timecnt overflow"))?,
    )?;
    add(&mut total, h.timecnt)?;
    add(
        &mut total,
        h.typecnt
            .checked_mul(6)
            .ok_or_else(|| ParseFormatError::new("TZif typecnt overflow"))?,
    )?;
    add(&mut total, h.charcnt)?;
    add(
        &mut total,
        h.leapcnt
            .checked_mul(leap_sz)
            .ok_or_else(|| ParseFormatError::new("TZif leapcnt overflow"))?,
    )?;
    add(&mut total, h.isstdcnt)?;
    add(&mut total, h.isutcnt)?;
    Ok(total)
}

fn parse_tzif_body(
    body: &[u8],
    hdr: &TzifHeader,
    is_64: bool,
    footer: Option<PosixTzRule>,
) -> Result<TzData, ParseFormatError> {
    let mut pos = 0usize;
    let mut transitions = Vec::with_capacity(hdr.timecnt);
    if is_64 {
        for _ in 0..hdr.timecnt {
            transitions.push(read_be_i64(&body[pos..pos + 8])?);
            pos += 8;
        }
    } else {
        for _ in 0..hdr.timecnt {
            transitions.push(i64::from(read_be_i32(&body[pos..pos + 4])?));
            pos += 4;
        }
    }

    let type_indices = body[pos..pos + hdr.timecnt].to_vec();
    pos += hdr.timecnt;

    let mut types = Vec::with_capacity(hdr.typecnt);
    for _ in 0..hdr.typecnt {
        let ut_offset_secs = read_be_i32(&body[pos..pos + 4])?;
        let is_dst = body[pos + 4] != 0;
        pos += 6; // skip desigidx
        types.push(LocalTimeType {
            ut_offset_secs,
            is_dst,
        });
    }

    for &idx in &type_indices {
        if usize::from(idx) >= types.len() {
            return Err(ParseFormatError::new("TZif type index out of bounds"));
        }
    }

    Ok(TzData {
        transitions,
        type_indices,
        types,
        footer,
    })
}

fn parse_posix_tz(s: &str) -> Result<PosixTzRule, ParseFormatError> {
    let mut rest = skip_posix_tz_name(s)?;
    let (std_posix_offset, after_std) = parse_posix_offset(rest)?;
    // POSIX TZ offset sign is inverted relative to ISO-8601 (`EST5` => UTC-5 => `-18000`s).
    let std_offset_secs = -std_posix_offset;
    rest = after_std;
    if rest.is_empty() {
        return Ok(PosixTzRule {
            std_offset_secs,
            dst: None,
        });
    }

    rest = skip_posix_tz_name(rest)?;
    let (dst_offset_secs, after_dst) = if rest.starts_with(',') || rest.is_empty() {
        (std_offset_secs + 3600, rest)
    } else {
        let (dst_posix, tail) = parse_posix_offset(rest)?;
        (-dst_posix, tail)
    };
    rest = after_dst;
    let Some(after_comma) = rest.strip_prefix(',') else {
        return Ok(PosixTzRule {
            std_offset_secs,
            dst: None,
        });
    };
    let Some((start_str, end_str)) = after_comma.split_once(',') else {
        return Err(ParseFormatError::new(format!(
            "invalid POSIX TZ transition pair `{s}`"
        )));
    };
    let start = parse_posix_transition(start_str)?;
    let end = parse_posix_transition(end_str)?;
    Ok(PosixTzRule {
        std_offset_secs,
        dst: Some((dst_offset_secs, start, end)),
    })
}

fn skip_posix_tz_name(s: &str) -> Result<&str, ParseFormatError> {
    if let Some(after_lt) = s.strip_prefix('<') {
        let Some(end) = after_lt.find('>') else {
            return Err(ParseFormatError::new(format!(
                "unterminated quoted TZ name in `{s}`"
            )));
        };
        Ok(&after_lt[end + 1..])
    } else {
        let n = s
            .bytes()
            .take_while(|&b| !b.is_ascii_digit() && b != b'+' && b != b'-' && b != b',')
            .count();
        if n == 0 {
            return Err(ParseFormatError::new(format!("missing TZ name in `{s}`")));
        }
        Ok(&s[n..])
    }
}

fn parse_posix_offset(s: &str) -> Result<(i32, &str), ParseFormatError> {
    let (secs, rest) = parse_posix_hms(s)?;
    let secs_i32 =
        i32::try_from(secs).map_err(|_| ParseFormatError::new("POSIX TZ offset overflow"))?;
    Ok((secs_i32, rest))
}

fn parse_posix_hms(s: &str) -> Result<(i64, &str), ParseFormatError> {
    let (neg, mut rest) = if let Some(r) = s.strip_prefix('-') {
        (true, r)
    } else if let Some(r) = s.strip_prefix('+') {
        (false, r)
    } else {
        (false, s)
    };
    let (hours, r1) = take_u32_digits(rest)?;
    rest = r1;
    let mut mins = 0u32;
    let mut secs = 0u32;
    if let Some(after_c1) = rest.strip_prefix(':') {
        let (m, r2) = take_u32_digits(after_c1)?;
        mins = m;
        rest = r2;
        if let Some(after_c2) = rest.strip_prefix(':') {
            let (sc, r3) = take_u32_digits(after_c2)?;
            secs = sc;
            rest = r3;
        }
    }
    let total = i64::from(hours) * 3600 + i64::from(mins) * 60 + i64::from(secs);
    Ok((if neg { -total } else { total }, rest))
}

fn take_u32_digits(s: &str) -> Result<(u32, &str), ParseFormatError> {
    let n = s.bytes().take_while(u8::is_ascii_digit).count();
    if n == 0 {
        return Err(ParseFormatError::new(format!(
            "expected digits in POSIX TZ `{s}`"
        )));
    }
    let val: u32 = s[..n]
        .parse()
        .map_err(|_| ParseFormatError::new(format!("invalid integer in POSIX TZ `{s}`")))?;
    Ok((val, &s[n..]))
}

fn parse_posix_transition(s: &str) -> Result<PosixTransition, ParseFormatError> {
    let (date_str, time_secs) = match s.split_once('/') {
        Some((d, t)) => {
            let (secs, tail) = parse_posix_hms(t)?;
            if !tail.is_empty() {
                return Err(ParseFormatError::new(format!(
                    "trailing characters in POSIX TZ time `{s}`"
                )));
            }
            (d, secs)
        }
        None => (s, 7200), // Default 02:00:00 local time
    };

    let date = if let Some(m_rest) = date_str.strip_prefix('M') {
        let parts: Vec<&str> = m_rest.split('.').collect();
        if parts.len() != 3 {
            return Err(ParseFormatError::new(format!(
                "invalid POSIX Mm.w.d rule `{date_str}`"
            )));
        }
        let month: u32 = parts[0]
            .parse()
            .map_err(|_| ParseFormatError::new("invalid month in POSIX TZ"))?;
        let week: u32 = parts[1]
            .parse()
            .map_err(|_| ParseFormatError::new("invalid week in POSIX TZ"))?;
        let weekday: u32 = parts[2]
            .parse()
            .map_err(|_| ParseFormatError::new("invalid weekday in POSIX TZ"))?;
        if !(1..=12).contains(&month) || !(1..=5).contains(&week) || weekday > 6 {
            return Err(ParseFormatError::new(format!(
                "out-of-range POSIX Mm.w.d rule `{date_str}`"
            )));
        }
        PosixDateRule::MonthWeekDay {
            month,
            week,
            weekday,
        }
    } else if let Some(j_rest) = date_str.strip_prefix('J') {
        let n: u32 = j_rest
            .parse()
            .map_err(|_| ParseFormatError::new("invalid Julian Jn rule"))?;
        if !(1..=365).contains(&n) {
            return Err(ParseFormatError::new("out-of-range Julian Jn rule"));
        }
        PosixDateRule::JulianNoLeap(n)
    } else {
        let n: u32 = date_str
            .parse()
            .map_err(|_| ParseFormatError::new("invalid zero-based Julian rule"))?;
        if n > 365 {
            return Err(ParseFormatError::new("out-of-range zero-based Julian rule"));
        }
        PosixDateRule::JulianZeroBased(n)
    };

    Ok(PosixTransition { date, time_secs })
}

fn posix_rule_day_of_year(year: i64, rule: PosixDateRule) -> i64 {
    let jan1 = days_from_civil(year, 1, 1);
    match rule {
        PosixDateRule::JulianZeroBased(n) => jan1 + i64::from(n),
        PosixDateRule::JulianNoLeap(n) => {
            let mut offset = i64::from(n) - 1;
            if is_leap_year(year) && n >= 60 {
                offset += 1;
            }
            jan1 + offset
        }
        PosixDateRule::MonthWeekDay {
            month,
            week,
            weekday,
        } => {
            let first_day = days_from_civil(year, month, 1);
            // 1970-01-01 was Thursday (weekday 4 where 0 = Sunday).
            let first_wd = (first_day + 4).rem_euclid(7) as u32;
            let delta = (weekday + 7 - first_wd) % 7;
            let mut day = 1 + delta + (week - 1) * 7;
            let dim = days_in_month(year, month);
            while day > dim {
                day -= 7;
            }
            days_from_civil(year, month, day)
        }
    }
}

fn eval_posix_tz(rule: &PosixTzRule, utc_secs: i64) -> i32 {
    let Some((dst_offset_secs, start, end)) = rule.dst else {
        return rule.std_offset_secs;
    };
    let approx_days = (utc_secs + i64::from(rule.std_offset_secs)).div_euclid(86_400);
    let (year, _, _) = civil_from_days(approx_days);

    // Start transition occurs in standard time; end transition occurs in DST time.
    let start_utc = posix_rule_day_of_year(year, start.date) * 86_400 + start.time_secs
        - i64::from(rule.std_offset_secs);
    let end_utc = posix_rule_day_of_year(year, end.date) * 86_400 + end.time_secs
        - i64::from(dst_offset_secs);

    let in_dst = if start_utc < end_utc {
        // Northern Hemisphere (e.g., March -> November).
        utc_secs >= start_utc && utc_secs < end_utc
    } else {
        // Southern Hemisphere (e.g., October -> April).
        utc_secs >= start_utc || utc_secs < end_utc
    };
    if in_dst {
        dst_offset_secs
    } else {
        rule.std_offset_secs
    }
}

fn tz_cache() -> &'static Mutex<HashMap<String, Arc<TzData>>> {
    static CACHE: OnceLock<Mutex<HashMap<String, Arc<TzData>>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn is_valid_iana_zone_name(iana: &str) -> bool {
    if iana.is_empty()
        || iana.starts_with('/')
        || iana.ends_with('/')
        || iana.contains('\0')
        || iana.contains('\\')
    {
        return false;
    }
    if iana
        .split('/')
        .any(|seg| seg.is_empty() || seg == "." || seg == "..")
    {
        return false;
    }
    iana.bytes()
        .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'/' | b'_' | b'-' | b'+' | b'.'))
}

/// Load and cache an IANA timezone from `TZDIR` or `/usr/share/zoneinfo/` (plus built-in `"UTC"`).
///
/// # Errors
/// Returns [`ParseFormatError`] if `iana` is invalid, escapes zoneinfo, does not exist, or fails TZif parsing.
pub fn load_timezone(iana: &str) -> Result<Arc<TzData>, ParseFormatError> {
    if iana == "UTC" || iana == "Etc/UTC" || iana == "Z" {
        return Ok(Arc::new(TzData {
            transitions: Vec::new(),
            type_indices: Vec::new(),
            types: vec![LocalTimeType {
                ut_offset_secs: 0,
                is_dst: false,
            }],
            footer: None,
        }));
    }
    if !is_valid_iana_zone_name(iana) {
        return Err(ParseFormatError::new(format!(
            "invalid IANA timezone name `{iana}`"
        )));
    }
    if let Ok(guard) = tz_cache().lock()
        && let Some(cached) = guard.get(iana)
    {
        return Ok(Arc::clone(cached));
    }

    let base = std::env::var_os("TZDIR")
        .filter(|v| !v.is_empty())
        .map_or_else(|| PathBuf::from("/usr/share/zoneinfo"), PathBuf::from);
    let path = base.join(iana);
    let bytes = fs::read(&path).map_err(|_| {
        ParseFormatError::new(format!(
            "unknown IANA timezone `{iana}` (not found under `{}`)",
            base.display()
        ))
    })?;
    let parsed = Arc::new(TzData::parse(&bytes)?);
    if let Ok(mut guard) = tz_cache().lock() {
        guard.insert(iana.to_string(), Arc::clone(&parsed));
    }
    Ok(parsed)
}

/// Format a UTC `Timestamp` (microseconds since epoch) as ISO-8601 in an explicit IANA timezone
/// (e.g., `"2026-07-04T08:30:00-04:00"` for `"America/New_York"`, or `"...Z"` for `"UTC"`).
///
/// # Errors
/// Returns [`ParseFormatError`] if `iana` is unknown or overflows timestamp bounds.
pub fn format_timestamp_in_tz(utc_micros: i64, iana: &str) -> Result<String, ParseFormatError> {
    if iana == "UTC" || iana == "Etc/UTC" || iana == "Z" {
        return Ok(format_iso_timestamp(utc_micros));
    }
    let tz = load_timezone(iana)?;
    let offset_secs = i64::from(tz.offset_secs_at(utc_micros));
    let local_micros = utc_micros
        .checked_add(offset_secs * MICROS_PER_SECOND)
        .ok_or_else(|| ParseFormatError::new("timestamp overflow in timezone conversion"))?;

    let days = local_micros.div_euclid(MICROS_PER_DAY);
    let rem = local_micros.rem_euclid(MICROS_PER_DAY);
    let secs = rem / MICROS_PER_SECOND;
    let frac = rem % MICROS_PER_SECOND;
    let hour = secs / 3600;
    let minute = (secs % 3600) / 60;
    let second = secs % 60;
    let (y, m, d) = civil_from_days(days);

    let sign = if offset_secs < 0 { '-' } else { '+' };
    let abs_off = offset_secs.abs();
    let off_h = abs_off / 3600;
    let off_m = (abs_off % 3600) / 60;

    if frac == 0 {
        Ok(format!(
            "{y:04}-{m:02}-{d:02}T{hour:02}:{minute:02}:{second:02}{sign}{off_h:02}:{off_m:02}"
        ))
    } else {
        let frac_str = format!("{frac:06}");
        let trimmed = frac_str.trim_end_matches('0');
        Ok(format!(
            "{y:04}-{m:02}-{d:02}T{hour:02}:{minute:02}:{second:02}.{trimmed}{sign}{off_h:02}:{off_m:02}"
        ))
    }
}

/// Convert a UTC `Timestamp` (microseconds since epoch) to the local calendar `Date` (days since 1970-01-01)
/// in an explicit IANA timezone.
///
/// # Errors
/// Returns [`ParseFormatError`] if `iana` is unknown or overflows timestamp bounds.
pub fn local_date_in_tz(utc_micros: i64, iana: &str) -> Result<i64, ParseFormatError> {
    let tz = load_timezone(iana)?;
    let offset_secs = i64::from(tz.offset_secs_at(utc_micros));
    let local_micros = utc_micros
        .checked_add(offset_secs * MICROS_PER_SECOND)
        .ok_or_else(|| ParseFormatError::new("timestamp overflow in timezone conversion"))?;
    Ok(local_micros.div_euclid(MICROS_PER_DAY))
}
