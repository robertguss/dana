//! Zero-crate proleptic Gregorian calendar (`Date`), UTC `Timestamp`, `Duration`,
//! exact fixed-point `Decimal` parsing, `date_trunc`, and `months_between`.
//!
//! Civil/days conversions follow Howard Hinnant's algorithms, matching `Eval.lean`
//! and `src/oracle/eval.rs:date_trunc_month_days` identically.

use std::fmt;

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
