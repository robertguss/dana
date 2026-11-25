//! Built-in native data formats, transparent compression, crypto, calendar/TZif temporal math,
//! streaming CSV/TSV & JSON/JSONL quarantine codecs, PKZIP, OOXML Excel (`.xlsx`), Apache Parquet,
//! schema inference, and synthetic data generation.

pub mod compress;
pub mod constraint;
pub mod crypto;
pub mod csv;
pub mod fake;
pub mod infer;
pub mod json;
pub mod parquet;
pub mod time;
pub mod xlsx;
pub mod zip;
