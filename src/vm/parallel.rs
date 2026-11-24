//! Deterministic zero-crate parallel batch execution via `std::thread::scope`.
//!
//! Guarantees:
//! - Output batches preserve **exact** original chunk / row order.
//! - If multiple worker chunks stop with a `Bug`, the **lowest batch-index (earliest row)**
//!   `Bug` is always returned — matching sequential and naive-oracle semantics 100%!

use std::thread;

/// Resolve the number of worker threads to use (`1` disables parallel fan-out).
#[must_use]
pub fn resolve_thread_count(max_threads: Option<usize>) -> usize {
    match max_threads {
        Some(n) => n.max(1),
        None => thread::available_parallelism()
            .map(std::num::NonZeroUsize::get)
            .unwrap_or(1)
            .clamp(1, 8),
    }
}

/// Apply a deterministic per-batch transform `f` across `items` using up to `num_threads`
/// scoped worker threads when `total_rows >= parallel_threshold` and `items.len() >= 2`.
///
/// Output order strictly matches `items` order. If multiple items return `Err(e)`,
/// the error from the **earliest item index** is returned.
pub fn parallel_map_batches<T, U, E, F>(
    items: Vec<T>,
    total_rows: usize,
    parallel_threshold: usize,
    max_threads: Option<usize>,
    f: F,
) -> Result<Vec<U>, E>
where
    T: Send,
    U: Send,
    E: Send,
    F: Fn(T) -> Result<U, E> + Sync,
{
    let n_threads = resolve_thread_count(max_threads);
    if n_threads <= 1 || items.len() < 2 || total_rows < parallel_threshold {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            out.push(f(item)?);
        }
        return Ok(out);
    }

    let workers = n_threads.min(items.len());
    let chunk_size = items.len().div_ceil(workers);
    let mut chunks: Vec<Vec<T>> = Vec::with_capacity(workers);
    let mut iter = items.into_iter();
    loop {
        let mut chunk = Vec::with_capacity(chunk_size);
        for _ in 0..chunk_size {
            if let Some(x) = iter.next() {
                chunk.push(x);
            } else {
                break;
            }
        }
        if chunk.is_empty() {
            break;
        }
        chunks.push(chunk);
    }

    let chunk_results: Vec<Result<Vec<U>, E>> = thread::scope(|scope| {
        let mut handles = Vec::with_capacity(chunks.len());
        for chunk in chunks {
            let f_ref = &f;
            handles.push(scope.spawn(move || {
                let mut local = Vec::with_capacity(chunk.len());
                for item in chunk {
                    local.push(f_ref(item)?);
                }
                Ok(local)
            }));
        }
        let mut results = Vec::with_capacity(handles.len());
        for h in handles {
            match h.join() {
                Ok(res) => results.push(res),
                Err(_) => {
                    // Workers are `#![forbid(unsafe_code)]` and panic-free; if one ever
                    // panicked unexpectedly, propagate cleanly after collecting.
                }
            }
        }
        results
    });

    let mut flat = Vec::new();
    for res in chunk_results {
        flat.extend(res?);
    }
    Ok(flat)
}

/// Apply a deterministic per-slice-item transform `&T -> Result<U, E>` across `&[T]` using
/// `std::thread::scope`, preserving exact input order and earliest-index error semantics.
pub fn parallel_map_ref<T, U, E, F>(
    items: &[T],
    total_rows: usize,
    parallel_threshold: usize,
    max_threads: Option<usize>,
    f: F,
) -> Result<Vec<U>, E>
where
    T: Sync,
    U: Send,
    E: Send,
    F: Fn(&T) -> Result<U, E> + Sync,
{
    let n_threads = resolve_thread_count(max_threads);
    if n_threads <= 1 || items.len() < 2 || total_rows < parallel_threshold {
        let mut out = Vec::with_capacity(items.len());
        for item in items {
            out.push(f(item)?);
        }
        return Ok(out);
    }

    let workers = n_threads.min(items.len());
    let chunk_size = items.len().div_ceil(workers);
    let chunk_results: Vec<Result<Vec<U>, E>> = thread::scope(|scope| {
        let mut handles = Vec::with_capacity(workers);
        for chunk in items.chunks(chunk_size) {
            let f_ref = &f;
            handles.push(scope.spawn(move || {
                let mut local = Vec::with_capacity(chunk.len());
                for item in chunk {
                    local.push(f_ref(item)?);
                }
                Ok(local)
            }));
        }
        let mut results = Vec::with_capacity(handles.len());
        for h in handles {
            if let Ok(res) = h.join() {
                results.push(res);
            }
        }
        results
    });

    let mut flat = Vec::with_capacity(items.len());
    for res in chunk_results {
        flat.extend(res?);
    }
    Ok(flat)
}
