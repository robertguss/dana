//! Stack-management helper ensuring deeply nested Core IR programs never overflow
//! small caller stacks (e.g., 2 MiB `cargo test` threads or default 8 MiB main threads)
//! without requiring external crates or `unsafe` code.

use std::cell::Cell;
use std::panic;
use std::sync::Mutex;
use std::thread;

/// Virtual stack size (128 MiB) reserved on dedicated worker threads.
/// On Linux this is demand-paged, so shallow programs touch only a few KiB.
const LARGE_STACK_BYTES: usize = 128 * 1024 * 1024;

thread_local! {
    static ON_LARGE_STACK: Cell<bool> = const { Cell::new(false) };
}

/// Run `f` on a thread with a large stack (`128 MiB`).
///
/// If the current thread is already running inside `with_large_stack`, executes `f`
/// directly with zero thread-spawning overhead.
pub fn with_large_stack<R: Send, F: FnOnce() -> R + Send>(f: F) -> R {
    if ON_LARGE_STACK.with(Cell::get) {
        return f();
    }
    let mut result: Option<R> = None;
    let slot: Mutex<Option<F>> = Mutex::new(Some(f));
    thread::scope(|scope| {
        let builder = thread::Builder::new()
            .name("dana-stack".to_string())
            .stack_size(LARGE_STACK_BYTES);
        if let Ok(handle) = builder.spawn_scoped(scope, || {
            ON_LARGE_STACK.with(|flag| flag.set(true));
            let maybe_cb = slot.lock().ok().and_then(|mut guard| guard.take());
            maybe_cb.map(|cb| cb())
        }) {
            match handle.join() {
                Ok(res) => result = res,
                Err(payload) => panic::resume_unwind(payload),
            }
        }
    });
    if let Some(res) = result {
        return res;
    }
    if let Ok(Some(cb)) = slot.into_inner() {
        return cb();
    }
    unreachable!("dana-stack worker either produced a result or left the closure uninvoked")
}
