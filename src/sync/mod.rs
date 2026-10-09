//! Synchronization. [`internal`] holds the engine's std- or loom-backed
//! atomics, locks and gates, kept private.

pub(crate) mod internal;
