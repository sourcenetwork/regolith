//! Read access to the options a caller outside the crate has a reason to inspect.
//!
//! Prefixed `get_` because the builder method of the same option already owns
//! the bare name. Only the options an outside caller reads are here; a new one
//! is a new method.

use super::*;

macro_rules! copy_getters {
    ($($get:ident => $field:ident: $ty:ty),* $(,)?) => {
        impl Options {
            $(
                #[doc = concat!("The value of [`Options::", stringify!($field), "`].")]
                #[must_use]
                pub fn $get(&self) -> $ty {
                    self.$field
                }
            )*
        }
    };
}

copy_getters! {
    get_write_buffer_size => write_buffer_size: usize,
    get_arena_profile => arena_profile: ArenaProfile,
    get_block_size => block_size: usize,
    get_block_cache_size => block_cache_size: usize,
    get_block_cache_num_shard_bits => block_cache_num_shard_bits: u32,
    get_compression => compression: CompressionType,
    get_target_file_size => target_file_size: u64,
    get_durability => durability: DurabilityMode,
    get_max_write_buffer_number => max_write_buffer_number: usize,
    get_max_background_compactions => max_background_compactions: usize,
    get_max_value_size => max_value_size: usize,
}

impl Options {
    /// The value of [`Options::merge_operator`].
    #[must_use]
    pub fn get_merge_operator(&self) -> Option<&Arc<dyn MergeOperator>> {
        self.merge_operator.as_ref()
    }

    /// The value of [`Options::env`].
    #[must_use]
    pub fn get_env(&self) -> &Arc<dyn crate::env::Env> {
        &self.env
    }
}
