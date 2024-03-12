use Error;

/// `Result` type for CBOR serialisation and deserialisation.
pub type Result<'a, T> = core::result::Result<T, Error<'a>>;
