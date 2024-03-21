//! CBOR Value object representation
//!
//! While it is handy to be able to construct into the intermediate value
//! type it is also not recommended to use it as an intermediate type
//! before deserialising concrete type:
//!
//! - it is slow and bloated;
//! - it takes a lot dynamic memory and may not be compatible with the targeted environment;
//!
//! This is why all the objects here are marked as deprecated

#[cfg(feature = "alloc")]
use alloc::collections::BTreeMap;
#[cfg(test)]
use core::iter::repeat_with;

#[cfg(test)]
use quickcheck::{Arbitrary, Gen};

use de::*;
use error::Error;
use len::Len;
use result::Result;
use se::*;
use types::{Special, Type};

/// CBOR Object key, represents the possible supported values for
/// a CBOR key in a CBOR Map.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ObjectKey<'a> {
    Integer(u64),
    Bytes(&'a [u8]),
    Text(&'a str),
}
impl<'a> ObjectKey<'a> {
    /// convert the given `ObjectKey` into a CBOR [`Value`](./struct.Value.html)
    pub fn value(self) -> Value<'a> {
        match self {
            ObjectKey::Integer(v) => Value::U64(v),
            ObjectKey::Bytes(v) => Value::Bytes(v),
            ObjectKey::Text(v) => Value::Text(v),
        }
    }
}
impl<'a> Serialize for ObjectKey<'a> {
    fn serialize<'se>(
        &self,
        serializer: &'se mut Serializer<'se>,
    ) -> Result<'se, &'se mut Serializer<'se>> {
        match self {
            ObjectKey::Integer(ref v) => serializer.write_unsigned_integer(*v),
            ObjectKey::Bytes(ref v) => serializer.write_bytes(v),
            ObjectKey::Text(ref v) => serializer.write_text(v),
        }
    }
}
impl<'a> Deserialize<'a> for ObjectKey<'a> {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<'a, Self> {
        match raw.cbor_type()? {
            Type::UnsignedInteger => Ok(ObjectKey::Integer(raw.unsigned_integer()?)),
            Type::Bytes => Ok(ObjectKey::Bytes(raw.bytes()?)),
            Type::Text => Ok(ObjectKey::Text(raw.text()?)),
            t => Err(Error::CustomError(
                format_args!("Type `{:?}' is not a support type for CBOR Map's key", t)
                    .as_str()
                    .unwrap(),
            )),
        }
    }
}

/// All possible CBOR supported values.
///
/// We advise not to use these objects as an intermediary representation before
/// retrieving custom types as it is a slow and not memory efficient way to do
/// so. However it is handy for debugging or reverse a given protocol.
///
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum Value<'a> {
    U64(u64),
    I64(i64),
    Bytes(&'a [u8]),
    Text(&'a str),
    Array(&'a [Value<'a>]),
    IArray(&'a [Value<'a>]),
    #[cfg(feature = "alloc")]
    Object(BTreeMap<ObjectKey<'a>, Value<'a>>),
    #[cfg(feature = "alloc")]
    IObject(BTreeMap<ObjectKey<'a>, Value<'a>>),
    Tag(u64, &'a Value<'a>),
    Special(Special),
}

impl Serialize for Value<'_> {
    fn serialize<'se>(
        &'se self,
        serializer: &'se mut Serializer<'se>,
    ) -> Result<'se, &'se mut Serializer<'se>> {
        match self {
            Value::U64(ref v) => serializer.write_unsigned_integer(*v),
            Value::I64(ref v) => serializer.write_negative_integer(*v),
            Value::Bytes(ref v) => serializer.write_bytes(v),
            Value::Text(ref v) => serializer.write_text(v),
            Value::Array(ref v) => {
                let mut s = serializer.write_array(Len::Len(v.len() as u64))?;
                for element in v.iter() {
                    s = s.serialize(element)?;
                }
                Ok(s)
            }
            Value::IArray(ref v) => {
                let mut s = serializer.write_array(Len::Indefinite)?;
                for element in v.iter() {
                    s = s.serialize(element)?;
                }
                s.write_special(Special::Break)
            }
            #[cfg(feature = "alloc")]
            Value::Object(ref v) => {
                serializer.write_map(Len::Len(v.len() as u64))?;
                for element in v {
                    serializer.serialize(element.0)?.serialize(element.1)?;
                }
                Ok(serializer)
            }
            #[cfg(feature = "alloc")]
            Value::IObject(ref v) => {
                serializer.write_map(Len::Indefinite)?;
                for element in v {
                    serializer.serialize(element.0)?.serialize(element.1)?;
                }
                serializer.write_special(Special::Break)
            }
            Value::Tag(ref tag, ref v) => serializer.write_tag(*tag)?.serialize(v),
            Value::Special(ref v) => serializer.write_special(*v),
        }
    }
}
impl<'a> Deserialize<'a> for Value<'_> {
    fn deserialize(raw: &mut Deserializer<'a>) -> Result<'a, Self> {
        match raw.cbor_type()? {
            Type::UnsignedInteger => Ok(Value::U64(raw.unsigned_integer()?)),
            Type::NegativeInteger => Ok(Value::I64(raw.negative_integer()?)),
            Type::Bytes => Ok(Value::Bytes(raw.bytes()?)),
            Type::Text => Ok(Value::Text(raw.text()?)),
            Type::Array => {
                let len = raw.array()?;
                let mut vec = Vec::new();
                match len {
                    Len::Indefinite => {
                        while {
                            let t = raw.cbor_type()?;
                            if t == Type::Special {
                                let special = raw.special()?;
                                assert_eq!(special, Special::Break);
                                false
                            } else {
                                vec.push(Deserialize::deserialize(raw)?);
                                true
                            }
                        } {}
                        Ok(Value::IArray(vec))
                    }
                    Len::Len(len) => {
                        for _ in 0..len {
                            vec.push(Deserialize::deserialize(raw)?);
                        }
                        Ok(Value::Array(vec))
                    }
                }
            }
            #[cfg(feature = "alloc")]
            Type::Map => {
                let len = raw.map()?;
                let mut vec = BTreeMap::new();
                match len {
                    Len::Indefinite => {
                        while {
                            let t = raw.cbor_type()?;
                            if t == Type::Special {
                                let special = raw.special()?;
                                assert_eq!(special, Special::Break);
                                false
                            } else {
                                let k = Deserialize::deserialize(raw)?;
                                let v = Deserialize::deserialize(raw)?;
                                vec.insert(k, v);
                                true
                            }
                        } {}
                        Ok(Value::IObject(vec))
                    }
                    Len::Len(len) => {
                        for _ in 0..len {
                            let k = Deserialize::deserialize(raw)?;
                            let v = Deserialize::deserialize(raw)?;
                            vec.insert(k, v);
                        }
                        Ok(Value::Object(vec))
                    }
                }
            }
            Type::Tag => {
                let tag = raw.tag()?;
                Ok(Value::Tag(tag, &Deserialize::deserialize(raw)?))
            }
            Type::Special => Ok(Value::Special(raw.special()?)),
        }
    }
}

#[cfg(test)]
impl Arbitrary for ObjectKey {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        match u8::arbitrary(g) % 3 {
            0 => ObjectKey::Integer(Arbitrary::arbitrary(g)),
            1 => ObjectKey::Bytes(Arbitrary::arbitrary(g)),
            2 => ObjectKey::Text(Arbitrary::arbitrary(g)),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
fn arbitrary_value_finite<G: Gen>(g: &mut G) -> Value {
    match u8::arbitrary(g) % 5 {
        0 => Value::U64(Arbitrary::arbitrary(g)),
        1 => Value::I64(Arbitrary::arbitrary(g)),
        2 => Value::Bytes(Arbitrary::arbitrary(g)),
        3 => Value::Text(Arbitrary::arbitrary(g)),
        4 => Value::Special(Arbitrary::arbitrary(g)),
        _ => unreachable!(),
    }
}

#[cfg(test)]
fn arbitrary_value_indefinite<G: Gen>(counter: usize, g: &mut G) -> Value {
    if counter == 0 {
        arbitrary_value_finite(g)
    } else {
        match u8::arbitrary(g) % 5 {
            0 => Value::U64(u64::arbitrary(g)),
            1 => Value::I64(i64::arbitrary(g)),
            2 => Value::Bytes(Arbitrary::arbitrary(g)),
            3 => Value::Text(Arbitrary::arbitrary(g)),
            4 => {
                let size = usize::arbitrary(g);
                Value::Array(
                    repeat_with(|| arbitrary_value_indefinite(counter - 1, g))
                        .take(size)
                        .collect(),
                )
            }
            5 => {
                let size = usize::arbitrary(g);
                Value::IArray(
                    repeat_with(|| arbitrary_value_indefinite(counter - 1, g))
                        .take(size)
                        .collect(),
                )
            }
            6 => {
                let size = usize::arbitrary(g);
                Value::Object(
                    repeat_with(|| {
                        (
                            ObjectKey::arbitrary(g),
                            arbitrary_value_indefinite(counter - 1, g),
                        )
                    })
                    .take(size)
                    .collect(),
                )
            }
            7 => {
                let size = usize::arbitrary(g);
                Value::IObject(
                    repeat_with(|| {
                        (
                            ObjectKey::arbitrary(g),
                            arbitrary_value_indefinite(counter - 1, g),
                        )
                    })
                    .take(size)
                    .collect(),
                )
            }
            8 => Value::Tag(
                u64::arbitrary(g),
                arbitrary_value_indefinite(counter - 1, g).into(),
            ),
            9 => Value::Special(Arbitrary::arbitrary(g)),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
impl Arbitrary for Value {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        arbitrary_value_indefinite(3, g)
    }
}

#[cfg(test)]
mod test {
    use super::super::test_encode_decode;
    use super::*;

    #[test]
    fn u64() {
        assert!(test_encode_decode(&Value::U64(0)).unwrap());
        assert!(test_encode_decode(&Value::U64(23)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xff)).unwrap());
        assert!(test_encode_decode(&Value::U64(0x100)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xffff)).unwrap());
        assert!(test_encode_decode(&Value::U64(0x10000)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xffffffff)).unwrap());
        assert!(test_encode_decode(&Value::U64(0x100000000)).unwrap());
        assert!(test_encode_decode(&Value::U64(0xffffffffffffffff)).unwrap());
    }

    #[test]
    fn i64() {
        assert!(test_encode_decode(&Value::I64(0)).unwrap());
        assert!(test_encode_decode(&Value::I64(23)).unwrap());
        assert!(test_encode_decode(&Value::I64(-99)).unwrap());
        assert!(test_encode_decode(&Value::I64(99999)).unwrap());
        assert!(test_encode_decode(&Value::I64(-9999999)).unwrap());
        assert!(test_encode_decode(&Value::I64(-283749237289)).unwrap());
        assert!(test_encode_decode(&Value::I64(93892929229)).unwrap());
    }

    #[test]
    fn bytes() {
        assert!(test_encode_decode(&Value::Bytes(&[])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(&[0; 23])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(&[0; 24])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(&[0; 256])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(&[0; 10293])).unwrap());
        assert!(test_encode_decode(&Value::Bytes(&[0; 99999000])).unwrap());
    }

    #[test]
    fn text() {
        assert!(test_encode_decode(&Value::Text("")).unwrap());
        assert!(test_encode_decode(&Value::Text("hellow world")).unwrap());
        assert!(test_encode_decode(&Value::Text("some sentence, some sentence... some sentence...some sentence, some sentence... some sentence...")).unwrap());
    }

    #[test]
    fn array() {
        assert!(test_encode_decode(&Value::Array(&[])).unwrap());
        assert!(
            test_encode_decode(&Value::Array(&[Value::U64(0), Value::Text("some text")])).unwrap()
        );
    }

    #[test]
    fn iarray() {
        assert!(test_encode_decode(&Value::IArray(&[])).unwrap());
        assert!(
            test_encode_decode(&Value::IArray(&[Value::U64(0), Value::Text("some text")])).unwrap()
        );
    }

    #[test]
    fn tag() {
        assert!(test_encode_decode(&Value::Tag(23, &Value::U64(0))).unwrap());
        assert!(test_encode_decode(&Value::Tag(24, &Value::Bytes(&[0; 32]))).unwrap());
        assert!(test_encode_decode(&Value::Tag(0x1ff, &Value::Bytes(&[0; 624]))).unwrap());
    }

    quickcheck! {
        fn property_encode_decode(value: Value) -> bool {
            test_encode_decode(&value).unwrap()
        }
    }
}
