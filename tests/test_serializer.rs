#![cfg(feature = "serde")]
use serde::{
    ser::{
        SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant, SerializeTuple,
        SerializeTupleStruct, SerializeTupleVariant,
    },
    Serialize, Serializer,
};
use std::fmt::{Display, Formatter};

pub struct TestSerializer;

#[derive(PartialEq, Eq, Debug)]
pub enum Number {
    U64(u64),
    I64(i64),
}

#[derive(Debug)]
pub struct Error(String);

impl Display for Error {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

impl From<&'static str> for Error {
    fn from(error: &'static str) -> Self {
        Self(error.to_owned())
    }
}

impl serde::ser::Error for Error {
    fn custom<T>(message: T) -> Self
    where
        T: Display,
    {
        Self(message.to_string())
    }
}

pub enum Never {}

impl Serializer for TestSerializer {
    type Ok = Number;
    type Error = Error;
    type SerializeSeq = Never;
    type SerializeTuple = Never;
    type SerializeTupleStruct = Never;
    type SerializeTupleVariant = Never;
    type SerializeMap = Never;
    type SerializeStruct = Never;
    type SerializeStructVariant = Never;

    fn serialize_bool(self, _: bool) -> Result<Self::Ok, Self::Error> {
        Err("serialize_bool".into())
    }

    fn serialize_i8(self, _: i8) -> Result<Self::Ok, Self::Error> {
        Err("serialize_i8".into())
    }

    fn serialize_i16(self, _: i16) -> Result<Self::Ok, Self::Error> {
        Err("serialize_i16".into())
    }

    fn serialize_i32(self, _: i32) -> Result<Self::Ok, Self::Error> {
        Err("serialize_i32".into())
    }

    fn serialize_i64(self, number: i64) -> Result<Self::Ok, Self::Error> {
        Ok(Number::I64(number))
    }

    fn serialize_u8(self, _: u8) -> Result<Self::Ok, Self::Error> {
        Err("serialize_u8".into())
    }

    fn serialize_u16(self, _: u16) -> Result<Self::Ok, Self::Error> {
        Err("serialize_u16".into())
    }

    fn serialize_u32(self, _: u32) -> Result<Self::Ok, Self::Error> {
        Err("serialize_u32".into())
    }

    fn serialize_u64(self, number: u64) -> Result<Self::Ok, Self::Error> {
        Ok(Number::U64(number))
    }

    fn serialize_f32(self, _: f32) -> Result<Self::Ok, Self::Error> {
        Err("serialize_f32".into())
    }

    fn serialize_f64(self, _: f64) -> Result<Self::Ok, Self::Error> {
        Err("serialize_f64".into())
    }

    fn serialize_char(self, _: char) -> Result<Self::Ok, Self::Error> {
        Err("serialize_char".into())
    }

    fn serialize_str(self, _: &str) -> Result<Self::Ok, Self::Error> {
        Err("serialize_str".into())
    }

    fn serialize_bytes(self, _: &[u8]) -> Result<Self::Ok, Self::Error> {
        Err("serialize_bytes".into())
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Err("serialize_none".into())
    }

    fn serialize_some<T>(self, _: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        Err("serialize_some".into())
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Err("serialize_unit".into())
    }

    fn serialize_unit_struct(self, _: &'static str) -> Result<Self::Ok, Self::Error> {
        Err("serialize_unit_struct".into())
    }

    fn serialize_unit_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Err("serialize_unit_variant".into())
    }

    fn serialize_newtype_struct<T>(self, _: &'static str, _: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        Err("serialize_newtype_struct".into())
    }

    fn serialize_newtype_variant<T>(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Serialize,
    {
        Err("serialize_newtype_variant".into())
    }

    fn serialize_seq(self, _: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err("serialize_seq".into())
    }

    fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Err("serialize_tuple".into())
    }

    fn serialize_tuple_struct(
        self,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Err("serialize_tuple_struct".into())
    }

    fn serialize_tuple_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Err("serialize_tuple_variant".into())
    }

    fn serialize_map(self, _: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Err("serialize_map".into())
    }

    fn serialize_struct(
        self,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Err("serialize_struct".into())
    }

    fn serialize_struct_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Err("serialize_struct_variant".into())
    }

    fn collect_str<T>(self, _: &T) -> Result<Self::Ok, Self::Error>
    where
        T: ?Sized + Display,
    {
        Err("collect_str".into())
    }
}

impl SerializeSeq for Never {
    type Ok = Number;
    type Error = Error;

    fn serialize_element<T>(&mut self, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        unreachable!()
    }
}

impl SerializeTuple for Never {
    type Ok = Number;
    type Error = Error;

    fn serialize_element<T>(&mut self, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        unreachable!()
    }
}

impl SerializeTupleStruct for Never {
    type Ok = Number;
    type Error = Error;

    fn serialize_field<T>(&mut self, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        unreachable!()
    }
}

impl SerializeTupleVariant for Never {
    type Ok = Number;
    type Error = Error;

    fn serialize_field<T>(&mut self, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        unreachable!()
    }
}

impl SerializeMap for Never {
    type Ok = Number;
    type Error = Error;

    fn serialize_key<T>(&mut self, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn serialize_value<T>(&mut self, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        unreachable!()
    }
}

impl SerializeStruct for Never {
    type Ok = Number;
    type Error = Error;

    fn serialize_field<T>(&mut self, _: &'static str, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        unreachable!()
    }
}

impl SerializeStructVariant for Never {
    type Ok = Number;
    type Error = Error;

    fn serialize_field<T>(&mut self, _: &'static str, _: &T) -> Result<(), Self::Error>
    where
        T: ?Sized + Serialize,
    {
        unreachable!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        unreachable!()
    }
}
