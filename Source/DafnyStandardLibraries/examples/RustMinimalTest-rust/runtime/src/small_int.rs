#![allow(unused_imports)]

use crate::DafnyPrint;
use crate::Rc;
use num::FromPrimitive;
use num::ToPrimitive;
use num::{bigint::ParseBigIntError, Integer, Num, One, Signed, Zero};
use std::{
    clone::Clone,
    cmp::Ordering,
    convert::From,
    fmt::Formatter,
    hash::Hash,
    ops::{Add, Div, Mul, Neg, Rem, Sub},
};

type InternalInt = i128;

#[derive(Clone, Copy)]
pub struct DafnyInt {
    data: InternalInt,
}

const ONE: DafnyInt = DafnyInt { data: 1 };
const ZERO: DafnyInt = DafnyInt { data: 0 };

impl DafnyInt {
    pub fn new(data: InternalInt) -> DafnyInt {
        DafnyInt { data }
    }
}

impl AsRef<InternalInt> for DafnyInt {
    fn as_ref(&self) -> &InternalInt {
        &self.data
    }
}

impl Default for DafnyInt {
    fn default() -> Self {
        ZERO
    }
}

impl Zero for DafnyInt {
    #[inline]
    fn zero() -> Self {
        ZERO
    }
    #[inline]
    fn is_zero(&self) -> bool {
        self.data == 0
    }
}
impl One for DafnyInt {
    #[inline]
    fn one() -> Self {
        ONE
    }
}

impl Num for DafnyInt {
    type FromStrRadixErr = std::num::ParseIntError;

    #[inline]
    fn from_str_radix(s: &str, radix: u32) -> Result<Self, std::num::ParseIntError> {
        let x = InternalInt::from_str_radix(s, radix)?;
        Ok(DafnyInt::new(x))
    }
}

impl Ord for DafnyInt {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.data.cmp(&other.data)
    }
}
impl Signed for DafnyInt {
    #[inline]
    fn abs(&self) -> Self {
        DafnyInt {
            data: self.data.abs(),
        }
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        DafnyInt {
            data: self.data.abs_sub(&other.data),
        }
    }

    #[inline]
    fn signum(&self) -> Self {
        DafnyInt {
            data: self.data.signum(),
        }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.data.is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.data.is_negative()
    }
}

// Comparison
impl PartialOrd<DafnyInt> for DafnyInt {
    #[inline]
    fn partial_cmp(&self, other: &DafnyInt) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl DafnyInt {
    #[inline]
    pub fn parse_bytes(number: &[u8], radix: u32) -> DafnyInt {
        let x = InternalInt::from_str_radix(std::str::from_utf8(number).unwrap(), radix).unwrap();
        DafnyInt::new(x)
    }
    pub fn from_usize(usize: usize) -> DafnyInt {
        DafnyInt {
            data: usize as InternalInt,
        }
    }
    pub fn from_i32(i: i32) -> DafnyInt {
        DafnyInt {
            data: i as InternalInt,
        }
    }
}

// impl<const N: usize> From<&[u8; N]> for DafnyInt {
//     fn from(number: &[u8; N]) -> Self {
//         DafnyInt::parse_bytes(number, 10)
//     }
// }

// impl From<&[u8]> for DafnyInt {
//     fn from(val: &[u8]) -> DafnyInt {
//         DafnyInt::parse_bytes(val, 10)
//     }
// }

impl From<DafnyInt> for u8 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_u8().unwrap()
    }
}
impl From<DafnyInt> for u16 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_u16().unwrap()
    }
}
impl From<DafnyInt> for u32 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_u32().unwrap()
    }
}
impl From<DafnyInt> for u64 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_u64().unwrap()
    }
}
impl From<DafnyInt> for u128 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_u128().unwrap()
    }
}
impl From<DafnyInt> for i8 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_i8().unwrap()
    }
}
impl From<DafnyInt> for i16 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_i16().unwrap()
    }
}
impl From<DafnyInt> for i32 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_i32().unwrap()
    }
}
impl From<DafnyInt> for i64 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_i64().unwrap()
    }
}
impl From<DafnyInt> for i128 {
    fn from(val: DafnyInt) -> Self {
        val.data.to_i128().unwrap()
    }
}
impl From<DafnyInt> for usize {
    fn from(val: DafnyInt) -> Self {
        val.data.to_usize().unwrap()
    }
}

impl ToPrimitive for DafnyInt {
    fn to_i64(&self) -> Option<i64> {
        self.data.to_i64()
    }

    fn to_u64(&self) -> Option<u64> {
        self.data.to_u64()
    }

    // Override of functions
    fn to_u128(&self) -> Option<u128> {
        self.data.to_u128()
    }

    fn to_i128(&self) -> Option<i128> {
        self.data.to_i128()
    }
}

impl PartialEq<DafnyInt> for DafnyInt {
    fn eq(&self, other: &DafnyInt) -> bool {
        self.data.eq(&other.data)
    }
}
impl Eq for DafnyInt {}
impl Hash for DafnyInt {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.data.hash(state);
    }
}

impl DafnyPrint for DafnyInt {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl ::std::fmt::Debug for DafnyInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl Add<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn add(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: self.data + rhs.data,
        }
    }
}

impl Mul<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn mul(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: self.data * rhs.data,
        }
    }
}

impl Div<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn div(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: self.data / rhs.data,
        }
    }
}

impl Sub<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn sub(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: self.data - rhs.data,
        }
    }
}
impl Rem<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn rem(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: self.data % rhs.data,
        }
    }
}
impl Neg for DafnyInt {
    type Output = DafnyInt;

    #[inline]
    fn neg(self) -> Self::Output {
        DafnyInt { data: -self.data }
    }
}

macro_rules! impl_dafnyint_from {
    () => {};
    ($type:ident) => {
        #[allow(trivial_numeric_casts)]
        impl ::std::convert::From<$type> for $crate::DafnyInt {
            fn from(n: $type) -> Self {
                $crate::DafnyInt {
                    data: n as InternalInt,
                }
            }
        }
        #[allow(trivial_numeric_casts)]
        impl $crate::DafnyUsize for $type {
            fn into_usize(self) -> usize {
                self as usize
            }
        }
    };
}

impl_dafnyint_from! { u8 }
impl_dafnyint_from! { u16 }
impl_dafnyint_from! { u32 }
impl_dafnyint_from! { u64 }
impl_dafnyint_from! { u128 }
impl_dafnyint_from! { i8 }
impl_dafnyint_from! { i16 }
impl_dafnyint_from! { i32 }
impl_dafnyint_from! { i64 }
impl_dafnyint_from! { i128 }
impl_dafnyint_from! { usize }
