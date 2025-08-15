use crate::DafnyPrint;
use crate::Rc;
use num::bigint::BigInt;
use num::rational::BigRational;
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

// Zero-cost abstraction over a Rc<BigInt>

#[derive(Clone)]
pub struct DafnyInt {
    data: Rc<BigInt>,
}

impl DafnyInt {
    pub fn new(data: Rc<BigInt>) -> DafnyInt {
        DafnyInt { data }
    }
    pub fn strong_count(&self) -> usize {
        Rc::strong_count(&self.data)
    }
}

impl AsRef<BigInt> for DafnyInt {
    fn as_ref(&self) -> &BigInt {
        &self.data
    }
}

impl Default for DafnyInt {
    fn default() -> Self {
        DafnyInt::new(Rc::new(BigInt::zero()))
    }
}

pub fn dafny_int_to_bigint(i: &DafnyInt) -> BigInt {
    i.data.as_ref().clone()
}
pub fn bigint_to_dafny_int(i: &BigInt) -> DafnyInt {
    DafnyInt {
        data: Rc::new(i.clone()),
    }
}

impl Zero for DafnyInt {
    #[inline]
    fn zero() -> Self {
        DafnyInt {
            data: Rc::new(BigInt::zero()),
        }
    }
    #[inline]
    fn is_zero(&self) -> bool {
        self.data.is_zero()
    }
}
impl One for DafnyInt {
    #[inline]
    fn one() -> Self {
        DafnyInt {
            data: Rc::new(BigInt::one()),
        }
    }
}
impl Num for DafnyInt {
    type FromStrRadixErr = ParseBigIntError;

    #[inline]
    fn from_str_radix(s: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Ok(DafnyInt {
            data: Rc::new(BigInt::from_str_radix(s, radix)?),
        })
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
            data: Rc::new(self.data.as_ref().abs()),
        }
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        DafnyInt {
            data: Rc::new(self.data.as_ref().abs_sub(other.data.as_ref())),
        }
    }

    #[inline]
    fn signum(&self) -> Self {
        DafnyInt {
            data: Rc::new(self.data.as_ref().signum()),
        }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.data.as_ref().is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.data.as_ref().is_negative()
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
        DafnyInt {
            data: Rc::new(BigInt::parse_bytes(number, radix).unwrap()),
        }
    }
    pub fn from_usize(usize: usize) -> DafnyInt {
        DafnyInt {
            data: Rc::new(BigInt::from(usize)),
        }
    }
    pub fn from_i32(i: i32) -> DafnyInt {
        DafnyInt {
            data: Rc::new(BigInt::from(i)),
        }
    }
}

// fn dafny_rational_to_int(r: &BigRational) -> BigInt {
//     euclidian_division(r.numer().clone(), r.denom().clone())
// }

impl DafnyPrint for BigInt {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

fn divides_a_power_of_10(mut i: BigInt) -> (bool, BigInt, usize) {
    let one: BigInt = One::one();

    let mut factor = one.clone();
    let mut log10 = 0;

    let zero = Zero::zero();
    let ten = BigInt::from_i32(10).unwrap();

    if i <= zero {
        return (false, factor, log10);
    }

    while i.is_multiple_of(&ten) {
        i /= BigInt::from_i32(10).unwrap();
        log10 += 1;
    }

    let two = BigInt::from_i32(2).unwrap();
    let five = BigInt::from_i32(5).unwrap();

    while i.is_multiple_of(&five) {
        i /= &five;
        factor *= &two;
        log10 += 1;
    }

    while i.is_multiple_of(&two) {
        i /= &two;
        factor *= &two;
        log10 += 1;
    }

    (i == one, factor, log10)
}

impl DafnyPrint for BigRational {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        if self.denom() == &One::one() || self.numer() == &Zero::zero() {
            write!(f, "{}.0", self.numer())
        } else {
            let (divides, factor, log10) = divides_a_power_of_10(self.denom().clone());
            if divides {
                let mut num = self.numer().clone();
                num *= factor;

                if num.is_negative() {
                    write!(f, "-")?;
                    num = -num;
                }

                let digits = num.to_string();

                if log10 < digits.len() {
                    let digit_count = digits.len() - log10;
                    write!(f, "{}", &digits[..digit_count])?;
                    write!(f, ".")?;
                    write!(f, "{}", &digits[digit_count..])
                } else {
                    let z = log10 - digits.len();
                    write!(f, "0.")?;
                    for _ in 0..z {
                        write!(f, "0")?;
                    }
                    write!(f, "{}", digits)
                }
            } else {
                write!(f, "({}.0 / {}.0)", self.numer(), self.denom())
            }
        }
    }
}

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
            data: Rc::new(self.data.as_ref() + rhs.data.as_ref()),
        }
    }
}

impl Mul<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn mul(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: Rc::new(self.data.as_ref() * rhs.data.as_ref()),
        }
    }
}

impl Div<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn div(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: Rc::new(self.data.as_ref() / rhs.data.as_ref()),
        }
    }
}

impl Sub<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn sub(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: Rc::new(self.data.as_ref() - rhs.data.as_ref()),
        }
    }
}
impl Rem<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn rem(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt {
            data: Rc::new(self.data.as_ref() % rhs.data.as_ref()),
        }
    }
}
impl Neg for DafnyInt {
    type Output = DafnyInt;

    #[inline]
    fn neg(self) -> Self::Output {
        DafnyInt {
            data: Rc::new(-self.data.as_ref()),
        }
    }
}

macro_rules! impl_dafnyint_from {
    () => {};
    ($type:ident) => {
        impl ::std::convert::From<$type> for $crate::DafnyInt {
            fn from(n: $type) -> Self {
                $crate::DafnyInt {
                    data: $crate::Rc::new(n.into()),
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
