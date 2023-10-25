#![allow(warnings, unconditional_panic)]
extern crate dafny_runtime;
mod r#_System {
#[derive(Clone, PartialEq)]
#[repr(transparent)]
pub struct r#nat(pub ::dafny_runtime::BigInt);
impl  ::dafny_runtime::DafnyErasable for r#nat {
type Erased = ::dafny_runtime::BigInt;
}
impl  ::dafny_runtime::DafnyUnerasable<::dafny_runtime::BigInt> for r#nat {}
impl  ::dafny_runtime::DafnyUnerasable<r#nat> for r#nat {}
impl  ::std::default::Default for r#nat {
fn default() -> Self {
r#nat(::std::default::Default::default())
}
}
impl  ::dafny_runtime::DafnyPrint for r#nat {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
::dafny_runtime::DafnyPrint::fmt_print(&self.0, __fmt_print_formatter, in_seq)
}
}
impl  ::std::ops::Deref for r#nat {
type Target = ::dafny_runtime::BigInt;
fn deref(&self) -> &Self::Target {
&self.0
}
}

#[derive(PartialEq)]
pub enum r#Tuple2<r#T0, r#T1, > {
r#___hMake2 { r#_0: r#T0, r#_1: r#T1, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple2<r#T0, r#T1, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple2::r#___hMake2 { r#_0, r#_1, } => r#_0,
r#Tuple2::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple2::r#___hMake2 { r#_0, r#_1, } => r#_1,
r#Tuple2::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple2<r#T0, r#T1, > {
type Erased = r#Tuple2<r#T0::Erased, r#T1::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple2<r#T0__Erased, r#T1__Erased, >> for r#Tuple2<r#T0, r#T1, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple2<r#T0, r#T1, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple2::r#___hMake2 { r#_0, r#_1, } => {
write!(__fmt_print_formatter, "_System.Tuple2.___hMake2(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple2::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple2<r#T0, r#T1, > {
fn default() -> Self {
r#Tuple2::r#___hMake2 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple0 {
r#___hMake0 { },

}
impl  r#Tuple0 {

}
impl  ::dafny_runtime::DafnyErasable for r#Tuple0 {
type Erased = r#Tuple0;
}
impl  ::dafny_runtime::DafnyUnerasable<r#Tuple0> for r#Tuple0 {}

impl  ::dafny_runtime::DafnyPrint for r#Tuple0 {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple0::r#___hMake0 { } => {
write!(__fmt_print_formatter, "_System.Tuple0.___hMake0")?;
Ok(())
}
}
}
}

impl  ::std::default::Default for r#Tuple0 {
fn default() -> Self {
r#Tuple0::r#___hMake0 {
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple3<r#T0, r#T1, r#T2, > {
r#___hMake3 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple3<r#T0, r#T1, r#T2, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple3::r#___hMake3 { r#_0, r#_1, r#_2, } => r#_0,
r#Tuple3::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple3::r#___hMake3 { r#_0, r#_1, r#_2, } => r#_1,
r#Tuple3::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple3::r#___hMake3 { r#_0, r#_1, r#_2, } => r#_2,
r#Tuple3::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple3<r#T0, r#T1, r#T2, > {
type Erased = r#Tuple3<r#T0::Erased, r#T1::Erased, r#T2::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple3<r#T0__Erased, r#T1__Erased, r#T2__Erased, >> for r#Tuple3<r#T0, r#T1, r#T2, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple3<r#T0, r#T1, r#T2, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple3::r#___hMake3 { r#_0, r#_1, r#_2, } => {
write!(__fmt_print_formatter, "_System.Tuple3.___hMake3(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple3::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple3<r#T0, r#T1, r#T2, > {
fn default() -> Self {
r#Tuple3::r#___hMake3 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple4<r#T0, r#T1, r#T2, r#T3, > {
r#___hMake4 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple4<r#T0, r#T1, r#T2, r#T3, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple4::r#___hMake4 { r#_0, r#_1, r#_2, r#_3, } => r#_0,
r#Tuple4::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple4::r#___hMake4 { r#_0, r#_1, r#_2, r#_3, } => r#_1,
r#Tuple4::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple4::r#___hMake4 { r#_0, r#_1, r#_2, r#_3, } => r#_2,
r#Tuple4::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple4::r#___hMake4 { r#_0, r#_1, r#_2, r#_3, } => r#_3,
r#Tuple4::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple4<r#T0, r#T1, r#T2, r#T3, > {
type Erased = r#Tuple4<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple4<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, >> for r#Tuple4<r#T0, r#T1, r#T2, r#T3, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple4<r#T0, r#T1, r#T2, r#T3, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple4::r#___hMake4 { r#_0, r#_1, r#_2, r#_3, } => {
write!(__fmt_print_formatter, "_System.Tuple4.___hMake4(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple4::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple4<r#T0, r#T1, r#T2, r#T3, > {
fn default() -> Self {
r#Tuple4::r#___hMake4 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple5<r#T0, r#T1, r#T2, r#T3, r#T4, > {
r#___hMake5 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple5<r#T0, r#T1, r#T2, r#T3, r#T4, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple5::r#___hMake5 { r#_0, r#_1, r#_2, r#_3, r#_4, } => r#_0,
r#Tuple5::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple5::r#___hMake5 { r#_0, r#_1, r#_2, r#_3, r#_4, } => r#_1,
r#Tuple5::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple5::r#___hMake5 { r#_0, r#_1, r#_2, r#_3, r#_4, } => r#_2,
r#Tuple5::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple5::r#___hMake5 { r#_0, r#_1, r#_2, r#_3, r#_4, } => r#_3,
r#Tuple5::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple5::r#___hMake5 { r#_0, r#_1, r#_2, r#_3, r#_4, } => r#_4,
r#Tuple5::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple5<r#T0, r#T1, r#T2, r#T3, r#T4, > {
type Erased = r#Tuple5<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple5<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, >> for r#Tuple5<r#T0, r#T1, r#T2, r#T3, r#T4, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple5<r#T0, r#T1, r#T2, r#T3, r#T4, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple5::r#___hMake5 { r#_0, r#_1, r#_2, r#_3, r#_4, } => {
write!(__fmt_print_formatter, "_System.Tuple5.___hMake5(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple5::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple5<r#T0, r#T1, r#T2, r#T3, r#T4, > {
fn default() -> Self {
r#Tuple5::r#___hMake5 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple6<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, > {
r#___hMake6 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple6<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple6::r#___hMake6 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, } => r#_0,
r#Tuple6::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple6::r#___hMake6 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, } => r#_1,
r#Tuple6::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple6::r#___hMake6 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, } => r#_2,
r#Tuple6::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple6::r#___hMake6 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, } => r#_3,
r#Tuple6::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple6::r#___hMake6 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, } => r#_4,
r#Tuple6::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple6::r#___hMake6 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, } => r#_5,
r#Tuple6::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple6<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, > {
type Erased = r#Tuple6<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple6<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, >> for r#Tuple6<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple6<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple6::r#___hMake6 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, } => {
write!(__fmt_print_formatter, "_System.Tuple6.___hMake6(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple6::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple6<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, > {
fn default() -> Self {
r#Tuple6::r#___hMake6 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple7<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, > {
r#___hMake7 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple7<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => r#_0,
r#Tuple7::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => r#_1,
r#Tuple7::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => r#_2,
r#Tuple7::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => r#_3,
r#Tuple7::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => r#_4,
r#Tuple7::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => r#_5,
r#Tuple7::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => r#_6,
r#Tuple7::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple7<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, > {
type Erased = r#Tuple7<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple7<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, >> for r#Tuple7<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple7<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple7::r#___hMake7 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, } => {
write!(__fmt_print_formatter, "_System.Tuple7.___hMake7(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple7::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple7<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, > {
fn default() -> Self {
r#Tuple7::r#___hMake7 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple8<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, > {
r#___hMake8 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple8<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_0,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_1,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_2,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_3,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_4,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_5,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_6,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => r#_7,
r#Tuple8::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple8<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, > {
type Erased = r#Tuple8<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple8<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, >> for r#Tuple8<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple8<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple8::r#___hMake8 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, } => {
write!(__fmt_print_formatter, "_System.Tuple8.___hMake8(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple8::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple8<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, > {
fn default() -> Self {
r#Tuple8::r#___hMake8 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple9<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, > {
r#___hMake9 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple9<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_0,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_1,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_2,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_3,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_4,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_5,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_6,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_7,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => r#_8,
r#Tuple9::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple9<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, > {
type Erased = r#Tuple9<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple9<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, >> for r#Tuple9<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple9<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple9::r#___hMake9 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, } => {
write!(__fmt_print_formatter, "_System.Tuple9.___hMake9(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple9::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple9<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, > {
fn default() -> Self {
r#Tuple9::r#___hMake9 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple10<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, > {
r#___hMake10 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple10<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_0,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_1,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_2,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_3,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_4,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_5,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_6,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_7,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_8,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => r#_9,
r#Tuple10::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple10<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, > {
type Erased = r#Tuple10<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple10<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, >> for r#Tuple10<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple10<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple10::r#___hMake10 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, } => {
write!(__fmt_print_formatter, "_System.Tuple10.___hMake10(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple10::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple10<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, > {
fn default() -> Self {
r#Tuple10::r#___hMake10 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple11<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, > {
r#___hMake11 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple11<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_0,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_1,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_2,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_3,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_4,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_5,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_6,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_7,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_8,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_9,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => r#_10,
r#Tuple11::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple11<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, > {
type Erased = r#Tuple11<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple11<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, >> for r#Tuple11<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple11<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple11::r#___hMake11 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, } => {
write!(__fmt_print_formatter, "_System.Tuple11.___hMake11(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple11::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple11<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, > {
fn default() -> Self {
r#Tuple11::r#___hMake11 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple12<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, > {
r#___hMake12 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple12<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_0,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_1,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_2,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_3,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_4,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_5,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_6,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_7,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_8,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_9,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_10,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => r#_11,
r#Tuple12::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple12<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, > {
type Erased = r#Tuple12<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple12<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, >> for r#Tuple12<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple12<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple12::r#___hMake12 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, } => {
write!(__fmt_print_formatter, "_System.Tuple12.___hMake12(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple12::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple12<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, > {
fn default() -> Self {
r#Tuple12::r#___hMake12 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple13<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, > {
r#___hMake13 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple13<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_0,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_1,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_2,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_3,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_4,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_5,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_6,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_7,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_8,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_9,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_10,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_11,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => r#_12,
r#Tuple13::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple13<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, > {
type Erased = r#Tuple13<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple13<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, >> for r#Tuple13<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple13<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple13::r#___hMake13 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, } => {
write!(__fmt_print_formatter, "_System.Tuple13.___hMake13(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple13::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple13<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, > {
fn default() -> Self {
r#Tuple13::r#___hMake13 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple14<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, > {
r#___hMake14 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, r#_13: r#T13, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>, ::std::marker::PhantomData::<r#T13>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple14<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T13 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_0,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_1,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_2,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_3,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_4,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_5,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_6,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_7,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_8,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_9,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_10,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_11,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_12,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_13(&self) -> &r#T13 {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => r#_13,
r#Tuple14::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple14<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, > {
type Erased = r#Tuple14<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, r#T13::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, r#T13__Erased, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T13__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple14<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, r#T13__Erased, >> for r#Tuple14<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple14<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple14::r#___hMake14 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, } => {
write!(__fmt_print_formatter, "_System.Tuple14.___hMake14(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_13, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple14::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple14<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, > {
fn default() -> Self {
r#Tuple14::r#___hMake14 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
r#_13: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple15<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, > {
r#___hMake15 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, r#_13: r#T13, r#_14: r#T14, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>, ::std::marker::PhantomData::<r#T13>, ::std::marker::PhantomData::<r#T14>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple15<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T13 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T14 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_0,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_1,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_2,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_3,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_4,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_5,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_6,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_7,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_8,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_9,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_10,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_11,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_12,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_13(&self) -> &r#T13 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_13,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_14(&self) -> &r#T14 {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => r#_14,
r#Tuple15::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple15<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, > {
type Erased = r#Tuple15<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, r#T13::Erased, r#T14::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, r#T13__Erased, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T13__Erased> + 'static, r#T14__Erased, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T14__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple15<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, r#T13__Erased, r#T14__Erased, >> for r#Tuple15<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple15<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple15::r#___hMake15 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, } => {
write!(__fmt_print_formatter, "_System.Tuple15.___hMake15(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_13, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_14, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple15::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple15<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, > {
fn default() -> Self {
r#Tuple15::r#___hMake15 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
r#_13: ::std::default::Default::default(),
r#_14: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple16<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, > {
r#___hMake16 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, r#_13: r#T13, r#_14: r#T14, r#_15: r#T15, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>, ::std::marker::PhantomData::<r#T13>, ::std::marker::PhantomData::<r#T14>, ::std::marker::PhantomData::<r#T15>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple16<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T13 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T14 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T15 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_0,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_1,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_2,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_3,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_4,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_5,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_6,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_7,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_8,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_9,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_10,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_11,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_12,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_13(&self) -> &r#T13 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_13,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_14(&self) -> &r#T14 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_14,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_15(&self) -> &r#T15 {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => r#_15,
r#Tuple16::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple16<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, > {
type Erased = r#Tuple16<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, r#T13::Erased, r#T14::Erased, r#T15::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, r#T13__Erased, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T13__Erased> + 'static, r#T14__Erased, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T14__Erased> + 'static, r#T15__Erased, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T15__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple16<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, r#T13__Erased, r#T14__Erased, r#T15__Erased, >> for r#Tuple16<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple16<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple16::r#___hMake16 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, } => {
write!(__fmt_print_formatter, "_System.Tuple16.___hMake16(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_13, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_14, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_15, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple16::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple16<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, > {
fn default() -> Self {
r#Tuple16::r#___hMake16 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
r#_13: ::std::default::Default::default(),
r#_14: ::std::default::Default::default(),
r#_15: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple17<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, > {
r#___hMake17 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, r#_13: r#T13, r#_14: r#T14, r#_15: r#T15, r#_16: r#T16, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>, ::std::marker::PhantomData::<r#T13>, ::std::marker::PhantomData::<r#T14>, ::std::marker::PhantomData::<r#T15>, ::std::marker::PhantomData::<r#T16>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple17<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T13 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T14 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T15 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T16 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_0,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_1,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_2,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_3,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_4,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_5,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_6,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_7,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_8,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_9,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_10,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_11,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_12,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_13(&self) -> &r#T13 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_13,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_14(&self) -> &r#T14 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_14,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_15(&self) -> &r#T15 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_15,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_16(&self) -> &r#T16 {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => r#_16,
r#Tuple17::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple17<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, > {
type Erased = r#Tuple17<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, r#T13::Erased, r#T14::Erased, r#T15::Erased, r#T16::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, r#T13__Erased, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T13__Erased> + 'static, r#T14__Erased, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T14__Erased> + 'static, r#T15__Erased, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T15__Erased> + 'static, r#T16__Erased, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T16__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple17<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, r#T13__Erased, r#T14__Erased, r#T15__Erased, r#T16__Erased, >> for r#Tuple17<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple17<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple17::r#___hMake17 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, } => {
write!(__fmt_print_formatter, "_System.Tuple17.___hMake17(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_13, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_14, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_15, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_16, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple17::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple17<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, > {
fn default() -> Self {
r#Tuple17::r#___hMake17 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
r#_13: ::std::default::Default::default(),
r#_14: ::std::default::Default::default(),
r#_15: ::std::default::Default::default(),
r#_16: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple18<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, > {
r#___hMake18 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, r#_13: r#T13, r#_14: r#T14, r#_15: r#T15, r#_16: r#T16, r#_17: r#T17, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>, ::std::marker::PhantomData::<r#T13>, ::std::marker::PhantomData::<r#T14>, ::std::marker::PhantomData::<r#T15>, ::std::marker::PhantomData::<r#T16>, ::std::marker::PhantomData::<r#T17>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple18<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T13 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T14 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T15 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T16 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T17 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_0,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_1,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_2,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_3,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_4,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_5,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_6,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_7,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_8,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_9,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_10,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_11,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_12,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_13(&self) -> &r#T13 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_13,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_14(&self) -> &r#T14 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_14,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_15(&self) -> &r#T15 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_15,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_16(&self) -> &r#T16 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_16,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_17(&self) -> &r#T17 {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => r#_17,
r#Tuple18::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple18<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, > {
type Erased = r#Tuple18<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, r#T13::Erased, r#T14::Erased, r#T15::Erased, r#T16::Erased, r#T17::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, r#T13__Erased, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T13__Erased> + 'static, r#T14__Erased, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T14__Erased> + 'static, r#T15__Erased, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T15__Erased> + 'static, r#T16__Erased, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T16__Erased> + 'static, r#T17__Erased, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T17__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple18<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, r#T13__Erased, r#T14__Erased, r#T15__Erased, r#T16__Erased, r#T17__Erased, >> for r#Tuple18<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple18<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple18::r#___hMake18 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, } => {
write!(__fmt_print_formatter, "_System.Tuple18.___hMake18(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_13, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_14, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_15, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_16, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_17, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple18::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple18<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, > {
fn default() -> Self {
r#Tuple18::r#___hMake18 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
r#_13: ::std::default::Default::default(),
r#_14: ::std::default::Default::default(),
r#_15: ::std::default::Default::default(),
r#_16: ::std::default::Default::default(),
r#_17: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple19<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, > {
r#___hMake19 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, r#_13: r#T13, r#_14: r#T14, r#_15: r#T15, r#_16: r#T16, r#_17: r#T17, r#_18: r#T18, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>, ::std::marker::PhantomData::<r#T13>, ::std::marker::PhantomData::<r#T14>, ::std::marker::PhantomData::<r#T15>, ::std::marker::PhantomData::<r#T16>, ::std::marker::PhantomData::<r#T17>, ::std::marker::PhantomData::<r#T18>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple19<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T13 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T14 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T15 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T16 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T17 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T18 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_0,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_1,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_2,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_3,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_4,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_5,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_6,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_7,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_8,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_9,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_10,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_11,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_12,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_13(&self) -> &r#T13 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_13,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_14(&self) -> &r#T14 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_14,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_15(&self) -> &r#T15 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_15,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_16(&self) -> &r#T16 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_16,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_17(&self) -> &r#T17 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_17,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_18(&self) -> &r#T18 {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => r#_18,
r#Tuple19::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple19<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, > {
type Erased = r#Tuple19<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, r#T13::Erased, r#T14::Erased, r#T15::Erased, r#T16::Erased, r#T17::Erased, r#T18::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, r#T13__Erased, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T13__Erased> + 'static, r#T14__Erased, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T14__Erased> + 'static, r#T15__Erased, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T15__Erased> + 'static, r#T16__Erased, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T16__Erased> + 'static, r#T17__Erased, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T17__Erased> + 'static, r#T18__Erased, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T18__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple19<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, r#T13__Erased, r#T14__Erased, r#T15__Erased, r#T16__Erased, r#T17__Erased, r#T18__Erased, >> for r#Tuple19<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple19<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple19::r#___hMake19 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, } => {
write!(__fmt_print_formatter, "_System.Tuple19.___hMake19(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_13, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_14, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_15, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_16, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_17, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_18, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple19::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple19<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, > {
fn default() -> Self {
r#Tuple19::r#___hMake19 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
r#_13: ::std::default::Default::default(),
r#_14: ::std::default::Default::default(),
r#_15: ::std::default::Default::default(),
r#_16: ::std::default::Default::default(),
r#_17: ::std::default::Default::default(),
r#_18: ::std::default::Default::default(),
}
}
}

#[derive(PartialEq)]
pub enum r#Tuple20<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, r#T19, > {
r#___hMake20 { r#_0: r#T0, r#_1: r#T1, r#_2: r#T2, r#_3: r#T3, r#_4: r#T4, r#_5: r#T5, r#_6: r#T6, r#_7: r#T7, r#_8: r#T8, r#_9: r#T9, r#_10: r#T10, r#_11: r#T11, r#_12: r#T12, r#_13: r#T13, r#_14: r#T14, r#_15: r#T15, r#_16: r#T16, r#_17: r#T17, r#_18: r#T18, r#_19: r#T19, },
_PhantomVariant(::std::marker::PhantomData::<r#T0>, ::std::marker::PhantomData::<r#T1>, ::std::marker::PhantomData::<r#T2>, ::std::marker::PhantomData::<r#T3>, ::std::marker::PhantomData::<r#T4>, ::std::marker::PhantomData::<r#T5>, ::std::marker::PhantomData::<r#T6>, ::std::marker::PhantomData::<r#T7>, ::std::marker::PhantomData::<r#T8>, ::std::marker::PhantomData::<r#T9>, ::std::marker::PhantomData::<r#T10>, ::std::marker::PhantomData::<r#T11>, ::std::marker::PhantomData::<r#T12>, ::std::marker::PhantomData::<r#T13>, ::std::marker::PhantomData::<r#T14>, ::std::marker::PhantomData::<r#T15>, ::std::marker::PhantomData::<r#T16>, ::std::marker::PhantomData::<r#T17>, ::std::marker::PhantomData::<r#T18>, ::std::marker::PhantomData::<r#T19>)
}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T19: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T19> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > r#Tuple20<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, r#T19, > where <r#T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T2 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T3 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T4 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T5 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T6 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T7 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T8 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T9 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T10 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T11 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T12 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T13 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T14 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T15 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T16 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T17 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T18 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <r#T19 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
pub fn r#_0(&self) -> &r#T0 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_0,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_1(&self) -> &r#T1 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_1,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_2(&self) -> &r#T2 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_2,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_3(&self) -> &r#T3 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_3,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_4(&self) -> &r#T4 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_4,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_5(&self) -> &r#T5 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_5,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_6(&self) -> &r#T6 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_6,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_7(&self) -> &r#T7 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_7,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_8(&self) -> &r#T8 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_8,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_9(&self) -> &r#T9 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_9,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_10(&self) -> &r#T10 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_10,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_11(&self) -> &r#T11 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_11,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_12(&self) -> &r#T12 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_12,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_13(&self) -> &r#T13 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_13,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_14(&self) -> &r#T14 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_14,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_15(&self) -> &r#T15 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_15,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_16(&self) -> &r#T16 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_16,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_17(&self) -> &r#T17 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_17,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_18(&self) -> &r#T18 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_18,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}
pub fn r#_19(&self) -> &r#T19 {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => r#_19,
r#Tuple20::_PhantomVariant(..) => panic!(),
}
}

}
impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T19: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T19> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyErasable for r#Tuple20<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, r#T19, > {
type Erased = r#Tuple20<r#T0::Erased, r#T1::Erased, r#T2::Erased, r#T3::Erased, r#T4::Erased, r#T5::Erased, r#T6::Erased, r#T7::Erased, r#T8::Erased, r#T9::Erased, r#T10::Erased, r#T11::Erased, r#T12::Erased, r#T13::Erased, r#T14::Erased, r#T15::Erased, r#T16::Erased, r#T17::Erased, r#T18::Erased, r#T19::Erased, >;
}
impl <r#T0__Erased, r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T0__Erased> + 'static, r#T1__Erased, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T1__Erased> + 'static, r#T2__Erased, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T2__Erased> + 'static, r#T3__Erased, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T3__Erased> + 'static, r#T4__Erased, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T4__Erased> + 'static, r#T5__Erased, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T5__Erased> + 'static, r#T6__Erased, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T6__Erased> + 'static, r#T7__Erased, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T7__Erased> + 'static, r#T8__Erased, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T8__Erased> + 'static, r#T9__Erased, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T9__Erased> + 'static, r#T10__Erased, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T10__Erased> + 'static, r#T11__Erased, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T11__Erased> + 'static, r#T12__Erased, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T12__Erased> + 'static, r#T13__Erased, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T13__Erased> + 'static, r#T14__Erased, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T14__Erased> + 'static, r#T15__Erased, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T15__Erased> + 'static, r#T16__Erased, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T16__Erased> + 'static, r#T17__Erased, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T17__Erased> + 'static, r#T18__Erased, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T18__Erased> + 'static, r#T19__Erased, r#T19: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T19> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<r#T19__Erased> + 'static, > ::dafny_runtime::DafnyUnerasable<r#Tuple20<r#T0__Erased, r#T1__Erased, r#T2__Erased, r#T3__Erased, r#T4__Erased, r#T5__Erased, r#T6__Erased, r#T7__Erased, r#T8__Erased, r#T9__Erased, r#T10__Erased, r#T11__Erased, r#T12__Erased, r#T13__Erased, r#T14__Erased, r#T15__Erased, r#T16__Erased, r#T17__Erased, r#T18__Erased, r#T19__Erased, >> for r#Tuple20<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, r#T19, > {}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T19: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T19> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::dafny_runtime::DafnyPrint for r#Tuple20<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, r#T19, > {
fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
match self {
r#Tuple20::r#___hMake20 { r#_0, r#_1, r#_2, r#_3, r#_4, r#_5, r#_6, r#_7, r#_8, r#_9, r#_10, r#_11, r#_12, r#_13, r#_14, r#_15, r#_16, r#_17, r#_18, r#_19, } => {
write!(__fmt_print_formatter, "_System.Tuple20.___hMake20(")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_0, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_1, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_2, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_3, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_4, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_5, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_6, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_7, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_8, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_9, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_10, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_11, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_12, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_13, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_14, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_15, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_16, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_17, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_18, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ", ")?;
::dafny_runtime::DafnyPrint::fmt_print(r#_19, __fmt_print_formatter, false)?;
write!(__fmt_print_formatter, ")")?;
Ok(())
}
r#Tuple20::_PhantomVariant(..) => {panic!()
}
}
}
}

impl <r#T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T2: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T2> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T3: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T3> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T4: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T4> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T5: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T5> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T6: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T6> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T7: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T7> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T8: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T8> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T9: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T9> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T10: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T10> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T11: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T11> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T12: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T12> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T13: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T13> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T14: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T14> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T15: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T15> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T16: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T16> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T17: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T17> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T18: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T18> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, r#T19: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<r#T19> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, > ::std::default::Default for r#Tuple20<r#T0, r#T1, r#T2, r#T3, r#T4, r#T5, r#T6, r#T7, r#T8, r#T9, r#T10, r#T11, r#T12, r#T13, r#T14, r#T15, r#T16, r#T17, r#T18, r#T19, > {
fn default() -> Self {
r#Tuple20::r#___hMake20 {
r#_0: ::std::default::Default::default(),
r#_1: ::std::default::Default::default(),
r#_2: ::std::default::Default::default(),
r#_3: ::std::default::Default::default(),
r#_4: ::std::default::Default::default(),
r#_5: ::std::default::Default::default(),
r#_6: ::std::default::Default::default(),
r#_7: ::std::default::Default::default(),
r#_8: ::std::default::Default::default(),
r#_9: ::std::default::Default::default(),
r#_10: ::std::default::Default::default(),
r#_11: ::std::default::Default::default(),
r#_12: ::std::default::Default::default(),
r#_13: ::std::default::Default::default(),
r#_14: ::std::default::Default::default(),
r#_15: ::std::default::Default::default(),
r#_16: ::std::default::Default::default(),
r#_17: ::std::default::Default::default(),
r#_18: ::std::default::Default::default(),
r#_19: ::std::default::Default::default(),
}
}
}

}