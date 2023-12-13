// Package Std_BoundedInts
// Dafny module Std_BoundedInts compiled into Go

package Std_BoundedInts

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Std_Wrappers "Std_Wrappers"
  Std_Concurrent "Std_Concurrent"
  Std_FileIOInternalExterns "Std_FileIOInternalExterns"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
var _ Std_Concurrent.Dummy__
var _ = Std_FileIOInternalExterns.INTERNAL__ReadBytesFromFile

type Dummy__ struct{}


// Definition of class Default__
type Default__ struct {
  dummy byte
}

func New_Default___() *Default__ {
  _this := Default__{}

  return &_this
}

type CompanionStruct_Default___ struct {
}
var Companion_Default___ = CompanionStruct_Default___ {
}

func (_this *Default__) Equals(other *Default__) bool {
  return _this == other
}

func (_this *Default__) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*Default__)
  return ok && _this.Equals(other)
}

func (*Default__) String() string {
  return "Std_BoundedInts.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) TWO__TO__THE__8() _dafny.Int {
  return _dafny.IntOfInt64(256)
}
func (_static *CompanionStruct_Default___) UINT8__MAX() uint8 {
  return uint8(255)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__16() _dafny.Int {
  return _dafny.IntOfInt64(65536)
}
func (_static *CompanionStruct_Default___) UINT16__MAX() uint16 {
  return uint16(65535)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__32() _dafny.Int {
  return _dafny.IntOfInt64(4294967296)
}
func (_static *CompanionStruct_Default___) UINT32__MAX() uint32 {
  return uint32(4294967295)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__64() _dafny.Int {
  return _dafny.IntOfString("18446744073709551616")
}
func (_static *CompanionStruct_Default___) UINT64__MAX() uint64 {
  return uint64(18446744073709551615)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__7() _dafny.Int {
  return _dafny.IntOfInt64(128)
}
func (_static *CompanionStruct_Default___) INT8__MIN() int8 {
  return int8(-128)
}
func (_static *CompanionStruct_Default___) INT8__MAX() int8 {
  return int8(127)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__15() _dafny.Int {
  return _dafny.IntOfInt64(32768)
}
func (_static *CompanionStruct_Default___) INT16__MIN() int16 {
  return int16(-32768)
}
func (_static *CompanionStruct_Default___) INT16__MAX() int16 {
  return int16(32767)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__31() _dafny.Int {
  return _dafny.IntOfInt64(2147483648)
}
func (_static *CompanionStruct_Default___) INT32__MIN() int32 {
  return int32(-2147483648)
}
func (_static *CompanionStruct_Default___) INT32__MAX() int32 {
  return int32(2147483647)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__63() _dafny.Int {
  return _dafny.IntOfString("9223372036854775808")
}
func (_static *CompanionStruct_Default___) INT64__MIN() int64 {
  return int64(-9223372036854775808)
}
func (_static *CompanionStruct_Default___) INT64__MAX() int64 {
  return int64(9223372036854775807)
}
func (_static *CompanionStruct_Default___) NAT8__MAX() uint8 {
  return uint8(127)
}
func (_static *CompanionStruct_Default___) NAT16__MAX() uint16 {
  return uint16(32767)
}
func (_static *CompanionStruct_Default___) NAT32__MAX() uint32 {
  return uint32(2147483647)
}
func (_static *CompanionStruct_Default___) NAT64__MAX() uint64 {
  return uint64(9223372036854775807)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__128() _dafny.Int {
  return _dafny.IntOfString("340282366920938463463374607431768211456")
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__127() _dafny.Int {
  return _dafny.IntOfString("170141183460469231731687303715884105728")
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__0() _dafny.Int {
  return _dafny.One
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__1() _dafny.Int {
  return _dafny.IntOfInt64(2)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__2() _dafny.Int {
  return _dafny.IntOfInt64(4)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__4() _dafny.Int {
  return _dafny.IntOfInt64(16)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__5() _dafny.Int {
  return _dafny.IntOfInt64(32)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__24() _dafny.Int {
  return _dafny.IntOfInt64(16777216)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__40() _dafny.Int {
  return _dafny.IntOfInt64(1099511627776)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__48() _dafny.Int {
  return _dafny.IntOfInt64(281474976710656)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__56() _dafny.Int {
  return _dafny.IntOfInt64(72057594037927936)
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__256() _dafny.Int {
  return _dafny.IntOfString("115792089237316195423570985008687907853269984665640564039457584007913129639936")
}
func (_static *CompanionStruct_Default___) TWO__TO__THE__512() _dafny.Int {
  return _dafny.IntOfString("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096")
}
// End of class Default__

// Definition of class Uint8
type Uint8 struct {
}

func New_Uint8_() *Uint8 {
  _this := Uint8{}

  return &_this
}

type CompanionStruct_Uint8_ struct {
}
var Companion_Uint8_ = CompanionStruct_Uint8_ {
}

func (*Uint8) String() string {
  return "Std_BoundedInts.Uint8"
}
func (_this *Uint8) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Uint8{}

func (_this *CompanionStruct_Uint8_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint8(0), false }
    return next.(_dafny.Int).Uint8(), true
  }
}
// End of class Uint8

func Type_Uint8_() _dafny.TypeDescriptor {
  return type_Uint8_{}
}

type type_Uint8_ struct {
}

func (_this type_Uint8_) Default() interface{} {
  return uint8(0)
}

func (_this type_Uint8_) String() string {
  return "Std_BoundedInts.Uint8"
}

// Definition of class Uint16
type Uint16 struct {
}

func New_Uint16_() *Uint16 {
  _this := Uint16{}

  return &_this
}

type CompanionStruct_Uint16_ struct {
}
var Companion_Uint16_ = CompanionStruct_Uint16_ {
}

func (*Uint16) String() string {
  return "Std_BoundedInts.Uint16"
}
func (_this *Uint16) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Uint16{}

func (_this *CompanionStruct_Uint16_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint16(0), false }
    return next.(_dafny.Int).Uint16(), true
  }
}
// End of class Uint16

func Type_Uint16_() _dafny.TypeDescriptor {
  return type_Uint16_{}
}

type type_Uint16_ struct {
}

func (_this type_Uint16_) Default() interface{} {
  return uint16(0)
}

func (_this type_Uint16_) String() string {
  return "Std_BoundedInts.Uint16"
}

// Definition of class Uint32
type Uint32 struct {
}

func New_Uint32_() *Uint32 {
  _this := Uint32{}

  return &_this
}

type CompanionStruct_Uint32_ struct {
}
var Companion_Uint32_ = CompanionStruct_Uint32_ {
}

func (*Uint32) String() string {
  return "Std_BoundedInts.Uint32"
}
func (_this *Uint32) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Uint32{}

func (_this *CompanionStruct_Uint32_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint32(0), false }
    return next.(_dafny.Int).Uint32(), true
  }
}
// End of class Uint32

func Type_Uint32_() _dafny.TypeDescriptor {
  return type_Uint32_{}
}

type type_Uint32_ struct {
}

func (_this type_Uint32_) Default() interface{} {
  return uint32(0)
}

func (_this type_Uint32_) String() string {
  return "Std_BoundedInts.Uint32"
}

// Definition of class Uint64
type Uint64 struct {
}

func New_Uint64_() *Uint64 {
  _this := Uint64{}

  return &_this
}

type CompanionStruct_Uint64_ struct {
}
var Companion_Uint64_ = CompanionStruct_Uint64_ {
}

func (*Uint64) String() string {
  return "Std_BoundedInts.Uint64"
}
func (_this *Uint64) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Uint64{}

func (_this *CompanionStruct_Uint64_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint64(0), false }
    return next.(_dafny.Int).Uint64(), true
  }
}
// End of class Uint64

func Type_Uint64_() _dafny.TypeDescriptor {
  return type_Uint64_{}
}

type type_Uint64_ struct {
}

func (_this type_Uint64_) Default() interface{} {
  return uint64(0)
}

func (_this type_Uint64_) String() string {
  return "Std_BoundedInts.Uint64"
}

// Definition of class Uint128
type Uint128 struct {
}

func New_Uint128_() *Uint128 {
  _this := Uint128{}

  return &_this
}

type CompanionStruct_Uint128_ struct {
}
var Companion_Uint128_ = CompanionStruct_Uint128_ {
}

func (*Uint128) String() string {
  return "Std_BoundedInts.Uint128"
}
func (_this *Uint128) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Uint128{}

// End of class Uint128

func Type_Uint128_() _dafny.TypeDescriptor {
  return type_Uint128_{}
}

type type_Uint128_ struct {
}

func (_this type_Uint128_) Default() interface{} {
  return _dafny.Zero
}

func (_this type_Uint128_) String() string {
  return "Std_BoundedInts.Uint128"
}

// Definition of class Int8
type Int8 struct {
}

func New_Int8_() *Int8 {
  _this := Int8{}

  return &_this
}

type CompanionStruct_Int8_ struct {
}
var Companion_Int8_ = CompanionStruct_Int8_ {
}

func (*Int8) String() string {
  return "Std_BoundedInts.Int8"
}
func (_this *Int8) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Int8{}

func (_this *CompanionStruct_Int8_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return int8(0), false }
    return next.(_dafny.Int).Int8(), true
  }
}
// End of class Int8

func Type_Int8_() _dafny.TypeDescriptor {
  return type_Int8_{}
}

type type_Int8_ struct {
}

func (_this type_Int8_) Default() interface{} {
  return int8(0)
}

func (_this type_Int8_) String() string {
  return "Std_BoundedInts.Int8"
}

// Definition of class Int16
type Int16 struct {
}

func New_Int16_() *Int16 {
  _this := Int16{}

  return &_this
}

type CompanionStruct_Int16_ struct {
}
var Companion_Int16_ = CompanionStruct_Int16_ {
}

func (*Int16) String() string {
  return "Std_BoundedInts.Int16"
}
func (_this *Int16) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Int16{}

func (_this *CompanionStruct_Int16_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return int16(0), false }
    return next.(_dafny.Int).Int16(), true
  }
}
// End of class Int16

func Type_Int16_() _dafny.TypeDescriptor {
  return type_Int16_{}
}

type type_Int16_ struct {
}

func (_this type_Int16_) Default() interface{} {
  return int16(0)
}

func (_this type_Int16_) String() string {
  return "Std_BoundedInts.Int16"
}

// Definition of class Int32
type Int32 struct {
}

func New_Int32_() *Int32 {
  _this := Int32{}

  return &_this
}

type CompanionStruct_Int32_ struct {
}
var Companion_Int32_ = CompanionStruct_Int32_ {
}

func (*Int32) String() string {
  return "Std_BoundedInts.Int32"
}
func (_this *Int32) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Int32{}

func (_this *CompanionStruct_Int32_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return int32(0), false }
    return next.(_dafny.Int).Int32(), true
  }
}
// End of class Int32

func Type_Int32_() _dafny.TypeDescriptor {
  return type_Int32_{}
}

type type_Int32_ struct {
}

func (_this type_Int32_) Default() interface{} {
  return int32(0)
}

func (_this type_Int32_) String() string {
  return "Std_BoundedInts.Int32"
}

// Definition of class Int64
type Int64 struct {
}

func New_Int64_() *Int64 {
  _this := Int64{}

  return &_this
}

type CompanionStruct_Int64_ struct {
}
var Companion_Int64_ = CompanionStruct_Int64_ {
}

func (*Int64) String() string {
  return "Std_BoundedInts.Int64"
}
func (_this *Int64) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Int64{}

func (_this *CompanionStruct_Int64_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return int64(0), false }
    return next.(_dafny.Int).Int64(), true
  }
}
// End of class Int64

func Type_Int64_() _dafny.TypeDescriptor {
  return type_Int64_{}
}

type type_Int64_ struct {
}

func (_this type_Int64_) Default() interface{} {
  return int64(0)
}

func (_this type_Int64_) String() string {
  return "Std_BoundedInts.Int64"
}

// Definition of class Int128
type Int128 struct {
}

func New_Int128_() *Int128 {
  _this := Int128{}

  return &_this
}

type CompanionStruct_Int128_ struct {
}
var Companion_Int128_ = CompanionStruct_Int128_ {
}

func (*Int128) String() string {
  return "Std_BoundedInts.Int128"
}
func (_this *Int128) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Int128{}

// End of class Int128

func Type_Int128_() _dafny.TypeDescriptor {
  return type_Int128_{}
}

type type_Int128_ struct {
}

func (_this type_Int128_) Default() interface{} {
  return _dafny.Zero
}

func (_this type_Int128_) String() string {
  return "Std_BoundedInts.Int128"
}

// Definition of class Nat8
type Nat8 struct {
}

func New_Nat8_() *Nat8 {
  _this := Nat8{}

  return &_this
}

type CompanionStruct_Nat8_ struct {
}
var Companion_Nat8_ = CompanionStruct_Nat8_ {
}

func (*Nat8) String() string {
  return "Std_BoundedInts.Nat8"
}
func (_this *Nat8) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Nat8{}

func (_this *CompanionStruct_Nat8_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint8(0), false }
    return next.(_dafny.Int).Uint8(), true
  }
}
// End of class Nat8

func Type_Nat8_() _dafny.TypeDescriptor {
  return type_Nat8_{}
}

type type_Nat8_ struct {
}

func (_this type_Nat8_) Default() interface{} {
  return uint8(0)
}

func (_this type_Nat8_) String() string {
  return "Std_BoundedInts.Nat8"
}

// Definition of class Nat16
type Nat16 struct {
}

func New_Nat16_() *Nat16 {
  _this := Nat16{}

  return &_this
}

type CompanionStruct_Nat16_ struct {
}
var Companion_Nat16_ = CompanionStruct_Nat16_ {
}

func (*Nat16) String() string {
  return "Std_BoundedInts.Nat16"
}
func (_this *Nat16) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Nat16{}

func (_this *CompanionStruct_Nat16_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint16(0), false }
    return next.(_dafny.Int).Uint16(), true
  }
}
// End of class Nat16

func Type_Nat16_() _dafny.TypeDescriptor {
  return type_Nat16_{}
}

type type_Nat16_ struct {
}

func (_this type_Nat16_) Default() interface{} {
  return uint16(0)
}

func (_this type_Nat16_) String() string {
  return "Std_BoundedInts.Nat16"
}

// Definition of class Nat32
type Nat32 struct {
}

func New_Nat32_() *Nat32 {
  _this := Nat32{}

  return &_this
}

type CompanionStruct_Nat32_ struct {
}
var Companion_Nat32_ = CompanionStruct_Nat32_ {
}

func (*Nat32) String() string {
  return "Std_BoundedInts.Nat32"
}
func (_this *Nat32) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Nat32{}

func (_this *CompanionStruct_Nat32_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint32(0), false }
    return next.(_dafny.Int).Uint32(), true
  }
}
// End of class Nat32

func Type_Nat32_() _dafny.TypeDescriptor {
  return type_Nat32_{}
}

type type_Nat32_ struct {
}

func (_this type_Nat32_) Default() interface{} {
  return uint32(0)
}

func (_this type_Nat32_) String() string {
  return "Std_BoundedInts.Nat32"
}

// Definition of class Nat64
type Nat64 struct {
}

func New_Nat64_() *Nat64 {
  _this := Nat64{}

  return &_this
}

type CompanionStruct_Nat64_ struct {
}
var Companion_Nat64_ = CompanionStruct_Nat64_ {
}

func (*Nat64) String() string {
  return "Std_BoundedInts.Nat64"
}
func (_this *Nat64) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Nat64{}

func (_this *CompanionStruct_Nat64_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return uint64(0), false }
    return next.(_dafny.Int).Uint64(), true
  }
}
// End of class Nat64

func Type_Nat64_() _dafny.TypeDescriptor {
  return type_Nat64_{}
}

type type_Nat64_ struct {
}

func (_this type_Nat64_) Default() interface{} {
  return uint64(0)
}

func (_this type_Nat64_) String() string {
  return "Std_BoundedInts.Nat64"
}

// Definition of class Nat128
type Nat128 struct {
}

func New_Nat128_() *Nat128 {
  _this := Nat128{}

  return &_this
}

type CompanionStruct_Nat128_ struct {
}
var Companion_Nat128_ = CompanionStruct_Nat128_ {
}

func (*Nat128) String() string {
  return "Std_BoundedInts.Nat128"
}
func (_this *Nat128) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Nat128{}

// End of class Nat128

func Type_Nat128_() _dafny.TypeDescriptor {
  return type_Nat128_{}
}

type type_Nat128_ struct {
}

func (_this type_Nat128_) Default() interface{} {
  return _dafny.Zero
}

func (_this type_Nat128_) String() string {
  return "Std_BoundedInts.Nat128"
}

// Definition of class Opt__byte
type Opt__byte struct {
}

func New_Opt__byte_() *Opt__byte {
  _this := Opt__byte{}

  return &_this
}

type CompanionStruct_Opt__byte_ struct {
}
var Companion_Opt__byte_ = CompanionStruct_Opt__byte_ {
}

func (*Opt__byte) String() string {
  return "Std_BoundedInts.Opt__byte"
}
func (_this *Opt__byte) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Opt__byte{}

func (_this *CompanionStruct_Opt__byte_) IntegerRange(lo _dafny.Int, hi _dafny.Int) _dafny.Iterator {
  iter := _dafny.IntegerRange(lo, hi)
  return func() (interface{}, bool) {
    next, ok := iter()
    if !ok { return int16(0), false }
    return next.(_dafny.Int).Int16(), true
  }
}
// End of class Opt__byte

func Type_Opt__byte_() _dafny.TypeDescriptor {
  return type_Opt__byte_{}
}

type type_Opt__byte_ struct {
}

func (_this type_Opt__byte_) Default() interface{} {
  return int16(0)
}

func (_this type_Opt__byte_) String() string {
  return "Std_BoundedInts.Opt__byte"
}
