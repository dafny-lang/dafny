// Package _System
// Dafny module _System compiled into Go

package _System

import (
  _dafny "dafny"
  os "os"
)
var _ _dafny.Dummy__
var _ = os.Args

type Dummy__ struct{}


// Definition of class Nat
type Nat struct {
}

func New_Nat_() *Nat {
  _this := Nat{}

  return &_this
}

type CompanionStruct_Nat_ struct {
}
var Companion_Nat_ = CompanionStruct_Nat_ {
}

func (*Nat) String() string {
  return "_System.Nat"
}
// End of class Nat

func Type_Nat_() _dafny.TypeDescriptor {
  return type_Nat_{}
}

type type_Nat_ struct {
}

func (_this type_Nat_) Default() interface{} {
  return _dafny.Zero
}

func (_this type_Nat_) String() string {
  return "_System.Nat"
}

// Definition of class HPartialFunc1___
type HPartialFunc1___ struct {
}

func New_HPartialFunc1____() *HPartialFunc1___ {
  _this := HPartialFunc1___{}

  return &_this
}

type CompanionStruct_HPartialFunc1____ struct {
}
var Companion_HPartialFunc1____ = CompanionStruct_HPartialFunc1____ {
}

func (*HPartialFunc1___) String() string {
  return "_System.HPartialFunc1___"
}
// End of class HPartialFunc1___

func Type_HPartialFunc1____(Type_T0_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc1____{Type_T0_, Type_R_}
}

type type_HPartialFunc1____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc1____) Default() interface{} {
  return (func (interface{}) interface{})(nil)
}

func (_this type_HPartialFunc1____) String() string {
  return "_System.HPartialFunc1___"
}

// Definition of class HTotalFunc1___
type HTotalFunc1___ struct {
}

func New_HTotalFunc1____() *HTotalFunc1___ {
  _this := HTotalFunc1___{}

  return &_this
}

type CompanionStruct_HTotalFunc1____ struct {
}
var Companion_HTotalFunc1____ = CompanionStruct_HTotalFunc1____ {
}

func (*HTotalFunc1___) String() string {
  return "_System.HTotalFunc1___"
}
// End of class HTotalFunc1___

func Type_HTotalFunc1____(Type_T0_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc1____{Type_T0_, Type_R_}
}

type type_HTotalFunc1____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc1____) Default() interface{} {
  return func (interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc1____) String() string {
  return "_System.HTotalFunc1___"
}

// Definition of class HPartialFunc0___
type HPartialFunc0___ struct {
}

func New_HPartialFunc0____() *HPartialFunc0___ {
  _this := HPartialFunc0___{}

  return &_this
}

type CompanionStruct_HPartialFunc0____ struct {
}
var Companion_HPartialFunc0____ = CompanionStruct_HPartialFunc0____ {
}

func (*HPartialFunc0___) String() string {
  return "_System.HPartialFunc0___"
}
// End of class HPartialFunc0___

func Type_HPartialFunc0____(Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc0____{Type_R_}
}

type type_HPartialFunc0____ struct {
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc0____) Default() interface{} {
  return (func () interface{})(nil)
}

func (_this type_HPartialFunc0____) String() string {
  return "_System.HPartialFunc0___"
}

// Definition of class HTotalFunc0___
type HTotalFunc0___ struct {
}

func New_HTotalFunc0____() *HTotalFunc0___ {
  _this := HTotalFunc0___{}

  return &_this
}

type CompanionStruct_HTotalFunc0____ struct {
}
var Companion_HTotalFunc0____ = CompanionStruct_HTotalFunc0____ {
}

func (*HTotalFunc0___) String() string {
  return "_System.HTotalFunc0___"
}
// End of class HTotalFunc0___

func Type_HTotalFunc0____(Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc0____{Type_R_}
}

type type_HTotalFunc0____ struct {
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc0____) Default() interface{} {
  return func () interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc0____) String() string {
  return "_System.HTotalFunc0___"
}


// Definition of class HPartialFunc2___
type HPartialFunc2___ struct {
}

func New_HPartialFunc2____() *HPartialFunc2___ {
  _this := HPartialFunc2___{}

  return &_this
}

type CompanionStruct_HPartialFunc2____ struct {
}
var Companion_HPartialFunc2____ = CompanionStruct_HPartialFunc2____ {
}

func (*HPartialFunc2___) String() string {
  return "_System.HPartialFunc2___"
}
// End of class HPartialFunc2___

func Type_HPartialFunc2____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc2____{Type_T0_, Type_T1_, Type_R_}
}

type type_HPartialFunc2____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc2____) Default() interface{} {
  return (func (interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc2____) String() string {
  return "_System.HPartialFunc2___"
}

// Definition of class HTotalFunc2___
type HTotalFunc2___ struct {
}

func New_HTotalFunc2____() *HTotalFunc2___ {
  _this := HTotalFunc2___{}

  return &_this
}

type CompanionStruct_HTotalFunc2____ struct {
}
var Companion_HTotalFunc2____ = CompanionStruct_HTotalFunc2____ {
}

func (*HTotalFunc2___) String() string {
  return "_System.HTotalFunc2___"
}
// End of class HTotalFunc2___

func Type_HTotalFunc2____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc2____{Type_T0_, Type_T1_, Type_R_}
}

type type_HTotalFunc2____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc2____) Default() interface{} {
  return func (interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc2____) String() string {
  return "_System.HTotalFunc2___"
}

// Definition of class HPartialFunc3___
type HPartialFunc3___ struct {
}

func New_HPartialFunc3____() *HPartialFunc3___ {
  _this := HPartialFunc3___{}

  return &_this
}

type CompanionStruct_HPartialFunc3____ struct {
}
var Companion_HPartialFunc3____ = CompanionStruct_HPartialFunc3____ {
}

func (*HPartialFunc3___) String() string {
  return "_System.HPartialFunc3___"
}
// End of class HPartialFunc3___

func Type_HPartialFunc3____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc3____{Type_T0_, Type_T1_, Type_T2_, Type_R_}
}

type type_HPartialFunc3____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc3____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc3____) String() string {
  return "_System.HPartialFunc3___"
}

// Definition of class HTotalFunc3___
type HTotalFunc3___ struct {
}

func New_HTotalFunc3____() *HTotalFunc3___ {
  _this := HTotalFunc3___{}

  return &_this
}

type CompanionStruct_HTotalFunc3____ struct {
}
var Companion_HTotalFunc3____ = CompanionStruct_HTotalFunc3____ {
}

func (*HTotalFunc3___) String() string {
  return "_System.HTotalFunc3___"
}
// End of class HTotalFunc3___

func Type_HTotalFunc3____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc3____{Type_T0_, Type_T1_, Type_T2_, Type_R_}
}

type type_HTotalFunc3____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc3____) Default() interface{} {
  return func (interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc3____) String() string {
  return "_System.HTotalFunc3___"
}

// Definition of class HPartialFunc4___
type HPartialFunc4___ struct {
}

func New_HPartialFunc4____() *HPartialFunc4___ {
  _this := HPartialFunc4___{}

  return &_this
}

type CompanionStruct_HPartialFunc4____ struct {
}
var Companion_HPartialFunc4____ = CompanionStruct_HPartialFunc4____ {
}

func (*HPartialFunc4___) String() string {
  return "_System.HPartialFunc4___"
}
// End of class HPartialFunc4___

func Type_HPartialFunc4____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc4____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_R_}
}

type type_HPartialFunc4____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc4____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc4____) String() string {
  return "_System.HPartialFunc4___"
}

// Definition of class HTotalFunc4___
type HTotalFunc4___ struct {
}

func New_HTotalFunc4____() *HTotalFunc4___ {
  _this := HTotalFunc4___{}

  return &_this
}

type CompanionStruct_HTotalFunc4____ struct {
}
var Companion_HTotalFunc4____ = CompanionStruct_HTotalFunc4____ {
}

func (*HTotalFunc4___) String() string {
  return "_System.HTotalFunc4___"
}
// End of class HTotalFunc4___

func Type_HTotalFunc4____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc4____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_R_}
}

type type_HTotalFunc4____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc4____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc4____) String() string {
  return "_System.HTotalFunc4___"
}

// Definition of class HPartialFunc5___
type HPartialFunc5___ struct {
}

func New_HPartialFunc5____() *HPartialFunc5___ {
  _this := HPartialFunc5___{}

  return &_this
}

type CompanionStruct_HPartialFunc5____ struct {
}
var Companion_HPartialFunc5____ = CompanionStruct_HPartialFunc5____ {
}

func (*HPartialFunc5___) String() string {
  return "_System.HPartialFunc5___"
}
// End of class HPartialFunc5___

func Type_HPartialFunc5____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc5____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_R_}
}

type type_HPartialFunc5____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc5____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc5____) String() string {
  return "_System.HPartialFunc5___"
}

// Definition of class HTotalFunc5___
type HTotalFunc5___ struct {
}

func New_HTotalFunc5____() *HTotalFunc5___ {
  _this := HTotalFunc5___{}

  return &_this
}

type CompanionStruct_HTotalFunc5____ struct {
}
var Companion_HTotalFunc5____ = CompanionStruct_HTotalFunc5____ {
}

func (*HTotalFunc5___) String() string {
  return "_System.HTotalFunc5___"
}
// End of class HTotalFunc5___

func Type_HTotalFunc5____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc5____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_R_}
}

type type_HTotalFunc5____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc5____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc5____) String() string {
  return "_System.HTotalFunc5___"
}

// Definition of class HPartialFunc6___
type HPartialFunc6___ struct {
}

func New_HPartialFunc6____() *HPartialFunc6___ {
  _this := HPartialFunc6___{}

  return &_this
}

type CompanionStruct_HPartialFunc6____ struct {
}
var Companion_HPartialFunc6____ = CompanionStruct_HPartialFunc6____ {
}

func (*HPartialFunc6___) String() string {
  return "_System.HPartialFunc6___"
}
// End of class HPartialFunc6___

func Type_HPartialFunc6____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc6____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_R_}
}

type type_HPartialFunc6____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc6____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc6____) String() string {
  return "_System.HPartialFunc6___"
}

// Definition of class HTotalFunc6___
type HTotalFunc6___ struct {
}

func New_HTotalFunc6____() *HTotalFunc6___ {
  _this := HTotalFunc6___{}

  return &_this
}

type CompanionStruct_HTotalFunc6____ struct {
}
var Companion_HTotalFunc6____ = CompanionStruct_HTotalFunc6____ {
}

func (*HTotalFunc6___) String() string {
  return "_System.HTotalFunc6___"
}
// End of class HTotalFunc6___

func Type_HTotalFunc6____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc6____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_R_}
}

type type_HTotalFunc6____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc6____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc6____) String() string {
  return "_System.HTotalFunc6___"
}

// Definition of class HPartialFunc7___
type HPartialFunc7___ struct {
}

func New_HPartialFunc7____() *HPartialFunc7___ {
  _this := HPartialFunc7___{}

  return &_this
}

type CompanionStruct_HPartialFunc7____ struct {
}
var Companion_HPartialFunc7____ = CompanionStruct_HPartialFunc7____ {
}

func (*HPartialFunc7___) String() string {
  return "_System.HPartialFunc7___"
}
// End of class HPartialFunc7___

func Type_HPartialFunc7____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc7____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_R_}
}

type type_HPartialFunc7____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc7____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc7____) String() string {
  return "_System.HPartialFunc7___"
}

// Definition of class HTotalFunc7___
type HTotalFunc7___ struct {
}

func New_HTotalFunc7____() *HTotalFunc7___ {
  _this := HTotalFunc7___{}

  return &_this
}

type CompanionStruct_HTotalFunc7____ struct {
}
var Companion_HTotalFunc7____ = CompanionStruct_HTotalFunc7____ {
}

func (*HTotalFunc7___) String() string {
  return "_System.HTotalFunc7___"
}
// End of class HTotalFunc7___

func Type_HTotalFunc7____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc7____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_R_}
}

type type_HTotalFunc7____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc7____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc7____) String() string {
  return "_System.HTotalFunc7___"
}

// Definition of class HPartialFunc8___
type HPartialFunc8___ struct {
}

func New_HPartialFunc8____() *HPartialFunc8___ {
  _this := HPartialFunc8___{}

  return &_this
}

type CompanionStruct_HPartialFunc8____ struct {
}
var Companion_HPartialFunc8____ = CompanionStruct_HPartialFunc8____ {
}

func (*HPartialFunc8___) String() string {
  return "_System.HPartialFunc8___"
}
// End of class HPartialFunc8___

func Type_HPartialFunc8____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc8____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_R_}
}

type type_HPartialFunc8____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc8____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc8____) String() string {
  return "_System.HPartialFunc8___"
}

// Definition of class HTotalFunc8___
type HTotalFunc8___ struct {
}

func New_HTotalFunc8____() *HTotalFunc8___ {
  _this := HTotalFunc8___{}

  return &_this
}

type CompanionStruct_HTotalFunc8____ struct {
}
var Companion_HTotalFunc8____ = CompanionStruct_HTotalFunc8____ {
}

func (*HTotalFunc8___) String() string {
  return "_System.HTotalFunc8___"
}
// End of class HTotalFunc8___

func Type_HTotalFunc8____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc8____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_R_}
}

type type_HTotalFunc8____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc8____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc8____) String() string {
  return "_System.HTotalFunc8___"
}

// Definition of class HPartialFunc9___
type HPartialFunc9___ struct {
}

func New_HPartialFunc9____() *HPartialFunc9___ {
  _this := HPartialFunc9___{}

  return &_this
}

type CompanionStruct_HPartialFunc9____ struct {
}
var Companion_HPartialFunc9____ = CompanionStruct_HPartialFunc9____ {
}

func (*HPartialFunc9___) String() string {
  return "_System.HPartialFunc9___"
}
// End of class HPartialFunc9___

func Type_HPartialFunc9____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc9____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_R_}
}

type type_HPartialFunc9____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc9____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc9____) String() string {
  return "_System.HPartialFunc9___"
}

// Definition of class HTotalFunc9___
type HTotalFunc9___ struct {
}

func New_HTotalFunc9____() *HTotalFunc9___ {
  _this := HTotalFunc9___{}

  return &_this
}

type CompanionStruct_HTotalFunc9____ struct {
}
var Companion_HTotalFunc9____ = CompanionStruct_HTotalFunc9____ {
}

func (*HTotalFunc9___) String() string {
  return "_System.HTotalFunc9___"
}
// End of class HTotalFunc9___

func Type_HTotalFunc9____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc9____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_R_}
}

type type_HTotalFunc9____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc9____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc9____) String() string {
  return "_System.HTotalFunc9___"
}

// Definition of class HPartialFunc10___
type HPartialFunc10___ struct {
}

func New_HPartialFunc10____() *HPartialFunc10___ {
  _this := HPartialFunc10___{}

  return &_this
}

type CompanionStruct_HPartialFunc10____ struct {
}
var Companion_HPartialFunc10____ = CompanionStruct_HPartialFunc10____ {
}

func (*HPartialFunc10___) String() string {
  return "_System.HPartialFunc10___"
}
// End of class HPartialFunc10___

func Type_HPartialFunc10____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc10____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_R_}
}

type type_HPartialFunc10____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc10____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc10____) String() string {
  return "_System.HPartialFunc10___"
}

// Definition of class HTotalFunc10___
type HTotalFunc10___ struct {
}

func New_HTotalFunc10____() *HTotalFunc10___ {
  _this := HTotalFunc10___{}

  return &_this
}

type CompanionStruct_HTotalFunc10____ struct {
}
var Companion_HTotalFunc10____ = CompanionStruct_HTotalFunc10____ {
}

func (*HTotalFunc10___) String() string {
  return "_System.HTotalFunc10___"
}
// End of class HTotalFunc10___

func Type_HTotalFunc10____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc10____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_R_}
}

type type_HTotalFunc10____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc10____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc10____) String() string {
  return "_System.HTotalFunc10___"
}

// Definition of class HPartialFunc11___
type HPartialFunc11___ struct {
}

func New_HPartialFunc11____() *HPartialFunc11___ {
  _this := HPartialFunc11___{}

  return &_this
}

type CompanionStruct_HPartialFunc11____ struct {
}
var Companion_HPartialFunc11____ = CompanionStruct_HPartialFunc11____ {
}

func (*HPartialFunc11___) String() string {
  return "_System.HPartialFunc11___"
}
// End of class HPartialFunc11___

func Type_HPartialFunc11____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc11____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_R_}
}

type type_HPartialFunc11____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc11____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc11____) String() string {
  return "_System.HPartialFunc11___"
}

// Definition of class HTotalFunc11___
type HTotalFunc11___ struct {
}

func New_HTotalFunc11____() *HTotalFunc11___ {
  _this := HTotalFunc11___{}

  return &_this
}

type CompanionStruct_HTotalFunc11____ struct {
}
var Companion_HTotalFunc11____ = CompanionStruct_HTotalFunc11____ {
}

func (*HTotalFunc11___) String() string {
  return "_System.HTotalFunc11___"
}
// End of class HTotalFunc11___

func Type_HTotalFunc11____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc11____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_R_}
}

type type_HTotalFunc11____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc11____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc11____) String() string {
  return "_System.HTotalFunc11___"
}

// Definition of class HPartialFunc12___
type HPartialFunc12___ struct {
}

func New_HPartialFunc12____() *HPartialFunc12___ {
  _this := HPartialFunc12___{}

  return &_this
}

type CompanionStruct_HPartialFunc12____ struct {
}
var Companion_HPartialFunc12____ = CompanionStruct_HPartialFunc12____ {
}

func (*HPartialFunc12___) String() string {
  return "_System.HPartialFunc12___"
}
// End of class HPartialFunc12___

func Type_HPartialFunc12____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc12____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_R_}
}

type type_HPartialFunc12____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc12____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc12____) String() string {
  return "_System.HPartialFunc12___"
}

// Definition of class HTotalFunc12___
type HTotalFunc12___ struct {
}

func New_HTotalFunc12____() *HTotalFunc12___ {
  _this := HTotalFunc12___{}

  return &_this
}

type CompanionStruct_HTotalFunc12____ struct {
}
var Companion_HTotalFunc12____ = CompanionStruct_HTotalFunc12____ {
}

func (*HTotalFunc12___) String() string {
  return "_System.HTotalFunc12___"
}
// End of class HTotalFunc12___

func Type_HTotalFunc12____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc12____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_R_}
}

type type_HTotalFunc12____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc12____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc12____) String() string {
  return "_System.HTotalFunc12___"
}

// Definition of class HPartialFunc13___
type HPartialFunc13___ struct {
}

func New_HPartialFunc13____() *HPartialFunc13___ {
  _this := HPartialFunc13___{}

  return &_this
}

type CompanionStruct_HPartialFunc13____ struct {
}
var Companion_HPartialFunc13____ = CompanionStruct_HPartialFunc13____ {
}

func (*HPartialFunc13___) String() string {
  return "_System.HPartialFunc13___"
}
// End of class HPartialFunc13___

func Type_HPartialFunc13____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc13____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_R_}
}

type type_HPartialFunc13____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc13____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc13____) String() string {
  return "_System.HPartialFunc13___"
}

// Definition of class HTotalFunc13___
type HTotalFunc13___ struct {
}

func New_HTotalFunc13____() *HTotalFunc13___ {
  _this := HTotalFunc13___{}

  return &_this
}

type CompanionStruct_HTotalFunc13____ struct {
}
var Companion_HTotalFunc13____ = CompanionStruct_HTotalFunc13____ {
}

func (*HTotalFunc13___) String() string {
  return "_System.HTotalFunc13___"
}
// End of class HTotalFunc13___

func Type_HTotalFunc13____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc13____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_R_}
}

type type_HTotalFunc13____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc13____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc13____) String() string {
  return "_System.HTotalFunc13___"
}

// Definition of class HPartialFunc14___
type HPartialFunc14___ struct {
}

func New_HPartialFunc14____() *HPartialFunc14___ {
  _this := HPartialFunc14___{}

  return &_this
}

type CompanionStruct_HPartialFunc14____ struct {
}
var Companion_HPartialFunc14____ = CompanionStruct_HPartialFunc14____ {
}

func (*HPartialFunc14___) String() string {
  return "_System.HPartialFunc14___"
}
// End of class HPartialFunc14___

func Type_HPartialFunc14____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc14____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_R_}
}

type type_HPartialFunc14____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc14____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc14____) String() string {
  return "_System.HPartialFunc14___"
}

// Definition of class HTotalFunc14___
type HTotalFunc14___ struct {
}

func New_HTotalFunc14____() *HTotalFunc14___ {
  _this := HTotalFunc14___{}

  return &_this
}

type CompanionStruct_HTotalFunc14____ struct {
}
var Companion_HTotalFunc14____ = CompanionStruct_HTotalFunc14____ {
}

func (*HTotalFunc14___) String() string {
  return "_System.HTotalFunc14___"
}
// End of class HTotalFunc14___

func Type_HTotalFunc14____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc14____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_R_}
}

type type_HTotalFunc14____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc14____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc14____) String() string {
  return "_System.HTotalFunc14___"
}

// Definition of class HPartialFunc15___
type HPartialFunc15___ struct {
}

func New_HPartialFunc15____() *HPartialFunc15___ {
  _this := HPartialFunc15___{}

  return &_this
}

type CompanionStruct_HPartialFunc15____ struct {
}
var Companion_HPartialFunc15____ = CompanionStruct_HPartialFunc15____ {
}

func (*HPartialFunc15___) String() string {
  return "_System.HPartialFunc15___"
}
// End of class HPartialFunc15___

func Type_HPartialFunc15____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc15____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_R_}
}

type type_HPartialFunc15____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc15____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc15____) String() string {
  return "_System.HPartialFunc15___"
}

// Definition of class HTotalFunc15___
type HTotalFunc15___ struct {
}

func New_HTotalFunc15____() *HTotalFunc15___ {
  _this := HTotalFunc15___{}

  return &_this
}

type CompanionStruct_HTotalFunc15____ struct {
}
var Companion_HTotalFunc15____ = CompanionStruct_HTotalFunc15____ {
}

func (*HTotalFunc15___) String() string {
  return "_System.HTotalFunc15___"
}
// End of class HTotalFunc15___

func Type_HTotalFunc15____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc15____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_R_}
}

type type_HTotalFunc15____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc15____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc15____) String() string {
  return "_System.HTotalFunc15___"
}

// Definition of class HPartialFunc16___
type HPartialFunc16___ struct {
}

func New_HPartialFunc16____() *HPartialFunc16___ {
  _this := HPartialFunc16___{}

  return &_this
}

type CompanionStruct_HPartialFunc16____ struct {
}
var Companion_HPartialFunc16____ = CompanionStruct_HPartialFunc16____ {
}

func (*HPartialFunc16___) String() string {
  return "_System.HPartialFunc16___"
}
// End of class HPartialFunc16___

func Type_HPartialFunc16____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc16____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_R_}
}

type type_HPartialFunc16____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc16____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc16____) String() string {
  return "_System.HPartialFunc16___"
}

// Definition of class HTotalFunc16___
type HTotalFunc16___ struct {
}

func New_HTotalFunc16____() *HTotalFunc16___ {
  _this := HTotalFunc16___{}

  return &_this
}

type CompanionStruct_HTotalFunc16____ struct {
}
var Companion_HTotalFunc16____ = CompanionStruct_HTotalFunc16____ {
}

func (*HTotalFunc16___) String() string {
  return "_System.HTotalFunc16___"
}
// End of class HTotalFunc16___

func Type_HTotalFunc16____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc16____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_R_}
}

type type_HTotalFunc16____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc16____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc16____) String() string {
  return "_System.HTotalFunc16___"
}

// Definition of class HPartialFunc17___
type HPartialFunc17___ struct {
}

func New_HPartialFunc17____() *HPartialFunc17___ {
  _this := HPartialFunc17___{}

  return &_this
}

type CompanionStruct_HPartialFunc17____ struct {
}
var Companion_HPartialFunc17____ = CompanionStruct_HPartialFunc17____ {
}

func (*HPartialFunc17___) String() string {
  return "_System.HPartialFunc17___"
}
// End of class HPartialFunc17___

func Type_HPartialFunc17____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc17____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_R_}
}

type type_HPartialFunc17____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc17____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc17____) String() string {
  return "_System.HPartialFunc17___"
}

// Definition of class HTotalFunc17___
type HTotalFunc17___ struct {
}

func New_HTotalFunc17____() *HTotalFunc17___ {
  _this := HTotalFunc17___{}

  return &_this
}

type CompanionStruct_HTotalFunc17____ struct {
}
var Companion_HTotalFunc17____ = CompanionStruct_HTotalFunc17____ {
}

func (*HTotalFunc17___) String() string {
  return "_System.HTotalFunc17___"
}
// End of class HTotalFunc17___

func Type_HTotalFunc17____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc17____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_R_}
}

type type_HTotalFunc17____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc17____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc17____) String() string {
  return "_System.HTotalFunc17___"
}

// Definition of class HPartialFunc18___
type HPartialFunc18___ struct {
}

func New_HPartialFunc18____() *HPartialFunc18___ {
  _this := HPartialFunc18___{}

  return &_this
}

type CompanionStruct_HPartialFunc18____ struct {
}
var Companion_HPartialFunc18____ = CompanionStruct_HPartialFunc18____ {
}

func (*HPartialFunc18___) String() string {
  return "_System.HPartialFunc18___"
}
// End of class HPartialFunc18___

func Type_HPartialFunc18____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_T17_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc18____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_T17_, Type_R_}
}

type type_HPartialFunc18____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_T17_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc18____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc18____) String() string {
  return "_System.HPartialFunc18___"
}

// Definition of class HTotalFunc18___
type HTotalFunc18___ struct {
}

func New_HTotalFunc18____() *HTotalFunc18___ {
  _this := HTotalFunc18___{}

  return &_this
}

type CompanionStruct_HTotalFunc18____ struct {
}
var Companion_HTotalFunc18____ = CompanionStruct_HTotalFunc18____ {
}

func (*HTotalFunc18___) String() string {
  return "_System.HTotalFunc18___"
}
// End of class HTotalFunc18___

func Type_HTotalFunc18____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_T17_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc18____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_T17_, Type_R_}
}

type type_HTotalFunc18____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_T17_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc18____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc18____) String() string {
  return "_System.HTotalFunc18___"
}

// Definition of class HPartialFunc19___
type HPartialFunc19___ struct {
}

func New_HPartialFunc19____() *HPartialFunc19___ {
  _this := HPartialFunc19___{}

  return &_this
}

type CompanionStruct_HPartialFunc19____ struct {
}
var Companion_HPartialFunc19____ = CompanionStruct_HPartialFunc19____ {
}

func (*HPartialFunc19___) String() string {
  return "_System.HPartialFunc19___"
}
// End of class HPartialFunc19___

func Type_HPartialFunc19____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_T17_ _dafny.TypeDescriptor, Type_T18_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc19____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_T17_, Type_T18_, Type_R_}
}

type type_HPartialFunc19____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_T17_ _dafny.TypeDescriptor
  Type_T18_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc19____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc19____) String() string {
  return "_System.HPartialFunc19___"
}

// Definition of class HTotalFunc19___
type HTotalFunc19___ struct {
}

func New_HTotalFunc19____() *HTotalFunc19___ {
  _this := HTotalFunc19___{}

  return &_this
}

type CompanionStruct_HTotalFunc19____ struct {
}
var Companion_HTotalFunc19____ = CompanionStruct_HTotalFunc19____ {
}

func (*HTotalFunc19___) String() string {
  return "_System.HTotalFunc19___"
}
// End of class HTotalFunc19___

func Type_HTotalFunc19____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_T17_ _dafny.TypeDescriptor, Type_T18_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc19____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_T17_, Type_T18_, Type_R_}
}

type type_HTotalFunc19____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_T17_ _dafny.TypeDescriptor
  Type_T18_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc19____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc19____) String() string {
  return "_System.HTotalFunc19___"
}

// Definition of class HPartialFunc20___
type HPartialFunc20___ struct {
}

func New_HPartialFunc20____() *HPartialFunc20___ {
  _this := HPartialFunc20___{}

  return &_this
}

type CompanionStruct_HPartialFunc20____ struct {
}
var Companion_HPartialFunc20____ = CompanionStruct_HPartialFunc20____ {
}

func (*HPartialFunc20___) String() string {
  return "_System.HPartialFunc20___"
}
// End of class HPartialFunc20___

func Type_HPartialFunc20____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_T17_ _dafny.TypeDescriptor, Type_T18_ _dafny.TypeDescriptor, Type_T19_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HPartialFunc20____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_T17_, Type_T18_, Type_T19_, Type_R_}
}

type type_HPartialFunc20____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_T17_ _dafny.TypeDescriptor
  Type_T18_ _dafny.TypeDescriptor
  Type_T19_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HPartialFunc20____) Default() interface{} {
  return (func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{})(nil)
}

func (_this type_HPartialFunc20____) String() string {
  return "_System.HPartialFunc20___"
}

// Definition of class HTotalFunc20___
type HTotalFunc20___ struct {
}

func New_HTotalFunc20____() *HTotalFunc20___ {
  _this := HTotalFunc20___{}

  return &_this
}

type CompanionStruct_HTotalFunc20____ struct {
}
var Companion_HTotalFunc20____ = CompanionStruct_HTotalFunc20____ {
}

func (*HTotalFunc20___) String() string {
  return "_System.HTotalFunc20___"
}
// End of class HTotalFunc20___

func Type_HTotalFunc20____(Type_T0_ _dafny.TypeDescriptor, Type_T1_ _dafny.TypeDescriptor, Type_T2_ _dafny.TypeDescriptor, Type_T3_ _dafny.TypeDescriptor, Type_T4_ _dafny.TypeDescriptor, Type_T5_ _dafny.TypeDescriptor, Type_T6_ _dafny.TypeDescriptor, Type_T7_ _dafny.TypeDescriptor, Type_T8_ _dafny.TypeDescriptor, Type_T9_ _dafny.TypeDescriptor, Type_T10_ _dafny.TypeDescriptor, Type_T11_ _dafny.TypeDescriptor, Type_T12_ _dafny.TypeDescriptor, Type_T13_ _dafny.TypeDescriptor, Type_T14_ _dafny.TypeDescriptor, Type_T15_ _dafny.TypeDescriptor, Type_T16_ _dafny.TypeDescriptor, Type_T17_ _dafny.TypeDescriptor, Type_T18_ _dafny.TypeDescriptor, Type_T19_ _dafny.TypeDescriptor, Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_HTotalFunc20____{Type_T0_, Type_T1_, Type_T2_, Type_T3_, Type_T4_, Type_T5_, Type_T6_, Type_T7_, Type_T8_, Type_T9_, Type_T10_, Type_T11_, Type_T12_, Type_T13_, Type_T14_, Type_T15_, Type_T16_, Type_T17_, Type_T18_, Type_T19_, Type_R_}
}

type type_HTotalFunc20____ struct {
  Type_T0_ _dafny.TypeDescriptor
  Type_T1_ _dafny.TypeDescriptor
  Type_T2_ _dafny.TypeDescriptor
  Type_T3_ _dafny.TypeDescriptor
  Type_T4_ _dafny.TypeDescriptor
  Type_T5_ _dafny.TypeDescriptor
  Type_T6_ _dafny.TypeDescriptor
  Type_T7_ _dafny.TypeDescriptor
  Type_T8_ _dafny.TypeDescriptor
  Type_T9_ _dafny.TypeDescriptor
  Type_T10_ _dafny.TypeDescriptor
  Type_T11_ _dafny.TypeDescriptor
  Type_T12_ _dafny.TypeDescriptor
  Type_T13_ _dafny.TypeDescriptor
  Type_T14_ _dafny.TypeDescriptor
  Type_T15_ _dafny.TypeDescriptor
  Type_T16_ _dafny.TypeDescriptor
  Type_T17_ _dafny.TypeDescriptor
  Type_T18_ _dafny.TypeDescriptor
  Type_T19_ _dafny.TypeDescriptor
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_HTotalFunc20____) Default() interface{} {
  return func (interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}, interface{}) interface{} { return Type_R_.Default(); }
}

func (_this type_HTotalFunc20____) String() string {
  return "_System.HTotalFunc20___"
}
