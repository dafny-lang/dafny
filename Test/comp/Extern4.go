package Library

import (
  "dafny"
  "fmt"
  Wrappers "Wrappers_Compile"
)

type CompanionStruct_LibClass_ struct{}

var Companion_LibClass_ = CompanionStruct_LibClass_{}

func (CompanionStruct_LibClass_) CallMeInt(x dafny.Int) (y, z dafny.Int) {
  y = x.Plus(dafny.One)
  z = y.Plus(y)
  return
}

func (CompanionStruct_LibClass_) CallMeNative(x int32, b bool) int32 {
  var y int32
  if b {
    y = x + 1
  } else {
    y = x - 1
  }
  return y
}

type CompanionStruct_OtherClass_ struct{}

var OtherClass = CompanionStruct_OtherClass_{}

func (CompanionStruct_OtherClass_) CallMe() interface{} {
  return "OtherClass.CallMe"
}

type Dummy__ struct{}


// The Go compiler doesn't support Dafny methods in extern libraries
type AllDafny struct{}
var Companion_AllDafny_ = AllDafny{}
func (AllDafny) M() {
  fmt.Print("AllDafny.M\n")
}

type Mixed struct{}
type CompanionStruct_Mixed_ struct{}
var Companion_Mixed_ = CompanionStruct_Mixed_{}

func New_Mixed_() *Mixed {
  return &Mixed{}
}

func (m *Mixed) Ctor__() { }

// The Go compiler doesn't support Dafny methods in extern libraries
func (CompanionStruct_Mixed_) M() {
  fmt.Print("Extern static method says: ")
  Companion_Mixed_.P()
}
func (CompanionStruct_Mixed_) P() {
  fmt.Print("Mixed.P\n")
}
func (m *Mixed) IM() {
  fmt.Print("Extern instance method says: ")
  m.IP()
}
func (*Mixed) IP() {
  fmt.Print("Mixed.IP\n")
}
func (CompanionStruct_Mixed_) F() dafny.Int {
  return dafny.IntOf(1000).Plus(Companion_Mixed_.G())
}
func (CompanionStruct_Mixed_) G() dafny.Int {
  return dafny.One
}
func (m *Mixed) IF() dafny.Int {
  return dafny.IntOf(2000).Plus(m.IG())
}
func (m *Mixed) IG() dafny.Int {
  return dafny.IntOf(2)
}

type AllExtern struct{}
var Companion_AllExtern_ = AllExtern{}
func (AllExtern) P() {
  fmt.Print("AllExtern.P\n")
}
func (AllExtern) MaybeInt() Wrappers.Option {
  return Wrappers.Companion_Option_.Create_Some_(42)
}
func (AllExtern) IntPair() Wrappers.Pair {
  return Wrappers.Companion_Pair_.Create_Pair_(3, 7)

type SingletonOptimization struct{}
var Companion_SingletonOptimization_ = SingletonOptimization{}
func (SingletonOptimization) SingletonTuple(a int32) int32 {
  return a + 1
}
func (SingletonOptimization) NoWrapper(a int32) int32 {
  return a + 1
}
func (SingletonOptimization) GhostWrapper(a int32) int32 {
  return a + 1
}
