package Library

import (
  "dafny"
  "fmt"
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

type Dummy__ struct{}


// The Go compiler doesn't support Dafny methods in extern libraries
type AllDafny struct{}
var Companion_AllDafny_ = AllDafny{}
func (AllDafny) M() {
  fmt.Print("AllDafny.M\n")
}

type Mixed struct{ n dafny.Int }
type CompanionStruct_Mixed_ struct{}
var Companion_Mixed_ = CompanionStruct_Mixed_{}
func New_Mixed_(n dafny.Int) *Mixed {
  return &Mixed{n}
}
// The Go compiler doesn't support Dafny methods in extern libraries
func (CompanionStruct_Mixed_) M() {
  fmt.Print("Extern static code says: ")
  Companion_Mixed_.P()
}
func (CompanionStruct_Mixed_) P() {
  fmt.Print("Mixed.P\n")
}
func (m *Mixed) IM() {
  fmt.Print("Extern instance code says: ")
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
  return m.n
}

type AllExtern struct{}
var Companion_AllExtern_ = AllExtern{}
func (AllExtern) P() {
  fmt.Print("AllExtern.P\n")
}
