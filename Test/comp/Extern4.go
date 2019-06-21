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

type Mixed struct{}
var Companion_Mixed_ = Mixed{}
// The Go compiler doesn't support Dafny methods in extern libraries
func (Mixed) M() {
  fmt.Print("Mixed.M\n")
}
func (Mixed) P() {
  fmt.Print("Mixed.P\n")
}

type AllExtern struct{}
var Companion_AllExtern_ = AllExtern{}
func (AllExtern) P() {
  fmt.Print("AllExtern.P\n")
}

