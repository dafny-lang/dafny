package Interop

import (dafny "dafny"; math "math"; rand "math/rand"
  wrappers "Std_Wrappers")

type Dummy__ struct{}

type CompanionStruct_Default___ struct {
}
var Companion_Default___ = CompanionStruct_Default___ {
}

func (_static *CompanionStruct_Default___) Int32ToInt(x int32) (r dafny.Int) {
  r = dafny.IntOfInt32(x)
  return
}

func (_static *CompanionStruct_Default___) Int31n(x int32) (r int32) {
  r = rand.Int31n(x)
  return
}

func (_static *CompanionStruct_Default___) MaxInt32() (r int32) {
  r = math.MaxInt32
  return
}

func (_static *CompanionStruct_Default___) IntToInt32(value dafny.Int) (r wrappers.Option) {  
  if value.Cmp(dafny.IntOfInt32(math.MaxInt32)) == 1 || value.Cmp(dafny.IntOfInt32(math.MinInt32)) == -1 {
    r = wrappers.Companion_Option_.Create_None_()
  } else
  {
    r = wrappers.Companion_Option_.Create_Some_(value.Int32())
  }
  return
}