// Package Std_Math
// Dafny module Std_Math compiled into Go

package Std_Math

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Std_Wrappers "Std_Wrappers"
  Std_Concurrent "Std_Concurrent"
  Std_FileIOInternalExterns "Std_FileIOInternalExterns"
  Std_BoundedInts "Std_BoundedInts"
  Std_Base64 "Std_Base64"
  Std_Relations "Std_Relations"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
var _ Std_Concurrent.Dummy__
var _ = Std_FileIOInternalExterns.INTERNAL__ReadBytesFromFile
var _ Std_BoundedInts.Dummy__
var _ Std_Base64.Dummy__
var _ Std_Relations.Dummy__

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
  return "Std_Math.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Min(a _dafny.Int, b _dafny.Int) _dafny.Int {
  if ((a).Cmp(b) < 0) {
    return a
  } else {
    return b
  }
}
func (_static *CompanionStruct_Default___) Min3(a _dafny.Int, b _dafny.Int, c _dafny.Int) _dafny.Int {
  return Companion_Default___.Min(a, Companion_Default___.Min(b, c))
}
func (_static *CompanionStruct_Default___) Max(a _dafny.Int, b _dafny.Int) _dafny.Int {
  if ((a).Cmp(b) < 0) {
    return b
  } else {
    return a
  }
}
func (_static *CompanionStruct_Default___) Max3(a _dafny.Int, b _dafny.Int, c _dafny.Int) _dafny.Int {
  return Companion_Default___.Max(a, Companion_Default___.Max(b, c))
}
func (_static *CompanionStruct_Default___) Abs(a _dafny.Int) _dafny.Int {
  if ((a).Sign() == -1) {
    return (_dafny.Zero).Minus(a)
  } else {
    return a
  }
}
// End of class Default__
