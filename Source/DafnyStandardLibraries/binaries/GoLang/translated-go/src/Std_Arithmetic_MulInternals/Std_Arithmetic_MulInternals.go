// Package Std_Arithmetic_MulInternals
// Dafny module Std_Arithmetic_MulInternals compiled into Go

package Std_Arithmetic_MulInternals

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Std_Wrappers "Std_Wrappers"
  Std_BoundedInts "Std_BoundedInts"
  Std_Base64 "Std_Base64"
  Std_Relations "Std_Relations"
  Std_Math "Std_Math"
  Std_Collections_Seq "Std_Collections_Seq"
  Std_Collections_Array "Std_Collections_Array"
  Std_Collections_Imap "Std_Collections_Imap"
  Std_Functions "Std_Functions"
  Std_Collections_Iset "Std_Collections_Iset"
  Std_Collections_Map "Std_Collections_Map"
  Std_Collections_Set "Std_Collections_Set"
  Std_Collections "Std_Collections"
  Std_DynamicArray "Std_DynamicArray"
  Std_FileIO "Std_FileIO"
  Std_Arithmetic_GeneralInternals "Std_Arithmetic_GeneralInternals"
  Std_Arithmetic_MulInternalsNonlinear "Std_Arithmetic_MulInternalsNonlinear"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
var _ Std_BoundedInts.Dummy__
var _ Std_Base64.Dummy__
var _ Std_Relations.Dummy__
var _ Std_Math.Dummy__
var _ Std_Collections_Seq.Dummy__
var _ Std_Collections_Array.Dummy__
var _ Std_Collections_Imap.Dummy__
var _ Std_Functions.Dummy__
var _ Std_Collections_Iset.Dummy__
var _ Std_Collections_Map.Dummy__
var _ Std_Collections_Set.Dummy__
var _ Std_Collections.Dummy__
var _ Std_DynamicArray.Dummy__
var _ Std_FileIO.Dummy__
var _ Std_Arithmetic_GeneralInternals.Dummy__
var _ Std_Arithmetic_MulInternalsNonlinear.Dummy__

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
  return "Std_Arithmetic_MulInternals.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) MulPos(x _dafny.Int, y _dafny.Int) _dafny.Int {
  var _120___accumulator _dafny.Int = _dafny.Zero
  _ = _120___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((x).Sign() == 0) {
    return (_dafny.Zero).Plus(_120___accumulator)
  } else {
    _120___accumulator = (_120___accumulator).Plus(y)
    var _in28 _dafny.Int = (x).Minus(_dafny.One)
    _ = _in28
    var _in29 _dafny.Int = y
    _ = _in29
    x = _in28
    y = _in29
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) MulRecursive(x _dafny.Int, y _dafny.Int) _dafny.Int {
  if ((x).Sign() != -1) {
    return Companion_Default___.MulPos(x, y)
  } else {
    return (_dafny.IntOfInt64(-1)).Times(Companion_Default___.MulPos((_dafny.IntOfInt64(-1)).Times(x), y))
  }
}
// End of class Default__
