// Package Std_Collections_Array
// Dafny module Std_Collections_Array compiled into Go

package Std_Collections_Array

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
  return "Std_Collections_Array.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) BinarySearch(a _dafny.Array, key interface{}, less func (interface{}, interface{}) bool) Std_Wrappers.Option {
  var r Std_Wrappers.Option = Std_Wrappers.Companion_Option_.Default()
  _ = r
  var _96_lo _dafny.Int
  _ = _96_lo
  var _97_hi _dafny.Int
  _ = _97_hi
  var _rhs0 _dafny.Int = _dafny.Zero
  _ = _rhs0
  var _rhs1 _dafny.Int = _dafny.ArrayLen((a), 0)
  _ = _rhs1
  _96_lo = _rhs0
  _97_hi = _rhs1
  for (_96_lo).Cmp(_97_hi) < 0 {
    var _98_mid _dafny.Int
    _ = _98_mid
    _98_mid = ((_96_lo).Plus(_97_hi)).DivBy(_dafny.IntOfInt64(2))
    if ((less)(key, ((a)).ArrayGet1((_98_mid).Int()))) {
      _97_hi = _98_mid
    } else if ((less)(((a)).ArrayGet1((_98_mid).Int()), key)) {
      _96_lo = (_98_mid).Plus(_dafny.One)
    } else {
      r = Std_Wrappers.Companion_Option_.Create_Some_(_98_mid)
      return r
    }
  }
  r = Std_Wrappers.Companion_Option_.Create_None_()
  return r
  return r
}
// End of class Default__
