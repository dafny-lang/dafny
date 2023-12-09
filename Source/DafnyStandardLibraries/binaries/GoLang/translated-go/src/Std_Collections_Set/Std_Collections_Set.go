// Package Std_Collections_Set
// Dafny module Std_Collections_Set compiled into Go

package Std_Collections_Set

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
  return "Std_Collections_Set.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) ExtractFromSingleton(s _dafny.Set) interface{} {
  return func (_let_dummy_0 int) interface{} {
    var _103_x interface{} = (interface{})(nil)
    _ = _103_x
    {
      for _iter5 := _dafny.Iterate((s).Elements());; {
        _assign_such_that_1, _ok5 := _iter5()
        if !_ok5 { break }
        _103_x = interface{}(_assign_such_that_1).(interface{})
        if ((s).Contains(_103_x)) {
          goto L_ASSIGN_SUCH_THAT_1
        }
      }
      panic("assign-such-that search produced no value (line 7299)")
      goto L_ASSIGN_SUCH_THAT_1;
    }
  L_ASSIGN_SUCH_THAT_1:
    return _103_x
  }(0)
}
func (_static *CompanionStruct_Default___) Map(f func (interface{}) interface{}, xs _dafny.Set) _dafny.Set {
  var _104_ys _dafny.Set = func () _dafny.Set {
    var _coll4 = _dafny.NewBuilder()
    _ = _coll4
    for _iter6 := _dafny.Iterate((xs).Elements());; {
      _compr_4, _ok6 := _iter6()
      if !_ok6 { break }
      var _105_x interface{}
      _105_x = interface{}(_compr_4).(interface{})
      if ((xs).Contains(_105_x)) {
        _coll4.Add((f)(_105_x))
      }
    }
    return _coll4.ToSet()
  }()
  _ = _104_ys
  return _104_ys
}
func (_static *CompanionStruct_Default___) Filter(f func (interface{}) bool, xs _dafny.Set) _dafny.Set {
  var _106_ys _dafny.Set = func () _dafny.Set {
    var _coll5 = _dafny.NewBuilder()
    _ = _coll5
    for _iter7 := _dafny.Iterate((xs).Elements());; {
      _compr_5, _ok7 := _iter7()
      if !_ok7 { break }
      var _107_x interface{}
      _107_x = interface{}(_compr_5).(interface{})
      if (((xs).Contains(_107_x)) && ((f)(_107_x))) {
        _coll5.Add(_107_x)
      }
    }
    return _coll5.ToSet()
  }()
  _ = _106_ys
  return _106_ys
}
func (_static *CompanionStruct_Default___) SetRange(a _dafny.Int, b _dafny.Int) _dafny.Set {
  var _108___accumulator _dafny.Set = _dafny.SetOf()
  _ = _108___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((a).Cmp(b) == 0) {
    return (_dafny.SetOf()).Union(_108___accumulator)
  } else {
    _108___accumulator = (_108___accumulator).Union(_dafny.SetOf(a))
    var _in26 _dafny.Int = (a).Plus(_dafny.One)
    _ = _in26
    var _in27 _dafny.Int = b
    _ = _in27
    a = _in26
    b = _in27
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) SetRangeZeroBound(n _dafny.Int) _dafny.Set {
  return Companion_Default___.SetRange(_dafny.Zero, n)
}
// End of class Default__
