// Package Std_Collections_Set
// Dafny module Std_Collections_Set compiled into Go

package Std_Collections_Set

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
var _ Std_Concurrent.Dummy__
var _ Std_FileIOInternalExterns.Dummy__
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
    var _113_x interface{} = (interface{})(nil)
    _ = _113_x
    {
      for _iter5 := _dafny.Iterate((s).Elements());; {
        _assign_such_that_1, _ok5 := _iter5()
        if !_ok5 { break }
        _113_x = interface{}(_assign_such_that_1).(interface{})
        if ((s).Contains(_113_x)) {
          goto L_ASSIGN_SUCH_THAT_1
        }
      }
      panic("assign-such-that search produced no value (line 7408)")
      goto L_ASSIGN_SUCH_THAT_1;
    }
  L_ASSIGN_SUCH_THAT_1:
    return _113_x
  }(0)
}
func (_static *CompanionStruct_Default___) Map(f func (interface{}) interface{}, xs _dafny.Set) _dafny.Set {
  var _114_ys _dafny.Set = func () _dafny.Set {
    var _coll4 = _dafny.NewBuilder()
    _ = _coll4
    for _iter6 := _dafny.Iterate((xs).Elements());; {
      _compr_4, _ok6 := _iter6()
      if !_ok6 { break }
      var _115_x interface{}
      _115_x = interface{}(_compr_4).(interface{})
      if ((xs).Contains(_115_x)) {
        _coll4.Add((f)(_115_x))
      }
    }
    return _coll4.ToSet()
  }()
  _ = _114_ys
  return _114_ys
}
func (_static *CompanionStruct_Default___) Filter(f func (interface{}) bool, xs _dafny.Set) _dafny.Set {
  var _116_ys _dafny.Set = func () _dafny.Set {
    var _coll5 = _dafny.NewBuilder()
    _ = _coll5
    for _iter7 := _dafny.Iterate((xs).Elements());; {
      _compr_5, _ok7 := _iter7()
      if !_ok7 { break }
      var _117_x interface{}
      _117_x = interface{}(_compr_5).(interface{})
      if (((xs).Contains(_117_x)) && ((f)(_117_x))) {
        _coll5.Add(_117_x)
      }
    }
    return _coll5.ToSet()
  }()
  _ = _116_ys
  return _116_ys
}
func (_static *CompanionStruct_Default___) SetRange(a _dafny.Int, b _dafny.Int) _dafny.Set {
  var _118___accumulator _dafny.Set = _dafny.SetOf()
  _ = _118___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((a).Cmp(b) == 0) {
    return (_dafny.SetOf()).Union(_118___accumulator)
  } else {
    _118___accumulator = (_118___accumulator).Union(_dafny.SetOf(a))
    var _in30 _dafny.Int = (a).Plus(_dafny.One)
    _ = _in30
    var _in31 _dafny.Int = b
    _ = _in31
    a = _in30
    b = _in31
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) SetRangeZeroBound(n _dafny.Int) _dafny.Set {
  return Companion_Default___.SetRange(_dafny.Zero, n)
}
// End of class Default__
