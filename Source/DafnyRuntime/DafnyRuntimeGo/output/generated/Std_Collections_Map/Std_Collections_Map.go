// Package Std_Collections_Map
// Dafny module Std_Collections_Map compiled into Go

package Std_Collections_Map

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
var _ Std_Math.Dummy__
var _ Std_Collections_Seq.Dummy__
var _ Std_Collections_Array.Dummy__
var _ Std_Collections_Imap.Dummy__
var _ Std_Functions.Dummy__
var _ Std_Collections_Iset.Dummy__

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
  return "Std_Collections_Map.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Get(m _dafny.Map, x interface{}) Std_Wrappers.Option {
  if ((m).Contains(x)) {
    return Std_Wrappers.Companion_Option_.Create_Some_((m).Get(x).(interface{}))
  } else {
    return Std_Wrappers.Companion_Option_.Create_None_()
  }
}
func (_static *CompanionStruct_Default___) ToImap(m _dafny.Map) _dafny.Map {
  return func () _dafny.Map {
    var _coll1 = _dafny.NewMapBuilder()
    _ = _coll1
    for _iter2 := _dafny.Iterate((m).Keys().Elements());; {
      _compr_1, _ok2 := _iter2()
      if !_ok2 { break }
      var _109_x interface{}
      _109_x = interface{}(_compr_1).(interface{})
      if ((m).Contains(_109_x)) {
        _coll1.Add(_109_x,(m).Get(_109_x).(interface{}))
      }
    }
    return _coll1.ToMap()
  }()
}
func (_static *CompanionStruct_Default___) RemoveKeys(m _dafny.Map, xs _dafny.Set) _dafny.Map {
  return (m).Subtract(xs)
}
func (_static *CompanionStruct_Default___) Remove(m _dafny.Map, x interface{}) _dafny.Map {
  var _110_m_k _dafny.Map = func () _dafny.Map {
    var _coll2 = _dafny.NewMapBuilder()
    _ = _coll2
    for _iter3 := _dafny.Iterate((m).Keys().Elements());; {
      _compr_2, _ok3 := _iter3()
      if !_ok3 { break }
      var _111_x_k interface{}
      _111_x_k = interface{}(_compr_2).(interface{})
      if (((m).Contains(_111_x_k)) && (!_dafny.AreEqual(_111_x_k, x))) {
        _coll2.Add(_111_x_k,(m).Get(_111_x_k).(interface{}))
      }
    }
    return _coll2.ToMap()
  }()
  _ = _110_m_k
  return _110_m_k
}
func (_static *CompanionStruct_Default___) Restrict(m _dafny.Map, xs _dafny.Set) _dafny.Map {
  return func () _dafny.Map {
    var _coll3 = _dafny.NewMapBuilder()
    _ = _coll3
    for _iter4 := _dafny.Iterate((xs).Elements());; {
      _compr_3, _ok4 := _iter4()
      if !_ok4 { break }
      var _112_x interface{}
      _112_x = interface{}(_compr_3).(interface{})
      if (((xs).Contains(_112_x)) && ((m).Contains(_112_x))) {
        _coll3.Add(_112_x,(m).Get(_112_x).(interface{}))
      }
    }
    return _coll3.ToMap()
  }()
}
func (_static *CompanionStruct_Default___) Union(m _dafny.Map, m_k _dafny.Map) _dafny.Map {
  return (m).Merge(m_k)
}
// End of class Default__
