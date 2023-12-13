// Package Std_FileIO
// Dafny module Std_FileIO compiled into Go

package Std_FileIO

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
  Std_Collections_Set "Std_Collections_Set"
  Std_Collections "Std_Collections"
  Std_DynamicArray "Std_DynamicArray"
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
var _ Std_Collections_Map.Dummy__
var _ Std_Collections_Set.Dummy__
var _ Std_Collections.Dummy__
var _ Std_DynamicArray.Dummy__

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
  return "Std_FileIO.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) ReadBytesFromFile(path _dafny.Sequence) Std_Wrappers.Result {
  var res Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(_dafny.EmptySeq)
  _ = res
  var _125_isError bool
  _ = _125_isError
  var _126_bytesRead _dafny.Sequence
  _ = _126_bytesRead
  var _127_errorMsg _dafny.Sequence
  _ = _127_errorMsg
  var _out1 bool
  _ = _out1
  var _out2 _dafny.Sequence
  _ = _out2
  var _out3 _dafny.Sequence
  _ = _out3
  _out1, _out2, _out3 = Std_FileIOInternalExterns.Companion_Default___.INTERNAL__ReadBytesFromFile(path)
  _125_isError = _out1
  _126_bytesRead = _out2
  _127_errorMsg = _out3
  res = (func () Std_Wrappers.Result { if _125_isError { return Std_Wrappers.Companion_Result_.Create_Failure_(_127_errorMsg) }; return Std_Wrappers.Companion_Result_.Create_Success_(_126_bytesRead) })() 
  return res
  return res
}
func (_static *CompanionStruct_Default___) WriteBytesToFile(path _dafny.Sequence, bytes _dafny.Sequence) Std_Wrappers.Result {
  var res Std_Wrappers.Result = Std_Wrappers.Companion_Result_.Default(_dafny.TupleOf())
  _ = res
  var _128_isError bool
  _ = _128_isError
  var _129_errorMsg _dafny.Sequence
  _ = _129_errorMsg
  var _out4 bool
  _ = _out4
  var _out5 _dafny.Sequence
  _ = _out5
  _out4, _out5 = Std_FileIOInternalExterns.Companion_Default___.INTERNAL__WriteBytesToFile(path, bytes)
  _128_isError = _out4
  _129_errorMsg = _out5
  res = (func () Std_Wrappers.Result { if _128_isError { return Std_Wrappers.Companion_Result_.Create_Failure_(_129_errorMsg) }; return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.TupleOf()) })() 
  return res
  return res
}
// End of class Default__
