// Package Std_Collections_Seq
// Dafny module Std_Collections_Seq compiled into Go

package Std_Collections_Seq

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
  return "Std_Collections_Seq.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) First(xs _dafny.Sequence) interface{} {
  return (xs).Select(0).(interface{})
}
func (_static *CompanionStruct_Default___) DropFirst(xs _dafny.Sequence) _dafny.Sequence {
  return (xs).Drop(1)
}
func (_static *CompanionStruct_Default___) Last(xs _dafny.Sequence) interface{} {
  return (xs).Select(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32()).(interface{})
}
func (_static *CompanionStruct_Default___) DropLast(xs _dafny.Sequence) _dafny.Sequence {
  return (xs).Take(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32())
}
func (_static *CompanionStruct_Default___) ToArray(xs _dafny.Sequence) _dafny.Array {
  var a _dafny.Array = _dafny.NewArrayWithValue(nil, _dafny.IntOf(0))
  _ = a
  var _len0_2 _dafny.Int = _dafny.IntOfUint32((xs).Cardinality())
  _ = _len0_2
  var _nw2 _dafny.Array
  _ = _nw2
  if (_len0_2.Cmp(_dafny.Zero) == 0) {
    _nw2 = _dafny.NewArray(_len0_2)
  } else {
    var _init2 func (_dafny.Int) interface{} = (func (_69_xs _dafny.Sequence) func (_dafny.Int) interface{} {
      return func (_70_i _dafny.Int) interface{} {
        return (_69_xs).Select((_70_i).Uint32()).(interface{})
      }
    })(xs)
    _ = _init2
    var _element0_2 = _init2(_dafny.Zero)
    _ = _element0_2
    _nw2 = _dafny.NewArrayFromExample(_element0_2, nil, _len0_2)
    (_nw2).ArraySet1(_element0_2, 0)
    var _nativeLen0_2 = (_len0_2).Int()
    _ = _nativeLen0_2
    for _i0_2 := 1; _i0_2 < _nativeLen0_2; _i0_2++ {
      (_nw2).ArraySet1(_init2(_dafny.IntOf(_i0_2)), _i0_2)
    }
  }
  a = _nw2
  return a
}
func (_static *CompanionStruct_Default___) ToSet(xs _dafny.Sequence) _dafny.Set {
  return func () _dafny.Set {
    var _coll0 = _dafny.NewBuilder()
    _ = _coll0
    for _iter0 := _dafny.Iterate((xs).Elements());; {
      _compr_0, _ok0 := _iter0()
      if !_ok0 { break }
      var _71_x interface{}
      _71_x = interface{}(_compr_0).(interface{})
      if (_dafny.Companion_Sequence_.Contains(xs, _71_x)) {
        _coll0.Add(_71_x)
      }
    }
    return _coll0.ToSet()
  }()
}
func (_static *CompanionStruct_Default___) IndexOf(xs _dafny.Sequence, v interface{}) _dafny.Int {
  var _72___accumulator _dafny.Int = _dafny.Zero
  _ = _72___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (_dafny.AreEqual((xs).Select(0).(interface{}), v)) {
    return (_dafny.Zero).Plus(_72___accumulator)
  } else {
    _72___accumulator = (_72___accumulator).Plus(_dafny.One)
    var _in0 _dafny.Sequence = (xs).Drop(1)
    _ = _in0
    var _in1 interface{} = v
    _ = _in1
    xs = _in0
    v = _in1
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) IndexOfOption(xs _dafny.Sequence, v interface{}) Std_Wrappers.Option {
  return Companion_Default___.IndexByOption(xs, func (coer4 func (interface{}) bool) func (interface{}) bool {
    return func (arg4 interface{}) bool {
      return coer4(arg4)
    }
  }((func (_73_v interface{}) func (interface{}) bool {
    return func (_74_x interface{}) bool {
      return _dafny.AreEqual(_74_x, _73_v)
    }
  })(v)))
}
func (_static *CompanionStruct_Default___) IndexByOption(xs _dafny.Sequence, p func (interface{}) bool) Std_Wrappers.Option {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return Std_Wrappers.Companion_Option_.Create_None_()
  } else if ((p)((xs).Select(0).(interface{}))) {
    return Std_Wrappers.Companion_Option_.Create_Some_(_dafny.Zero)
  } else {
    var _75_o_k Std_Wrappers.Option = Companion_Default___.IndexByOption((xs).Drop(1), p)
    _ = _75_o_k
    if ((_75_o_k).Is_Some()) {
      return Std_Wrappers.Companion_Option_.Create_Some_(((_75_o_k).Dtor_value().(_dafny.Int)).Plus(_dafny.One))
    } else {
      return Std_Wrappers.Companion_Option_.Create_None_()
    }
  }
}
func (_static *CompanionStruct_Default___) LastIndexOf(xs _dafny.Sequence, v interface{}) _dafny.Int {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (_dafny.AreEqual((xs).Select(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32()).(interface{}), v)) {
    return (_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)
  } else {
    var _in2 _dafny.Sequence = (xs).Take(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32())
    _ = _in2
    var _in3 interface{} = v
    _ = _in3
    xs = _in2
    v = _in3
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) LastIndexOfOption(xs _dafny.Sequence, v interface{}) Std_Wrappers.Option {
  return Companion_Default___.LastIndexByOption(xs, func (coer5 func (interface{}) bool) func (interface{}) bool {
    return func (arg5 interface{}) bool {
      return coer5(arg5)
    }
  }((func (_76_v interface{}) func (interface{}) bool {
    return func (_77_x interface{}) bool {
      return _dafny.AreEqual(_77_x, _76_v)
    }
  })(v)))
}
func (_static *CompanionStruct_Default___) LastIndexByOption(xs _dafny.Sequence, p func (interface{}) bool) Std_Wrappers.Option {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return Std_Wrappers.Companion_Option_.Create_None_()
  } else if ((p)((xs).Select(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32()).(interface{}))) {
    return Std_Wrappers.Companion_Option_.Create_Some_((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One))
  } else {
    var _in4 _dafny.Sequence = (xs).Take(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32())
    _ = _in4
    var _in5 func (interface{}) bool = p
    _ = _in5
    xs = _in4
    p = _in5
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Remove(xs _dafny.Sequence, pos _dafny.Int) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate((xs).Take((pos).Uint32()), (xs).Drop(((pos).Plus(_dafny.One)).Uint32()))
}
func (_static *CompanionStruct_Default___) RemoveValue(xs _dafny.Sequence, v interface{}) _dafny.Sequence {
  if (!_dafny.Companion_Sequence_.Contains(xs, v)) {
    return xs
  } else {
    var _78_i _dafny.Int = Companion_Default___.IndexOf(xs, v)
    _ = _78_i
    return _dafny.Companion_Sequence_.Concatenate((xs).Take((_78_i).Uint32()), (xs).Drop(((_78_i).Plus(_dafny.One)).Uint32()))
  }
}
func (_static *CompanionStruct_Default___) Insert(xs _dafny.Sequence, a interface{}, pos _dafny.Int) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate((xs).Take((pos).Uint32()), _dafny.SeqOf(a)), (xs).Drop((pos).Uint32()))
}
func (_static *CompanionStruct_Default___) Reverse(xs _dafny.Sequence) _dafny.Sequence {
  var _79___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _79___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (_dafny.Companion_Sequence_.Equal(xs, _dafny.SeqOf())) {
    return _dafny.Companion_Sequence_.Concatenate(_79___accumulator, _dafny.SeqOf())
  } else {
    _79___accumulator = _dafny.Companion_Sequence_.Concatenate(_79___accumulator, _dafny.SeqOf((xs).Select(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32()).(interface{})))
    var _in6 _dafny.Sequence = (xs).Subsequence(0, ((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32())
    _ = _in6
    xs = _in6
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Repeat(v interface{}, length _dafny.Int) _dafny.Sequence {
  var _80___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _80___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((length).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_80___accumulator, _dafny.SeqOf())
  } else {
    _80___accumulator = _dafny.Companion_Sequence_.Concatenate(_80___accumulator, _dafny.SeqOf(v))
    var _in7 interface{} = v
    _ = _in7
    var _in8 _dafny.Int = (length).Minus(_dafny.One)
    _ = _in8
    v = _in7
    length = _in8
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Unzip(xs _dafny.Sequence) _dafny.Tuple {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.TupleOf(_dafny.SeqOf(), _dafny.SeqOf())
  } else {
    var _let_tmp_rhs0 _dafny.Tuple = Companion_Default___.Unzip(Companion_Default___.DropLast(xs))
    _ = _let_tmp_rhs0
    var _81_a _dafny.Sequence = (*(_let_tmp_rhs0).IndexInt(0)).(_dafny.Sequence)
    _ = _81_a
    var _82_b _dafny.Sequence = (*(_let_tmp_rhs0).IndexInt(1)).(_dafny.Sequence)
    _ = _82_b
    return _dafny.TupleOf(_dafny.Companion_Sequence_.Concatenate(_81_a, _dafny.SeqOf((*((Companion_Default___.Last(xs).(_dafny.Tuple))).IndexInt(0)))), _dafny.Companion_Sequence_.Concatenate(_82_b, _dafny.SeqOf((*((Companion_Default___.Last(xs).(_dafny.Tuple))).IndexInt(1)))))
  }
}
func (_static *CompanionStruct_Default___) Zip(xs _dafny.Sequence, ys _dafny.Sequence) _dafny.Sequence {
  var _83___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _83___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(), _83___accumulator)
  } else {
    _83___accumulator = _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(_dafny.TupleOf(Companion_Default___.Last(xs), Companion_Default___.Last(ys))), _83___accumulator)
    var _in9 _dafny.Sequence = Companion_Default___.DropLast(xs)
    _ = _in9
    var _in10 _dafny.Sequence = Companion_Default___.DropLast(ys)
    _ = _in10
    xs = _in9
    ys = _in10
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Max(xs _dafny.Sequence) _dafny.Int {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Cmp(_dafny.One) == 0) {
    return (xs).Select(0).(_dafny.Int)
  } else {
    return Std_Math.Companion_Default___.Max((xs).Select(0).(_dafny.Int), Companion_Default___.Max((xs).Drop(1)))
  }
}
func (_static *CompanionStruct_Default___) Min(xs _dafny.Sequence) _dafny.Int {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Cmp(_dafny.One) == 0) {
    return (xs).Select(0).(_dafny.Int)
  } else {
    return Std_Math.Companion_Default___.Min((xs).Select(0).(_dafny.Int), Companion_Default___.Min((xs).Drop(1)))
  }
}
func (_static *CompanionStruct_Default___) Flatten(xs _dafny.Sequence) _dafny.Sequence {
  var _84___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _84___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_84___accumulator, _dafny.SeqOf())
  } else {
    _84___accumulator = _dafny.Companion_Sequence_.Concatenate(_84___accumulator, (xs).Select(0).(_dafny.Sequence))
    var _in11 _dafny.Sequence = (xs).Drop(1)
    _ = _in11
    xs = _in11
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) FlattenReverse(xs _dafny.Sequence) _dafny.Sequence {
  var _85___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _85___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(), _85___accumulator)
  } else {
    _85___accumulator = _dafny.Companion_Sequence_.Concatenate(Companion_Default___.Last(xs).(_dafny.Sequence), _85___accumulator)
    var _in12 _dafny.Sequence = Companion_Default___.DropLast(xs)
    _ = _in12
    xs = _in12
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Join(seqs _dafny.Sequence, separator _dafny.Sequence) _dafny.Sequence {
  var _86___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _86___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((seqs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_86___accumulator, _dafny.SeqOf())
  } else if ((_dafny.IntOfUint32((seqs).Cardinality())).Cmp(_dafny.One) == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_86___accumulator, (seqs).Select(0).(_dafny.Sequence))
  } else {
    _86___accumulator = _dafny.Companion_Sequence_.Concatenate(_86___accumulator, _dafny.Companion_Sequence_.Concatenate((seqs).Select(0).(_dafny.Sequence), separator))
    var _in13 _dafny.Sequence = (seqs).Drop(1)
    _ = _in13
    var _in14 _dafny.Sequence = separator
    _ = _in14
    seqs = _in13
    separator = _in14
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Split(s _dafny.Sequence, delim interface{}) _dafny.Sequence {
  var _87___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _87___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  var _88_i Std_Wrappers.Option = Companion_Default___.IndexOfOption(s, delim)
  _ = _88_i
  if ((_88_i).Is_Some()) {
    _87___accumulator = _dafny.Companion_Sequence_.Concatenate(_87___accumulator, _dafny.SeqOf((s).Take(((_88_i).Dtor_value().(_dafny.Int)).Uint32())))
    var _in15 _dafny.Sequence = (s).Drop((((_88_i).Dtor_value().(_dafny.Int)).Plus(_dafny.One)).Uint32())
    _ = _in15
    var _in16 interface{} = delim
    _ = _in16
    s = _in15
    delim = _in16
    goto TAIL_CALL_START
  } else {
    return _dafny.Companion_Sequence_.Concatenate(_87___accumulator, _dafny.SeqOf(s))
  }
}
func (_static *CompanionStruct_Default___) SplitOnce(s _dafny.Sequence, delim interface{}) _dafny.Tuple {
  var _89_i Std_Wrappers.Option = Companion_Default___.IndexOfOption(s, delim)
  _ = _89_i
  return _dafny.TupleOf((s).Take(((_89_i).Dtor_value().(_dafny.Int)).Uint32()), (s).Drop((((_89_i).Dtor_value().(_dafny.Int)).Plus(_dafny.One)).Uint32()))
}
func (_static *CompanionStruct_Default___) SplitOnceOption(s _dafny.Sequence, delim interface{}) Std_Wrappers.Option {
  var _90_valueOrError0 Std_Wrappers.Option = Companion_Default___.IndexOfOption(s, delim)
  _ = _90_valueOrError0
  if ((_90_valueOrError0).IsFailure()) {
    return (_90_valueOrError0).PropagateFailure()
  } else {
    var _91_i _dafny.Int = (_90_valueOrError0).Extract().(_dafny.Int)
    _ = _91_i
    return Std_Wrappers.Companion_Option_.Create_Some_(_dafny.TupleOf((s).Take((_91_i).Uint32()), (s).Drop(((_91_i).Plus(_dafny.One)).Uint32())))
  }
}
func (_static *CompanionStruct_Default___) Map(f func (interface{}) interface{}, xs _dafny.Sequence) _dafny.Sequence {
  var _92___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _92___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_92___accumulator, _dafny.SeqOf())
  } else {
    _92___accumulator = _dafny.Companion_Sequence_.Concatenate(_92___accumulator, _dafny.SeqOf((f)((xs).Select(0).(interface{}))))
    var _in17 func (interface{}) interface{} = f
    _ = _in17
    var _in18 _dafny.Sequence = (xs).Drop(1)
    _ = _in18
    f = _in17
    xs = _in18
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) MapWithResult(f func (interface{}) Std_Wrappers.Result, xs _dafny.Sequence) Std_Wrappers.Result {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.SeqOf())
  } else {
    var _93_valueOrError0 Std_Wrappers.Result = (f)((xs).Select(0).(interface{}))
    _ = _93_valueOrError0
    if ((_93_valueOrError0).IsFailure()) {
      return (_93_valueOrError0).PropagateFailure()
    } else {
      var _94_head interface{} = (_93_valueOrError0).Extract()
      _ = _94_head
      var _95_valueOrError1 Std_Wrappers.Result = Companion_Default___.MapWithResult(f, (xs).Drop(1))
      _ = _95_valueOrError1
      if ((_95_valueOrError1).IsFailure()) {
        return (_95_valueOrError1).PropagateFailure()
      } else {
        var _96_tail _dafny.Sequence = (_95_valueOrError1).Extract().(_dafny.Sequence)
        _ = _96_tail
        return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(_94_head), _96_tail))
      }
    }
  }
}
func (_static *CompanionStruct_Default___) Filter(f func (interface{}) bool, xs _dafny.Sequence) _dafny.Sequence {
  var _97___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _97___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_97___accumulator, _dafny.SeqOf())
  } else {
    _97___accumulator = _dafny.Companion_Sequence_.Concatenate(_97___accumulator, (func () _dafny.Sequence { if (f)((xs).Select(0).(interface{})) { return _dafny.SeqOf((xs).Select(0).(interface{})) }; return _dafny.SeqOf() })() )
    var _in19 func (interface{}) bool = f
    _ = _in19
    var _in20 _dafny.Sequence = (xs).Drop(1)
    _ = _in20
    f = _in19
    xs = _in20
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) FoldLeft(f func (interface{}, interface{}) interface{}, init interface{}, xs _dafny.Sequence) interface{} {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return init
  } else {
    var _in21 func (interface{}, interface{}) interface{} = f
    _ = _in21
    var _in22 interface{} = (f)(init, (xs).Select(0).(interface{}))
    _ = _in22
    var _in23 _dafny.Sequence = (xs).Drop(1)
    _ = _in23
    f = _in21
    init = _in22
    xs = _in23
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) FoldRight(f func (interface{}, interface{}) interface{}, xs _dafny.Sequence, init interface{}) interface{} {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return init
  } else {
    return (f)((xs).Select(0).(interface{}), Companion_Default___.FoldRight(f, (xs).Drop(1), init))
  }
}
func (_static *CompanionStruct_Default___) SetToSeq(s _dafny.Set) _dafny.Sequence {
  var xs _dafny.Sequence = _dafny.EmptySeq
  _ = xs
  xs = _dafny.SeqOf()
  var _98_left _dafny.Set
  _ = _98_left
  _98_left = s
  for !(_98_left).Equals(_dafny.SetOf()) {
    var _99_x interface{}
    _ = _99_x
    {
      for _iter1 := _dafny.Iterate((_98_left).Elements());; {
        _assign_such_that_0, _ok1 := _iter1()
        if !_ok1 { break }
        _99_x = interface{}(_assign_such_that_0).(interface{})
        if ((_98_left).Contains(_99_x)) {
          goto L_ASSIGN_SUCH_THAT_0
        }
      }
      panic("assign-such-that search produced no value (line 7231)")
      goto L_ASSIGN_SUCH_THAT_0;
    }
  L_ASSIGN_SUCH_THAT_0:
    _98_left = (_98_left).Difference(_dafny.SetOf(_99_x))
    xs = _dafny.Companion_Sequence_.Concatenate(xs, _dafny.SeqOf(_99_x))
  }
  return xs
}
func (_static *CompanionStruct_Default___) SetToSortedSeq(s _dafny.Set, R func (interface{}, interface{}) bool) _dafny.Sequence {
  var xs _dafny.Sequence = _dafny.EmptySeq
  _ = xs
  var _out0 _dafny.Sequence
  _ = _out0
  _out0 = Companion_Default___.SetToSeq(s)
  xs = _out0
  xs = Companion_Default___.MergeSortBy(func (coer6 func (interface{}, interface{}) bool) func (interface{}, interface{}) bool {
    return func (arg6 interface{}, arg7 interface{}) bool {
      return coer6(arg6, arg7)
    }
  }(R), xs)
  return xs
}
func (_static *CompanionStruct_Default___) MergeSortBy(lessThanOrEq func (interface{}, interface{}) bool, a _dafny.Sequence) _dafny.Sequence {
  if ((_dafny.IntOfUint32((a).Cardinality())).Cmp(_dafny.One) <= 0) {
    return a
  } else {
    var _100_splitIndex _dafny.Int = (_dafny.IntOfUint32((a).Cardinality())).DivBy(_dafny.IntOfInt64(2))
    _ = _100_splitIndex
    var _101_left _dafny.Sequence = (a).Take((_100_splitIndex).Uint32())
    _ = _101_left
    var _102_right _dafny.Sequence = (a).Drop((_100_splitIndex).Uint32())
    _ = _102_right
    var _103_leftSorted _dafny.Sequence = Companion_Default___.MergeSortBy(lessThanOrEq, _101_left)
    _ = _103_leftSorted
    var _104_rightSorted _dafny.Sequence = Companion_Default___.MergeSortBy(lessThanOrEq, _102_right)
    _ = _104_rightSorted
    return Companion_Default___.MergeSortedWith(_103_leftSorted, _104_rightSorted, func (coer7 func (interface{}, interface{}) bool) func (interface{}, interface{}) bool {
      return func (arg8 interface{}, arg9 interface{}) bool {
        return coer7(arg8, arg9)
      }
    }(lessThanOrEq))
  }
}
func (_static *CompanionStruct_Default___) MergeSortedWith(left _dafny.Sequence, right _dafny.Sequence, lessThanOrEq func (interface{}, interface{}) bool) _dafny.Sequence {
  var _105___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _105___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((left).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_105___accumulator, right)
  } else if ((_dafny.IntOfUint32((right).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_105___accumulator, left)
  } else if ((lessThanOrEq)((left).Select(0).(interface{}), (right).Select(0).(interface{}))) {
    _105___accumulator = _dafny.Companion_Sequence_.Concatenate(_105___accumulator, _dafny.SeqOf((left).Select(0).(interface{})))
    var _in24 _dafny.Sequence = (left).Drop(1)
    _ = _in24
    var _in25 _dafny.Sequence = right
    _ = _in25
    var _in26 func (interface{}, interface{}) bool = lessThanOrEq
    _ = _in26
    left = _in24
    right = _in25
    lessThanOrEq = _in26
    goto TAIL_CALL_START
  } else {
    _105___accumulator = _dafny.Companion_Sequence_.Concatenate(_105___accumulator, _dafny.SeqOf((right).Select(0).(interface{})))
    var _in27 _dafny.Sequence = left
    _ = _in27
    var _in28 _dafny.Sequence = (right).Drop(1)
    _ = _in28
    var _in29 func (interface{}, interface{}) bool = lessThanOrEq
    _ = _in29
    left = _in27
    right = _in28
    lessThanOrEq = _in29
    goto TAIL_CALL_START
  }
}
// End of class Default__
