// Package Std_Collections_Seq
// Dafny module Std_Collections_Seq compiled into Go

package Std_Collections_Seq

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Std_Wrappers "Std_Wrappers"
  Std_BoundedInts "Std_BoundedInts"
  Std_Base64 "Std_Base64"
  Std_Relations "Std_Relations"
  Std_Math "Std_Math"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Std_Wrappers.Dummy__
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
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return Std_Wrappers.Companion_Option_.Create_None_()
  } else if (_dafny.AreEqual((xs).Select(0).(interface{}), v)) {
    return Std_Wrappers.Companion_Option_.Create_Some_(_dafny.Zero)
  } else {
    var _73_o_k Std_Wrappers.Option = Companion_Default___.IndexOfOption((xs).Drop(1), v)
    _ = _73_o_k
    if ((_73_o_k).Is_Some()) {
      return Std_Wrappers.Companion_Option_.Create_Some_(((_73_o_k).Dtor_value().(_dafny.Int)).Plus(_dafny.One))
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
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return Std_Wrappers.Companion_Option_.Create_None_()
  } else if (_dafny.AreEqual((xs).Select(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32()).(interface{}), v)) {
    return Std_Wrappers.Companion_Option_.Create_Some_((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One))
  } else {
    var _in4 _dafny.Sequence = (xs).Take(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32())
    _ = _in4
    var _in5 interface{} = v
    _ = _in5
    xs = _in4
    v = _in5
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
    var _74_i _dafny.Int = Companion_Default___.IndexOf(xs, v)
    _ = _74_i
    return _dafny.Companion_Sequence_.Concatenate((xs).Take((_74_i).Uint32()), (xs).Drop(((_74_i).Plus(_dafny.One)).Uint32()))
  }
}
func (_static *CompanionStruct_Default___) Insert(xs _dafny.Sequence, a interface{}, pos _dafny.Int) _dafny.Sequence {
  return _dafny.Companion_Sequence_.Concatenate(_dafny.Companion_Sequence_.Concatenate((xs).Take((pos).Uint32()), _dafny.SeqOf(a)), (xs).Drop((pos).Uint32()))
}
func (_static *CompanionStruct_Default___) Reverse(xs _dafny.Sequence) _dafny.Sequence {
  var _75___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _75___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if (_dafny.Companion_Sequence_.Equal(xs, _dafny.SeqOf())) {
    return _dafny.Companion_Sequence_.Concatenate(_75___accumulator, _dafny.SeqOf())
  } else {
    _75___accumulator = _dafny.Companion_Sequence_.Concatenate(_75___accumulator, _dafny.SeqOf((xs).Select(((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32()).(interface{})))
    var _in6 _dafny.Sequence = (xs).Subsequence(0, ((_dafny.IntOfUint32((xs).Cardinality())).Minus(_dafny.One)).Uint32())
    _ = _in6
    xs = _in6
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Repeat(v interface{}, length _dafny.Int) _dafny.Sequence {
  var _76___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _76___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((length).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_76___accumulator, _dafny.SeqOf())
  } else {
    _76___accumulator = _dafny.Companion_Sequence_.Concatenate(_76___accumulator, _dafny.SeqOf(v))
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
    var _77_a _dafny.Sequence = (*(_let_tmp_rhs0).IndexInt(0)).(_dafny.Sequence)
    _ = _77_a
    var _78_b _dafny.Sequence = (*(_let_tmp_rhs0).IndexInt(1)).(_dafny.Sequence)
    _ = _78_b
    return _dafny.TupleOf(_dafny.Companion_Sequence_.Concatenate(_77_a, _dafny.SeqOf((*((Companion_Default___.Last(xs).(_dafny.Tuple))).IndexInt(0)))), _dafny.Companion_Sequence_.Concatenate(_78_b, _dafny.SeqOf((*((Companion_Default___.Last(xs).(_dafny.Tuple))).IndexInt(1)))))
  }
}
func (_static *CompanionStruct_Default___) Zip(xs _dafny.Sequence, ys _dafny.Sequence) _dafny.Sequence {
  var _79___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _79___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(), _79___accumulator)
  } else {
    _79___accumulator = _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(_dafny.TupleOf(Companion_Default___.Last(xs), Companion_Default___.Last(ys))), _79___accumulator)
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
  var _80___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _80___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_80___accumulator, _dafny.SeqOf())
  } else {
    _80___accumulator = _dafny.Companion_Sequence_.Concatenate(_80___accumulator, (xs).Select(0).(_dafny.Sequence))
    var _in11 _dafny.Sequence = (xs).Drop(1)
    _ = _in11
    xs = _in11
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) FlattenReverse(xs _dafny.Sequence) _dafny.Sequence {
  var _81___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _81___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(), _81___accumulator)
  } else {
    _81___accumulator = _dafny.Companion_Sequence_.Concatenate(Companion_Default___.Last(xs).(_dafny.Sequence), _81___accumulator)
    var _in12 _dafny.Sequence = Companion_Default___.DropLast(xs)
    _ = _in12
    xs = _in12
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) Map(f func (interface{}) interface{}, xs _dafny.Sequence) _dafny.Sequence {
  var _82___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _82___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_82___accumulator, _dafny.SeqOf())
  } else {
    _82___accumulator = _dafny.Companion_Sequence_.Concatenate(_82___accumulator, _dafny.SeqOf((f)((xs).Select(0).(interface{}))))
    var _in13 func (interface{}) interface{} = f
    _ = _in13
    var _in14 _dafny.Sequence = (xs).Drop(1)
    _ = _in14
    f = _in13
    xs = _in14
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) MapWithResult(f func (interface{}) Std_Wrappers.Result, xs _dafny.Sequence) Std_Wrappers.Result {
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.SeqOf())
  } else {
    var _83_valueOrError0 Std_Wrappers.Result = (f)((xs).Select(0).(interface{}))
    _ = _83_valueOrError0
    if ((_83_valueOrError0).IsFailure()) {
      return (_83_valueOrError0).PropagateFailure()
    } else {
      var _84_head interface{} = (_83_valueOrError0).Extract()
      _ = _84_head
      var _85_valueOrError1 Std_Wrappers.Result = Companion_Default___.MapWithResult(f, (xs).Drop(1))
      _ = _85_valueOrError1
      if ((_85_valueOrError1).IsFailure()) {
        return (_85_valueOrError1).PropagateFailure()
      } else {
        var _86_tail _dafny.Sequence = (_85_valueOrError1).Extract().(_dafny.Sequence)
        _ = _86_tail
        return Std_Wrappers.Companion_Result_.Create_Success_(_dafny.Companion_Sequence_.Concatenate(_dafny.SeqOf(_84_head), _86_tail))
      }
    }
  }
}
func (_static *CompanionStruct_Default___) Filter(f func (interface{}) bool, xs _dafny.Sequence) _dafny.Sequence {
  var _87___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _87___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_87___accumulator, _dafny.SeqOf())
  } else {
    _87___accumulator = _dafny.Companion_Sequence_.Concatenate(_87___accumulator, (func () _dafny.Sequence { if (f)((xs).Select(0).(interface{})) { return _dafny.SeqOf((xs).Select(0).(interface{})) }; return _dafny.SeqOf() })() )
    var _in15 func (interface{}) bool = f
    _ = _in15
    var _in16 _dafny.Sequence = (xs).Drop(1)
    _ = _in16
    f = _in15
    xs = _in16
    goto TAIL_CALL_START
  }
}
func (_static *CompanionStruct_Default___) FoldLeft(f func (interface{}, interface{}) interface{}, init interface{}, xs _dafny.Sequence) interface{} {
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((xs).Cardinality())).Sign() == 0) {
    return init
  } else {
    var _in17 func (interface{}, interface{}) interface{} = f
    _ = _in17
    var _in18 interface{} = (f)(init, (xs).Select(0).(interface{}))
    _ = _in18
    var _in19 _dafny.Sequence = (xs).Drop(1)
    _ = _in19
    f = _in17
    init = _in18
    xs = _in19
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
  var _88_left _dafny.Set
  _ = _88_left
  _88_left = s
  for !(_88_left).Equals(_dafny.SetOf()) {
    var _89_x interface{}
    _ = _89_x
    {
      for _iter1 := _dafny.Iterate((_88_left).Elements());; {
        _assign_such_that_0, _ok1 := _iter1()
        if !_ok1 { break }
        _89_x = interface{}(_assign_such_that_0).(interface{})
        if ((_88_left).Contains(_89_x)) {
          goto L_ASSIGN_SUCH_THAT_0
        }
      }
      panic("assign-such-that search produced no value (line 7122)")
      goto L_ASSIGN_SUCH_THAT_0;
    }
  L_ASSIGN_SUCH_THAT_0:
    _88_left = (_88_left).Difference(_dafny.SetOf(_89_x))
    xs = _dafny.Companion_Sequence_.Concatenate(xs, _dafny.SeqOf(_89_x))
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
  xs = Companion_Default___.MergeSortBy(func (coer4 func (interface{}, interface{}) bool) func (interface{}, interface{}) bool {
    return func (arg4 interface{}, arg5 interface{}) bool {
      return coer4(arg4, arg5)
    }
  }(R), xs)
  return xs
}
func (_static *CompanionStruct_Default___) MergeSortBy(lessThanOrEq func (interface{}, interface{}) bool, a _dafny.Sequence) _dafny.Sequence {
  if ((_dafny.IntOfUint32((a).Cardinality())).Cmp(_dafny.One) <= 0) {
    return a
  } else {
    var _90_splitIndex _dafny.Int = (_dafny.IntOfUint32((a).Cardinality())).DivBy(_dafny.IntOfInt64(2))
    _ = _90_splitIndex
    var _91_left _dafny.Sequence = (a).Take((_90_splitIndex).Uint32())
    _ = _91_left
    var _92_right _dafny.Sequence = (a).Drop((_90_splitIndex).Uint32())
    _ = _92_right
    var _93_leftSorted _dafny.Sequence = Companion_Default___.MergeSortBy(lessThanOrEq, _91_left)
    _ = _93_leftSorted
    var _94_rightSorted _dafny.Sequence = Companion_Default___.MergeSortBy(lessThanOrEq, _92_right)
    _ = _94_rightSorted
    return Companion_Default___.MergeSortedWith(_93_leftSorted, _94_rightSorted, func (coer5 func (interface{}, interface{}) bool) func (interface{}, interface{}) bool {
      return func (arg6 interface{}, arg7 interface{}) bool {
        return coer5(arg6, arg7)
      }
    }(lessThanOrEq))
  }
}
func (_static *CompanionStruct_Default___) MergeSortedWith(left _dafny.Sequence, right _dafny.Sequence, lessThanOrEq func (interface{}, interface{}) bool) _dafny.Sequence {
  var _95___accumulator _dafny.Sequence = _dafny.SeqOf()
  _ = _95___accumulator
  goto TAIL_CALL_START
  TAIL_CALL_START:
  if ((_dafny.IntOfUint32((left).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_95___accumulator, right)
  } else if ((_dafny.IntOfUint32((right).Cardinality())).Sign() == 0) {
    return _dafny.Companion_Sequence_.Concatenate(_95___accumulator, left)
  } else if ((lessThanOrEq)((left).Select(0).(interface{}), (right).Select(0).(interface{}))) {
    _95___accumulator = _dafny.Companion_Sequence_.Concatenate(_95___accumulator, _dafny.SeqOf((left).Select(0).(interface{})))
    var _in20 _dafny.Sequence = (left).Drop(1)
    _ = _in20
    var _in21 _dafny.Sequence = right
    _ = _in21
    var _in22 func (interface{}, interface{}) bool = lessThanOrEq
    _ = _in22
    left = _in20
    right = _in21
    lessThanOrEq = _in22
    goto TAIL_CALL_START
  } else {
    _95___accumulator = _dafny.Companion_Sequence_.Concatenate(_95___accumulator, _dafny.SeqOf((right).Select(0).(interface{})))
    var _in23 _dafny.Sequence = left
    _ = _in23
    var _in24 _dafny.Sequence = (right).Drop(1)
    _ = _in24
    var _in25 func (interface{}, interface{}) bool = lessThanOrEq
    _ = _in25
    left = _in23
    right = _in24
    lessThanOrEq = _in25
    goto TAIL_CALL_START
  }
}
// End of class Default__
