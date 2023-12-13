// Package Std_Wrappers
// Dafny module Std_Wrappers compiled into Go

package Std_Wrappers

import (
  _dafny "dafny"
  os "os"
  _System "System_"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__

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
  return "Std_Wrappers.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Need(condition bool, error_ interface{}) OutcomeResult {
  if (condition) {
    return Companion_OutcomeResult_.Create_Pass_k_()
  } else {
    return Companion_OutcomeResult_.Create_Fail_k_(error_)
  }
}
// End of class Default__

// Definition of datatype Option
type Option struct {
  Data_Option_
}

func (_this Option) Get_() Data_Option_ {
  return _this.Data_Option_
}

type Data_Option_ interface {
  isOption()
}

type CompanionStruct_Option_ struct {
}
var Companion_Option_ = CompanionStruct_Option_ {
}

type Option_None struct {
}

func (Option_None) isOption() {}

func (CompanionStruct_Option_) Create_None_() Option {
  return Option{Option_None{}}
}

func (_this Option) Is_None() bool {
  _, ok := _this.Get_().(Option_None)
  return ok
}

type Option_Some struct {
  Value interface{}
}

func (Option_Some) isOption() {}

func (CompanionStruct_Option_) Create_Some_(Value interface{}) Option {
  return Option{Option_Some{Value}}
}

func (_this Option) Is_Some() bool {
  _, ok := _this.Get_().(Option_Some)
  return ok
}

func (CompanionStruct_Option_) Default() Option {
  return Companion_Option_.Create_None_()
}

func (_this Option) Dtor_value() interface{} {
  return _this.Get_().(Option_Some).Value
}

func (_this Option) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Option_None: {
      return "Wrappers.Option.None"
    }
    case Option_Some: {
      return "Wrappers.Option.Some" + "(" + _dafny.String(data.Value) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Option) Equals(other Option) bool {
  switch data1 := _this.Get_().(type) {
    case Option_None: {
      _, ok := other.Get_().(Option_None)
      return ok
    }
    case Option_Some: {
      data2, ok := other.Get_().(Option_Some)
      return ok && _dafny.AreEqual(data1.Value, data2.Value)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Option) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Option)
  return ok && _this.Equals(typed)
}

func Type_Option_() _dafny.TypeDescriptor {
  return type_Option_{}
}

type type_Option_ struct {
}

func (_this type_Option_) Default() interface{} {
  return Companion_Option_.Default();
}

func (_this type_Option_) String() string {
  return "Std_Wrappers.Option"
}
func (_this Option) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Option{}

func (_this Option) IsFailure() bool {
  {
    return (_this).Is_None()
  }
}
func (_this Option) PropagateFailure() Option {
  {
    return Companion_Option_.Create_None_()
  }
}
func (_this Option) Extract() interface{} {
  {
    return (_this).Dtor_value()
  }
}
func (_this Option) GetOr(default_ interface{}) interface{} {
  {
    var _source0 Option = _this
    _ = _source0
    if (_source0.Is_None()) {
      return default_
    } else {
      var _0___mcc_h0 interface{} = _source0.Get_().(Option_Some).Value
      _ = _0___mcc_h0
      var _1_v interface{} = _0___mcc_h0
      _ = _1_v
      return _1_v
    }
  }
}
func (_this Option) ToResult(error_ interface{}) Result {
  {
    var _source1 Option = _this
    _ = _source1
    if (_source1.Is_None()) {
      return Companion_Result_.Create_Failure_(error_)
    } else {
      var _2___mcc_h0 interface{} = _source1.Get_().(Option_Some).Value
      _ = _2___mcc_h0
      var _3_v interface{} = _2___mcc_h0
      _ = _3_v
      return Companion_Result_.Create_Success_(_3_v)
    }
  }
}
func (_this Option) ToOutcome(error_ interface{}) Outcome {
  {
    var _source2 Option = _this
    _ = _source2
    if (_source2.Is_None()) {
      return Companion_Outcome_.Create_Fail_(error_)
    } else {
      var _4___mcc_h0 interface{} = _source2.Get_().(Option_Some).Value
      _ = _4___mcc_h0
      var _5_v interface{} = _4___mcc_h0
      _ = _5_v
      return Companion_Outcome_.Create_Pass_()
    }
  }
}
func (_this Option) Map(rewrap func (Option) interface{}) interface{} {
  {
    return (rewrap)(_this)
  }
}
// End of datatype Option

// Definition of datatype Result
type Result struct {
  Data_Result_
}

func (_this Result) Get_() Data_Result_ {
  return _this.Data_Result_
}

type Data_Result_ interface {
  isResult()
}

type CompanionStruct_Result_ struct {
}
var Companion_Result_ = CompanionStruct_Result_ {
}

type Result_Success struct {
  Value interface{}
}

func (Result_Success) isResult() {}

func (CompanionStruct_Result_) Create_Success_(Value interface{}) Result {
  return Result{Result_Success{Value}}
}

func (_this Result) Is_Success() bool {
  _, ok := _this.Get_().(Result_Success)
  return ok
}

type Result_Failure struct {
  Error interface{}
}

func (Result_Failure) isResult() {}

func (CompanionStruct_Result_) Create_Failure_(Error interface{}) Result {
  return Result{Result_Failure{Error}}
}

func (_this Result) Is_Failure() bool {
  _, ok := _this.Get_().(Result_Failure)
  return ok
}

func (CompanionStruct_Result_) Default(_default_R interface{}) Result {
  return Companion_Result_.Create_Success_(_default_R)
}

func (_this Result) Dtor_value() interface{} {
  return _this.Get_().(Result_Success).Value
}

func (_this Result) Dtor_error() interface{} {
  return _this.Get_().(Result_Failure).Error
}

func (_this Result) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Result_Success: {
      return "Wrappers.Result.Success" + "(" + _dafny.String(data.Value) + ")"
    }
    case Result_Failure: {
      return "Wrappers.Result.Failure" + "(" + _dafny.String(data.Error) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Result) Equals(other Result) bool {
  switch data1 := _this.Get_().(type) {
    case Result_Success: {
      data2, ok := other.Get_().(Result_Success)
      return ok && _dafny.AreEqual(data1.Value, data2.Value)
    }
    case Result_Failure: {
      data2, ok := other.Get_().(Result_Failure)
      return ok && _dafny.AreEqual(data1.Error, data2.Error)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Result) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Result)
  return ok && _this.Equals(typed)
}

func Type_Result_(Type_R_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_Result_{Type_R_}
}

type type_Result_ struct {
  Type_R_ _dafny.TypeDescriptor
}

func (_this type_Result_) Default() interface{} {
  Type_R_ := _this.Type_R_
  _ = Type_R_
  return Companion_Result_.Default(Type_R_.Default());
}

func (_this type_Result_) String() string {
  return "Std_Wrappers.Result"
}
func (_this Result) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Result{}

func (_this Result) IsFailure() bool {
  {
    return (_this).Is_Failure()
  }
}
func (_this Result) PropagateFailure() Result {
  {
    return Companion_Result_.Create_Failure_((_this).Dtor_error())
  }
}
func (_this Result) Extract() interface{} {
  {
    return (_this).Dtor_value()
  }
}
func (_this Result) GetOr(default_ interface{}) interface{} {
  {
    var _source3 Result = _this
    _ = _source3
    if (_source3.Is_Success()) {
      var _6___mcc_h0 interface{} = _source3.Get_().(Result_Success).Value
      _ = _6___mcc_h0
      var _7_s interface{} = _6___mcc_h0
      _ = _7_s
      return _7_s
    } else {
      var _8___mcc_h1 interface{} = _source3.Get_().(Result_Failure).Error
      _ = _8___mcc_h1
      var _9_e interface{} = _8___mcc_h1
      _ = _9_e
      return default_
    }
  }
}
func (_this Result) ToOption() Option {
  {
    var _source4 Result = _this
    _ = _source4
    if (_source4.Is_Success()) {
      var _10___mcc_h0 interface{} = _source4.Get_().(Result_Success).Value
      _ = _10___mcc_h0
      var _11_s interface{} = _10___mcc_h0
      _ = _11_s
      return Companion_Option_.Create_Some_(_11_s)
    } else {
      var _12___mcc_h1 interface{} = _source4.Get_().(Result_Failure).Error
      _ = _12___mcc_h1
      var _13_e interface{} = _12___mcc_h1
      _ = _13_e
      return Companion_Option_.Create_None_()
    }
  }
}
func (_this Result) ToOutcome() Outcome {
  {
    var _source5 Result = _this
    _ = _source5
    if (_source5.Is_Success()) {
      var _14___mcc_h0 interface{} = _source5.Get_().(Result_Success).Value
      _ = _14___mcc_h0
      var _15_s interface{} = _14___mcc_h0
      _ = _15_s
      return Companion_Outcome_.Create_Pass_()
    } else {
      var _16___mcc_h1 interface{} = _source5.Get_().(Result_Failure).Error
      _ = _16___mcc_h1
      var _17_e interface{} = _16___mcc_h1
      _ = _17_e
      return Companion_Outcome_.Create_Fail_(_17_e)
    }
  }
}
func (_this Result) Map(rewrap func (Result) interface{}) interface{} {
  {
    return (rewrap)(_this)
  }
}
func (_this Result) MapFailure(reWrap func (interface{}) interface{}) Result {
  {
    var _source6 Result = _this
    _ = _source6
    if (_source6.Is_Success()) {
      var _18___mcc_h0 interface{} = _source6.Get_().(Result_Success).Value
      _ = _18___mcc_h0
      var _19_s interface{} = _18___mcc_h0
      _ = _19_s
      return Companion_Result_.Create_Success_(_19_s)
    } else {
      var _20___mcc_h1 interface{} = _source6.Get_().(Result_Failure).Error
      _ = _20___mcc_h1
      var _21_e interface{} = _20___mcc_h1
      _ = _21_e
      return Companion_Result_.Create_Failure_((reWrap)(_21_e))
    }
  }
}
// End of datatype Result

// Definition of datatype Outcome
type Outcome struct {
  Data_Outcome_
}

func (_this Outcome) Get_() Data_Outcome_ {
  return _this.Data_Outcome_
}

type Data_Outcome_ interface {
  isOutcome()
}

type CompanionStruct_Outcome_ struct {
}
var Companion_Outcome_ = CompanionStruct_Outcome_ {
}

type Outcome_Pass struct {
}

func (Outcome_Pass) isOutcome() {}

func (CompanionStruct_Outcome_) Create_Pass_() Outcome {
  return Outcome{Outcome_Pass{}}
}

func (_this Outcome) Is_Pass() bool {
  _, ok := _this.Get_().(Outcome_Pass)
  return ok
}

type Outcome_Fail struct {
  Error interface{}
}

func (Outcome_Fail) isOutcome() {}

func (CompanionStruct_Outcome_) Create_Fail_(Error interface{}) Outcome {
  return Outcome{Outcome_Fail{Error}}
}

func (_this Outcome) Is_Fail() bool {
  _, ok := _this.Get_().(Outcome_Fail)
  return ok
}

func (CompanionStruct_Outcome_) Default() Outcome {
  return Companion_Outcome_.Create_Pass_()
}

func (_this Outcome) Dtor_error() interface{} {
  return _this.Get_().(Outcome_Fail).Error
}

func (_this Outcome) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case Outcome_Pass: {
      return "Wrappers.Outcome.Pass"
    }
    case Outcome_Fail: {
      return "Wrappers.Outcome.Fail" + "(" + _dafny.String(data.Error) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Outcome) Equals(other Outcome) bool {
  switch data1 := _this.Get_().(type) {
    case Outcome_Pass: {
      _, ok := other.Get_().(Outcome_Pass)
      return ok
    }
    case Outcome_Fail: {
      data2, ok := other.Get_().(Outcome_Fail)
      return ok && _dafny.AreEqual(data1.Error, data2.Error)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Outcome) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Outcome)
  return ok && _this.Equals(typed)
}

func Type_Outcome_() _dafny.TypeDescriptor {
  return type_Outcome_{}
}

type type_Outcome_ struct {
}

func (_this type_Outcome_) Default() interface{} {
  return Companion_Outcome_.Default();
}

func (_this type_Outcome_) String() string {
  return "Std_Wrappers.Outcome"
}
func (_this Outcome) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Outcome{}

func (_this Outcome) IsFailure() bool {
  {
    return (_this).Is_Fail()
  }
}
func (_this Outcome) PropagateFailure() Outcome {
  {
    return _this
  }
}
func (_this Outcome) ToOption(r interface{}) Option {
  {
    var _source7 Outcome = _this
    _ = _source7
    if (_source7.Is_Pass()) {
      return Companion_Option_.Create_Some_(r)
    } else {
      var _22___mcc_h0 interface{} = _source7.Get_().(Outcome_Fail).Error
      _ = _22___mcc_h0
      var _23_e interface{} = _22___mcc_h0
      _ = _23_e
      return Companion_Option_.Create_None_()
    }
  }
}
func (_this Outcome) ToResult(r interface{}) Result {
  {
    var _source8 Outcome = _this
    _ = _source8
    if (_source8.Is_Pass()) {
      return Companion_Result_.Create_Success_(r)
    } else {
      var _24___mcc_h0 interface{} = _source8.Get_().(Outcome_Fail).Error
      _ = _24___mcc_h0
      var _25_e interface{} = _24___mcc_h0
      _ = _25_e
      return Companion_Result_.Create_Failure_(_25_e)
    }
  }
}
func (_this Outcome) Map(rewrap func (Outcome) interface{}) interface{} {
  {
    return (rewrap)(_this)
  }
}
func (_this Outcome) MapFailure(rewrap func (interface{}) interface{}, default_ interface{}) Result {
  {
    var _source9 Outcome = _this
    _ = _source9
    if (_source9.Is_Pass()) {
      return Companion_Result_.Create_Success_(default_)
    } else {
      var _26___mcc_h0 interface{} = _source9.Get_().(Outcome_Fail).Error
      _ = _26___mcc_h0
      var _27_e interface{} = _26___mcc_h0
      _ = _27_e
      return Companion_Result_.Create_Failure_((rewrap)(_27_e))
    }
  }
}
func (_static CompanionStruct_Outcome_) Need(condition bool, error_ interface{}) Outcome {
  if (condition) {
    return Companion_Outcome_.Create_Pass_()
  } else {
    return Companion_Outcome_.Create_Fail_(error_)
  }
}
// End of datatype Outcome

// Definition of datatype OutcomeResult
type OutcomeResult struct {
  Data_OutcomeResult_
}

func (_this OutcomeResult) Get_() Data_OutcomeResult_ {
  return _this.Data_OutcomeResult_
}

type Data_OutcomeResult_ interface {
  isOutcomeResult()
}

type CompanionStruct_OutcomeResult_ struct {
}
var Companion_OutcomeResult_ = CompanionStruct_OutcomeResult_ {
}

type OutcomeResult_Pass_k struct {
}

func (OutcomeResult_Pass_k) isOutcomeResult() {}

func (CompanionStruct_OutcomeResult_) Create_Pass_k_() OutcomeResult {
  return OutcomeResult{OutcomeResult_Pass_k{}}
}

func (_this OutcomeResult) Is_Pass_k() bool {
  _, ok := _this.Get_().(OutcomeResult_Pass_k)
  return ok
}

type OutcomeResult_Fail_k struct {
  Error interface{}
}

func (OutcomeResult_Fail_k) isOutcomeResult() {}

func (CompanionStruct_OutcomeResult_) Create_Fail_k_(Error interface{}) OutcomeResult {
  return OutcomeResult{OutcomeResult_Fail_k{Error}}
}

func (_this OutcomeResult) Is_Fail_k() bool {
  _, ok := _this.Get_().(OutcomeResult_Fail_k)
  return ok
}

func (CompanionStruct_OutcomeResult_) Default() OutcomeResult {
  return Companion_OutcomeResult_.Create_Pass_k_()
}

func (_this OutcomeResult) Dtor_error() interface{} {
  return _this.Get_().(OutcomeResult_Fail_k).Error
}

func (_this OutcomeResult) String() string {
  switch data := _this.Get_().(type) {
    case nil: return "null"
    case OutcomeResult_Pass_k: {
      return "Wrappers.OutcomeResult.Pass'"
    }
    case OutcomeResult_Fail_k: {
      return "Wrappers.OutcomeResult.Fail'" + "(" + _dafny.String(data.Error) + ")"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this OutcomeResult) Equals(other OutcomeResult) bool {
  switch data1 := _this.Get_().(type) {
    case OutcomeResult_Pass_k: {
      _, ok := other.Get_().(OutcomeResult_Pass_k)
      return ok
    }
    case OutcomeResult_Fail_k: {
      data2, ok := other.Get_().(OutcomeResult_Fail_k)
      return ok && _dafny.AreEqual(data1.Error, data2.Error)
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this OutcomeResult) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(OutcomeResult)
  return ok && _this.Equals(typed)
}

func Type_OutcomeResult_() _dafny.TypeDescriptor {
  return type_OutcomeResult_{}
}

type type_OutcomeResult_ struct {
}

func (_this type_OutcomeResult_) Default() interface{} {
  return Companion_OutcomeResult_.Default();
}

func (_this type_OutcomeResult_) String() string {
  return "Std_Wrappers.OutcomeResult"
}
func (_this OutcomeResult) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = OutcomeResult{}

func (_this OutcomeResult) IsFailure() bool {
  {
    return (_this).Is_Fail_k()
  }
}
func (_this OutcomeResult) PropagateFailure() Result {
  {
    return Companion_Result_.Create_Failure_((_this).Dtor_error())
  }
}
// End of datatype OutcomeResult
