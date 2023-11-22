// Package ExternConcurrent
// Dafny module ExternConcurrent compiled into Go

package ExternConcurrent

import (
  _dafny "dafny"
  os "os"
  sync "sync"
  _System "System_"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__

type Dummy__ struct{}



// Definition of class MutableMap
type MutableMap struct {
  Internal sync.Map
}

func New_MutableMap_() *MutableMap {
  return &MutableMap{}
}

type CompanionStruct_MutableMap_ struct {
}
var Companion_MutableMap_ = CompanionStruct_MutableMap_ {
}

func (_this *MutableMap) Equals(other *MutableMap) bool {
  return _this == other
}

func (_this *MutableMap) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*MutableMap)
  return ok && _this.Equals(other)
}

func (*MutableMap) String() string {
  return "ExternConcurrent.MutableMap"
}

func Type_MutableMap_(Type_K_ _dafny.TypeDescriptor, Type_V_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_MutableMap_{Type_K_, Type_V_}
}

type type_MutableMap_ struct {
  Type_K_ _dafny.TypeDescriptor
  Type_V_ _dafny.TypeDescriptor
}

func (_this type_MutableMap_) Default() interface{} {
  return (*MutableMap)(nil)
}

func (_this type_MutableMap_) String() string {
  return "ExternConcurrent.MutableMap"
}
func (_this *MutableMap) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &MutableMap{}

func (_this *MutableMap) Ctor__(inv func (interface{}, interface{}) bool) {
  {
  }
}
func (_this *MutableMap) Keys() _dafny.Set {
  {
    keys := make([]interface{}, 0)

    _this.Internal.Range(func(key, value interface{}) bool {
      keys = append(keys, key)
      return true
    })

    return _dafny.SetOf(keys[:]...)
  }
}
func (_this *MutableMap) HasKey(k interface{}) bool {
  {
    _, ok := _this.Internal.Load(k)
    return ok
  }
}
func (_this *MutableMap) Values() _dafny.Set {
  {
    values := make([]interface{}, 0)

    _this.Internal.Range(func(key, value interface{}) bool {
      values = append(values, value)
      return true
    })

    return _dafny.SetOf(values[:]...)
  }
}
func (_this *MutableMap) Items() _dafny.Set {
  {
    items := make([]interface{}, 0)

    _this.Internal.Range(func(key, value interface{}) bool {
      items = append(items, _dafny.TupleOf(key, value))
      return true
    })

    return _dafny.SetOf(items[:]...)
  }
}
func (_this *MutableMap) Get(k interface{}) Option {
  {
    value, ok := _this.Internal.Load(k)
    if ok {
      return Companion_Option_.Create_Some_(value)
    } else {
      return Companion_Option_.Create_None_()
    }
  }
}
func (_this *MutableMap) Put(k interface{}, v interface{}) {
  {
    _this.Internal.Store(k, v)
  }
}
func (_this *MutableMap) Remove(k interface{}) {
  {
    _this.Internal.Delete(k)
  }
}
func (_this *MutableMap) Cardinality() _dafny.Int {
  {
    var c _dafny.Int = _dafny.Zero

    _this.Internal.Range(func(key, value interface{}) bool {
      c = c.Plus(_dafny.One)
      return true
    })

    return c
  }
}
// End of class MutableMap

// Definition of class AtomicBox
type AtomicBox struct {
  mu sync.Mutex

  Boxed interface{}
}

func New_AtomicBox_() *AtomicBox {
  _this := AtomicBox{}

  _this.Boxed = (interface{})(nil)
  return &_this
}

type CompanionStruct_AtomicBox_ struct {
}
var Companion_AtomicBox_ = CompanionStruct_AtomicBox_ {
}

func (_this *AtomicBox) Equals(other *AtomicBox) bool {
  return _this == other
}

func (_this *AtomicBox) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*AtomicBox)
  return ok && _this.Equals(other)
}

func (*AtomicBox) String() string {
  return "ExternConcurrent.AtomicBox"
}

func Type_AtomicBox_(Type_T_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
  return type_AtomicBox_{Type_T_}
}

type type_AtomicBox_ struct {
  Type_T_ _dafny.TypeDescriptor
}

func (_this type_AtomicBox_) Default() interface{} {
  return (*AtomicBox)(nil)
}

func (_this type_AtomicBox_) String() string {
  return "ExternConcurrent.AtomicBox"
}
func (_this *AtomicBox) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &AtomicBox{}

func (_this *AtomicBox) Ctor__(inv func (interface{}) bool, t interface{}) {
  {
    _this.mu.Lock()
    _this.Boxed = t
    _this.mu.Unlock()
  }
}
func (_this *AtomicBox) Get() interface{} {
  {
    var t interface{} = (interface{})(nil)
    _this.mu.Lock()
    t = _this.Boxed
    _this.mu.Unlock()
    return t
  }
}
func (_this *AtomicBox) Put(t interface{}) {
  {
    _this.mu.Lock()
    _this.Boxed = t
    _this.mu.Unlock()
  }
}
// End of class AtomicBox

// Definition of class Lock
type Lock struct {
  mu sync.Mutex
}

func New_Lock_() *Lock {
  _this := Lock{}

  return &_this
}

type CompanionStruct_Lock_ struct {
}
var Companion_Lock_ = CompanionStruct_Lock_ {
}

func (_this *Lock) Equals(other *Lock) bool {
  return _this == other
}

func (_this *Lock) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*Lock)
  return ok && _this.Equals(other)
}

func (*Lock) String() string {
  return "ExternConcurrent.Lock"
}

func Type_Lock_() _dafny.TypeDescriptor {
  return type_Lock_{}
}

type type_Lock_ struct {
}

func (_this type_Lock_) Default() interface{} {
  return (*Lock)(nil)
}

func (_this type_Lock_) String() string {
  return "ExternConcurrent.Lock"
}
func (_this *Lock) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Lock{}

func (_this *Lock) Ctor__() {
  {
  }
}
func (_this *Lock) Lock__() {
  {
    _this.mu.Lock()
  }
}
func (_this *Lock) Unlock() {
  {
    _this.mu.Unlock()
  }
}
// End of class Lock

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
      return "ExternConcurrent.Option.None"
    }
    case Option_Some: {
      return "ExternConcurrent.Option.Some" + "(" + _dafny.String(data.Value) + ")"
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
  return "ExternConcurrent.Option"
}
func (_this Option) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Option{}

func (_this Option) UnwrapOr(default_ interface{}) interface{} {
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
// End of datatype Option
