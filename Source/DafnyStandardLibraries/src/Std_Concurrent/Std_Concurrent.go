package Std_Concurrent

import (
  _dafny "dafny"
  sync "sync"
  Std_Wrappers "Std_Wrappers"
)

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

func (_this *MutableMap) Ctor__() {
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
func (_this *MutableMap) Get(k interface{}) Std_Wrappers.Option {
  {
    value, ok := _this.Internal.Load(k)
    if ok {
      return Std_Wrappers.Companion_Option_.Create_Some_(value)
    } else {
      return Std_Wrappers.Companion_Option_.Create_None_()
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
func (_this *MutableMap) Size() _dafny.Int {
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

func (_this *AtomicBox) Ctor__(t interface{}) {
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