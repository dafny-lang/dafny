// Package _System
// Dafny module _System compiled into Go

package _System

import (
	os "os"

	_dafny "github.com/dafny-lang/DafnyRuntimeGo/v4/dafny"
)

var _ = os.Args
var _ _dafny.Dummy__

type Dummy__ struct{}

// Definition of class Nat
type Nat struct {
}

func New_Nat_() *Nat {
	_this := Nat{}

	return &_this
}

type CompanionStruct_Nat_ struct {
}

var Companion_Nat_ = CompanionStruct_Nat_{}

func (*Nat) String() string {
	return "_System.Nat"
}

// End of class Nat

func Type_Nat_() _dafny.TypeDescriptor {
	return type_Nat_{}
}

type type_Nat_ struct {
}

func (_this type_Nat_) Default() interface{} {
	return _dafny.Zero
}

func (_this type_Nat_) String() string {
	return "_System.Nat"
}
func (_this *CompanionStruct_Nat_) Is_(__source _dafny.Int) bool {
	var _0_x _dafny.Int = (__source)
	_ = _0_x
	return (_0_x).Sign() != -1
}
