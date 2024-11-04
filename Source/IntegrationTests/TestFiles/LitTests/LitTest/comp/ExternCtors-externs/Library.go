// FIXME: Test currently fails on Go

package Library

import (
	"dafny"
	"fmt"
)

type Class struct{ n dafny.Int }

func New_Class_(n dafny.Int) *Class {
	return &Class{n}
}

func (obj *Class) Get() dafny.Int {
	return obj.n
}

type CompanionStruct_Class_ struct{}
var Companion_Class_ = CompanionStruct_Class_{}

func (CompanionStruct_Class_) SayHi() {
	fmt.Println("Hello!");
}
