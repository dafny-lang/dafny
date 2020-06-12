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

// have to implement this because the Go backend can't mix Dafny and Go code :-\

func (obj *Class) Print() {
	fmt.Printf("My value is %d\n", obj.n)
}

type CompanionStruct_Class_ struct{}
var Companion_Class_ = CompanionStruct_Class_{}

func (CompanionStruct_Class_) SayHi() {
	fmt.Println("Hello!");
}
