package Nested_Library

import (
  "dafny"
)

type CompanionStruct_Default___ struct {
}
var Companion_Default___ = CompanionStruct_Default___ {
}

func (_static *CompanionStruct_Default___) Foo() {
  dafny.Print((dafny.SeqOfString("Nested.Library.Foo\n")).SetString())
}
