package Nested_mLibrary

import (
  "dafny"
)

func Foo() {
  dafny.Print((dafny.SeqOfString("Nested.Library.Foo\n")).SetString())
}
