// RUN: echo ""
// This is just an auxiliary file, with no tests by itself

abstract module Foo {
  type Value

  datatype Message =
    | M(value: Value)

  lemma someLemma(a: Message, b: Message, c: Message)
  {
    match (a, b, c) {
      case (M(x), M(y), M(z)) => { }
    }
  }
}

module ByteDefinition {
  newtype byte = i:int | 0 <= i < 0x100
  type Byte = byte
}

module ConcreteFoo refines Foo {
  import ByteDefinition

  type Value = ByteDefinition.Byte
}
