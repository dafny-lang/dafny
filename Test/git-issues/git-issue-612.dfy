// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D
{
  function method {:extern Foo} Foo() : bool
}

