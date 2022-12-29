// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D
{
  function method {:extern Foo} Foo() : bool
}

