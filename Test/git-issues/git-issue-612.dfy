// RUN: %testDafnyForEachResolver "%s"


datatype D = D
{
  function {:extern Foo} Foo() : bool
}

