// RUN: %testDafnyForEachResolver "%s" -- --general-traits=datatype

trait A<K> {
  function FunctionRequires(): bool
    requires true
  function FunctionReads(): bool
    reads {}
    decreases 2
  function FunctionEnsures(): bool
    ensures true

  method MethodRequires()
    requires true
  method MethodEnsures()
    ensures true
}

type B extends A<string> {
  // Each of the following 5 override checks once caused a crash, because those checks
  // were not expecting the overrides to be found in an abstract type.

  function FunctionRequires(): bool
  function FunctionReads(): bool
    decreases 2
  function FunctionEnsures(): bool

  method MethodRequires()
  method MethodEnsures()
}
