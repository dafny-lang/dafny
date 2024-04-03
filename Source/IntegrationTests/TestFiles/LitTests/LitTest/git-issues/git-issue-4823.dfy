// RUN: %baredafny verify %args --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Test<T> {
  function Cast(t: T): Test<T>
}

datatype Impl extends Test<Impl> = ImplConstructor()
{
  function Cast(t: Impl): Test<Impl> { t }
}