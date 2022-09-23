// RUN: %dafny_0 /compile:2 /compileTarget:java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Wrapper<T> = Wrapper(s: seq<T>)
{
  function method empty(): Wrapper<T>
  { Wrapper([]) }
}
