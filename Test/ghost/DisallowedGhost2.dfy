// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --print:-


method Test()
{
  var (ghost x) := 123; // syntax error
}
