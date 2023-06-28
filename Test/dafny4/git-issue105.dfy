// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

method lol() returns (c: int)
{
  c := 5;
  return c;
}
