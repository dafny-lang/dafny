// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment

method lol() returns (c: int)
{
  c := 5;
  return c;
}
