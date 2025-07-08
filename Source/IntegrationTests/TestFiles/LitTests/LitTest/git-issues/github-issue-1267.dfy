// RUN: %testDafnyForEachResolver "%s" -- --print:-


method Test()
{
  var tuple0 := (1 := 300, 0 := 10);
  var tuple1 := (10, 300);
  assert tuple0 == tuple1;
}
