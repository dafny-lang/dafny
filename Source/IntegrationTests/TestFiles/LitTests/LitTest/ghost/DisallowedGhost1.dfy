// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --print=-


method Test1()
{
  var first := 0;
  var t := (ghost first:=123, 1:=234); // error
}

method Test2()
{
  var t := (1:=123, 2:=234); // error
}

method Test3()
{
  var t := (1:=123, 1:=234); // error
}
