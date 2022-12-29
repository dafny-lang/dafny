// RUN: %baredafny verify %args "%s" > "%t"
// RUN: ! %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: ! %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  var big := 9223372036854775808;
  var a := new int[big];
  assert a.Length == big;
  print a.Length == big;
}

