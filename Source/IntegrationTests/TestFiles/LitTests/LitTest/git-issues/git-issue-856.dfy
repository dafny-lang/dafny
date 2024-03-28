// RUN: %verify "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 --target cs "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 --target js "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target go "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  var big := 9223372036854775808;
  var a := new int[big];
  assert a.Length == big;
  print a.Length == big;
}

