// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function IntToChar(i:int):char
  requires 0 <= i < 10
{
  (48 + i) as char
}

function CharToInt(i:char):int

{
  i as int - 48
}

method Main() {
  print IntToChar(8), "\n";
  print CharToInt('8'), "\n";
  Regression();
}

method Regression() {
  var i := '8';
  var u := i as myNative;  // this once crashed the verifier
  var v := i as mySubtype;  // this once crashed the verifier
  print i, " ", u, " ", v, "\n";
}

type mySubtype = x:int | 0 <= x < 100_000
newtype myNative = x:int | 0 <= x < 100_000
