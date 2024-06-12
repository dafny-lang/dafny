// NONUNIFORM: Tests output of Rust translation from input Dafny that uses Rust reserved names
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype X =
| X(fn: int, self: int, Self: int)
| None(None: int)

method Main()
{
  var f := X(0, 0, 0);
  var self := 0;
  var Self := 0;
  expect None(3).None == 3;
}