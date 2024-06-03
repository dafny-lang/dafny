// NONUNIFORM: Tests output of Rust translation from input Dafny that uses Rust reserved names
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype X = X(fn: int)

method Main()
{
  var f := X(3);
}