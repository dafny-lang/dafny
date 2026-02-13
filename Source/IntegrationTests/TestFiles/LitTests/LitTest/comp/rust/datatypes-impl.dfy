// NONUNIFORM: Tests generation of print, and equality in Rust for function / non-(==) type members
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype F = F(i: nat, f: int -> int)
datatype X<A> = X(x: A)

method Main()
{
  print X(3) == X(3), "\n",
        F(3, x => x), "\n";
}