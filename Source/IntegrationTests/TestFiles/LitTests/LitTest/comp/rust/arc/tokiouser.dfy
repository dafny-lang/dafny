// NONUNIFORM: Rust-specific tests
// RUN: %baredafny translate rs --rust-module-name=tokiouser --include-runtime=true --rust-sync "%s" > "%t"
// RUN: "%S/tokiouser-rust/cargo" run >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(head: string, m: map<int, int>, tail: List)
function OfSize(n: nat, c: char): List {
  if n == 0 then Nil else Cons([c], map[], OfSize(n-1, c))
}