// NONUNIFORM: Rust-specific tests
// RUN: %baredafny translate rs --rust-module-name=tokiouser --include-runtime=true --rust-sync "%s" > "%t"
// RUN: "%S/tokiouser-rust/cargo" run >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype List = Nil | Cons(head: string, m: map<int, int>, tail: List)
function OfSize(n: nat, c: char): List {
  if n == 0 then Nil else Cons([c], map[], OfSize(n-1, c))
}
datatype Option<+T> = None | Some(value: T)
trait UpperTrait {
}
class UnderlyingObject extends UpperTrait {
  constructor() {}
}
method Test() {
  var n := new UnderlyingObject();
  var c: Option<UnderlyingObject> := Some(n);
  var d: Option<UpperTrait> := c;
  var e: object := d.value;
  var f := e as UnderlyingObject;
  var s := [c];
  var e_seq: seq<Option<UpperTrait>> := s;
}