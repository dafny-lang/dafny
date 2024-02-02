// RUN: %exits-with 4 %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait H<Y> { var data: Y }
class K extends H<int> { }

type Singleton = ()

method Main() {
  var k := new K;
  var a: H<int> := k;
  var b: H<Singleton> := BadCast(k);
  assert a == k == b;
  label L:
  var x := a.data;
  Change(a);
  NothingChanged@L(b);
  assert a.data == x;
  assert false;
  var u := 1 / 0;
}

ghost method BadCast(k: K) returns (b: H<Singleton>)
  ensures b == k
{
  var oo: object := k;
  b := oo; // error: this was once not caught by the verifier
}

method Change(a: H<int>)
  modifies a
  ensures a.data != old(a.data)
{
  a.data := a.data + 1;
}

twostate lemma NothingChanged(b: H<Singleton>)
  ensures b.data == old(b.data)
{
  assert old(b.data) == () == b.data;
}
