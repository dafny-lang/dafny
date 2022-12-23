// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait A<X> { }
trait B<Y0, Y1> { }
trait C<Z> extends B<int, Z> { }

class K<U> extends object, B<int, U> { }
class L<V> extends C<V> { }

method AssignBackAndForth<W>(a: A<W>, b: B<int, W>, c: C<W>, k: K<W>, l: L<W>) returns (a': A<W>, b': B<int, W>, c': C<W>, k': K<W>, l': L<W>)
  ensures a' == a && b' == b && c' == c && k' == k && l' == l
{
  var o: object?;

  o := a;
  a' := o;

  o := b;
  b' := o;

  o := c;
  c' := o;

  o := k;
  k' := o;

  o := l;
  l' := o;
}

method AsBackAndForth<W>(a: A<W>, b: B<int, W>, c: C<W>, k: K<W>, l: L<W>) returns (a': object, b': object, c': object, k': object, l': object)
  ensures a' == a && b' == b && c' == c && k' == k && l' == l
{
  var o: object?;

  o := a;
  a' := o as A<W>;

  o := b;
  b' := o as B<int, W>;

  o := c;
  c' := o as C<W>;

  o := k;
  k' := o as K<W>;

  o := l;
  l' := o as L<W>;
}

method BadCasts<W>(k: K<W>, l: L<W>) {
  var o: object := k as object;
  if
  case true =>
    var b := k as B<int, W>;
    var b' := l as B<int, W>;
    var p := b as object as K<W>;
    var p' := b' as object as K<W>; // error
  case true =>
    var b := o as B<real, W>; // error
  case true =>
    var b := o as B<W, int>; // error
  case true =>
    var b := k as object as B<int, int>; // error
  case true =>
    var b := o as A<W>; // error
}

method CastsAfterTypeTests<W>(k: K<W>, l: L<W>) {
  var o: object := k as object;
  if
  case l as object is K<W> =>
    var p' := l as object as K<W>; // this verifies
    assert false; // and so does this
  case o is B<real, W> =>
    var b := o as B<real, W>;
  case o is B<W, int> =>
    var b := o as B<W, int>;
  case k as object is B<int, int> =>
    var b := k as object as B<int, int>;
  case o is A<W> =>
    var b := o as A<W>;
  case k is K<W> =>
    assert k == k as K<W>;
}

trait TraitA<X> { }
class ClassQ<Y> extends TraitA<Y> { }
method ParsingSuccessors<U>(t: TraitA<U>) {
  var b;
  b := if t is ClassQ<U> then true else false;
  b := t is ClassQ<U> && t is ClassQ<U>;
  b := t is ClassQ<U> || t is ClassQ<U>;
  b := t is ClassQ<U> ==> t is ClassQ<U>;
  b := t is ClassQ<U> <== t is ClassQ<U>;
  b := t is ClassQ<U> <==> t is ClassQ<U>;
  assert b;
}

class SupersetClass {
  const n: int
  constructor (n: int)
    ensures this.n == n
  {
    this.n := n;
  }
}

type SubsetClass = s: SupersetClass | s.n == 10 witness *

method SubsetConstraints() {
  var a: SupersetClass := new SupersetClass(8);
  var b: SupersetClass := new SupersetClass(10);
  var aa: SupersetClass?, bb: SupersetClass? := a, b;
  if
  case true =>
    assert a is SubsetClass; // error
  case true =>
    assert b is SubsetClass;
  case true =>
    assert aa is SubsetClass; // error
  case true =>
    assert bb is SubsetClass;
  case true =>
    var aa: SupersetClass? := null;
    assert aa is SubsetClass; // error
}

type Array = a: array<int> | a.Length == 10 witness *

method SubsetConstraintsArrays() {
  var arr := new int[8];
  var brr := new int[10];
  var aar: array?<int>, bbr: array?<int> := arr, brr;
  if
  case true =>
    assert arr is Array; // error
  case true =>
    assert brr is Array;
  case true =>
    assert aar is Array; // error
  case true =>
    assert bbr is Array;
  case true =>
    var xrr: array?<int> := null;
    assert xrr is Array; // error
}
