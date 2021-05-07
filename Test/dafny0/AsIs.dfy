// RUN: %dafny /compile:0 "%s" > "%t"
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
  case (l as object is K<W>) =>
    var p' := l as object as K<W>; // this works
    assert false; // and so does this
  case (o is B<real, W>) =>
    var b := o as B<real, W>;
  case (o is B<W, int>) =>
    var b := o as B<W, int>;
  case (k as object is B<int, int>) =>
    var b := k as object as B<int, int>;
  case (o is A<W>) =>
    var b := o as A<W>;
  case (k is K<W>) =>
    assert k == k as K<W>;
}
