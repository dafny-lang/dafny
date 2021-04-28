// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var a: A, b: B, c: C, k: K, l: L := new M, new M, new M, new K<real>, new L<real>;
  var a', b', c', k', l' := AssignBackAndForth(a, b, c, k, l);
  print a == a', " ", b == b', " ", c == c', " ", k == k', " ", l == l', "\n";
  a', b', c', k', l' := AsBackAndForth(a, b, c, k, l);
  print a == a', " ", b == b', " ", c == c', " ", k == k', " ", l == l', "\n";
}

trait A<X> { }
trait B<Y0, Y1> { }
trait C<Z> extends B<int, Z> { }

class K<U> extends object, B<int, U> { }
class L<V> extends C<V> { }
class M extends A<real>, C<real> { }

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

