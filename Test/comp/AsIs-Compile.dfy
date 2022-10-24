// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run --no-verify -t=cs %args "%s" >> "%t"
// RUN: %baredafny run --no-verify -t=js %args "%s" >> "%t"
// RUN: %baredafny run --no-verify -t=go %args "%s" >> "%t"
// RUN: %baredafny run --no-verify -t=java %args "%s" >> "%t"
// RUN: %baredafny run --no-verify -t=py %args "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var a: A, b: B, c: C, k: K, l: L := new M, new M, new M, new K<real>, new L<real>;
  var a', b', c', k', l' := AssignBackAndForth(a, b, c, k, l);
  print a == a', " ", b == b', " ", c == c', " ", k == k', " ", l == l', "\n";
  a', b', c', k', l' := AsBackAndForth(a, b, c, k, l);
  print a == a', " ", b == b', " ", c == c', " ", k == k', " ", l == l', "\n";
  IsTests();
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

method IsTests() {
  var p := new ClassP;
  var q := new ClassQ<int>;
  var r, r' := new ClassR<int>, new ClassR';
  var s := new ClassS;
  var t := new ClassT<int>;

  print "IsComparisons ----\n";
  IsComparisons0(q, q, p);
  IsComparisons0(r, r, r);
  IsComparisons0(s, s, s);
  IsComparisons0(q, r, r');
  IsComparisons1(r, t);
  IsComparisons1(r', t);

  print "TestNullIs ----\n";
  TestNullIs(q, q, q, q, q, q);
  TestNullIs(q, null, q, null, q, null);

  print "TestFromTraits ----\n";
  TestFromTraits0(null); // 5
  TestFromTraits1(null); // 0
  var xx := new XX;
  TestFromTraits0(xx); // 4
  TestFromTraits1(xx); // 4
  TestFromTraits2(xx); // 4
  TestFromTraits3(xx); // 4

  // TODO: print "SubsetConstraints ----\n";
  // TODO: SubsetConstraints();
}

trait TraitA<X> { }
trait TraitB<X> { }

class ClassP { }
class ClassQ<Y> extends TraitA<Y> { }
class ClassR<Z> extends TraitA<Z>, TraitB<Z> { }
class ClassS extends TraitA<int> { }
class ClassT<Z> extends TraitA<seq<Z>> { }
class ClassR' extends TraitB<int> { }

method IsComparisons0<U>(au: TraitA<U>, ai: TraitA<int>, o: object) {
  print au as object is ClassP, " ", au is ClassQ<U>, " ", au is ClassR<U>, " ", au as object is ClassS, "\n";
  print "  ", ai is ClassQ<int>, " ", ai is ClassR<int>, " ", ai is ClassS, "\n";
  print "  ", o is ClassP, " ", o is ClassS, "\n";
}

method IsComparisons1<U>(b: TraitB<U>, tz: TraitA<seq<U>>) {
  print b is ClassR<U>, " ", tz is ClassT<U>, "\n";
}

method TestNullIs<U>(o: object, oo: object?, t: TraitA<U>, tt: TraitA?<U>, q: ClassQ<U>, qq: ClassQ?<U>) {
  ghost var checkit := o is TraitA<U> && o is TraitA?<U> && o is ClassQ<U> && o is ClassQ?<U>;
  checkit := oo is TraitA<U> && oo is TraitA?<U> && oo is ClassQ<U> && oo is ClassQ?<U>;
  print o is object, " ", o is object?, "\n";
  print oo is object, " ", oo is object?, "\n";
  print t is object, " ", t is object?, " ", t is TraitA<U>, " ", t is TraitA?<U>, " ", t is ClassQ<U>, " ", t is ClassQ?<U>, "\n";
  print tt is object, " ", tt is object?, " ", tt is TraitA<U>, " ", tt is TraitA?<U>, " ", tt is ClassQ<U>, " ", tt is ClassQ?<U>, "\n";
  print q is object, " ", q is object?, " ", q is TraitA<U>, " ", q is TraitA?<U>, " ", q is ClassQ<U>, " ", q is ClassQ?<U>, "\n";
  print qq is object, " ", qq is object?, " ", qq is TraitA<U>, " ", qq is TraitA?<U>, " ", qq is ClassQ<U>, " ", qq is ClassQ?<U>, "\n";
}

trait XA { }
trait XB { }
trait XC extends XA, XB { }
trait XD extends XC { }
trait XE { }
class XX extends XD { }

method TestFromTraits0(x: XX?) {
  var o: object? := x;
  var c := 0;
  c := c + if o is XA? then 1 else 0;
  c := c + if o is XB? then 1 else 0;
  c := c + if o is XC? then 1 else 0;
  c := c + if o is XD? then 1 else 0;
  c := c + if o is XE? then 1 else 0;
  print c, "\n"; // 5 when x==null, 4 when x!=null
}

method TestFromTraits1(x: XX?) {
  var o: object? := x;
  var c := 0;
  c := c + if o is XA then 1 else 0;
  c := c + if o is XB then 1 else 0;
  c := c + if o is XC then 1 else 0;
  c := c + if o is XD then 1 else 0;
  c := c + if o is XE then 1 else 0;
  print c, "\n"; // 0 when x==null, 4 when x!=null
}

method TestFromTraits2(x: XX) {
  var o: object := x;
  var c := 0;
  c := c + if o is XA? then 1 else 0;
  c := c + if o is XB? then 1 else 0;
  c := c + if o is XC? then 1 else 0;
  c := c + if o is XD? then 1 else 0;
  c := c + if o is XE? then 1 else 0;
  print c, "\n"; // 4
}

method TestFromTraits3(x: XX) {
  var o: object := x;
  var c := 0;
  c := c + if o is XA then 1 else 0;
  c := c + if o is XB then 1 else 0;
  c := c + if o is XC then 1 else 0;
  c := c + if o is XD then 1 else 0;
  c := c + if o is XE then 1 else 0;
  print c, "\n"; // 4
}
/* TODO
class SupersetClass {
  const n: int
  constructor (n: int)
    ensures this.n == n
  {
    this.n := n;
  }
}

type SubsetClass = s: SupersetClass | s.n <= 10 witness *
type SubsetClass' = s: SupersetClass | s.n == 10 witness *
type Array = a: array<int> | a.Length <= 10 witness *
type Array' = a: Array | a.Length >= 10 witness *

method SubsetConstraints() {
  var a: SupersetClass := new SupersetClass(8);
  var b: SupersetClass := new SupersetClass(10);
  print a is SubsetClass, " ", a is SubsetClass', " "; // true false
  print b is SubsetClass, " ", b is SubsetClass', "\n"; // true true
  var aa: SupersetClass?, bb: SupersetClass? := a, b;
  print aa is SubsetClass, " ", aa is SubsetClass', " "; // true false
  print bb is SubsetClass, " ", bb is SubsetClass', "\n"; // true true
  aa, bb := null, null;
  print aa is SubsetClass, " ", aa is SubsetClass', " "; // false false
  print bb is SubsetClass, " ", bb is SubsetClass', "\n"; // false false
  var c: SubsetClass := a;
  print c as SupersetClass is SubsetClass', " "; // false
  c := b;
  print c as SupersetClass is SubsetClass', "\n"; // true

  var arr := new int[8];
  var brr := new int[10];
  print arr is Array, " ", arr is Array', " "; // true false
  print brr is Array, " ", brr is Array', "\n"; // true true
  var aar: array?<int>, bbr: array?<int> := arr, brr;
  print aar is Array, " ", aar is Array', " "; // true false
  print bbr is Array, " ", bbr is Array', "\n"; // true true
  aar, bbr := null, null;
  print aar is Array, " ", aar is Array', " "; // false false
  print bbr is Array, " ", bbr is Array', "\n"; // false false
  var crr: Array := arr;
  print crr is Array', " "; // false
  crr := brr;
  print crr is Array', "\n"; // true
}
*/
