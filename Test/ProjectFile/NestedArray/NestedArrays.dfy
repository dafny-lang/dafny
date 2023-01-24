// RUN: %baredafny %args "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

/* Note, compiling to arrays in Java is difficult. In fact, this is currently
 * broken, see https://github.com/dafny-lang/dafny/issues/3055. Until this gets
 * fixed, Java is omitted from this file.
 *
 * Also, note, these tests mostly check that auto-initialized variables of array
 * types get proper values. Without --relax-definite-assignment (which is
 * our new, planned default), there will still be some way to ask the compiler
 * to generate these values (a plan is to change ":= *" to be evidence for a
 * definite assignments). At that time, the functionality tested in this
 * file will still be needed in the compilers.
 */

method Main() {
  TestDefaultArrayValues<bool>();
  var r: array<array<bool>> := MoreTests();
  print r.Length, "\n"; // 0
}

datatype SingletonRecord = SingletonRecord(a: array<int>)
datatype GenericSingletonRecord<X> = GenericSingletonRecord(x: X)
class MyClass { }

method TestDefaultArrayValues<X>() {
  var arr: array<array<int>>;
  var srr: array<SingletonRecord>;
  var grr: array<GenericSingletonRecord<array<int>>>;
  var xrr: array<array<X>>;

  var arr2: array2<array<int>>;
  var srr2: array2<SingletonRecord>;
  var grr2: array2<GenericSingletonRecord<array<int>>>;
  var xrr2: array2<array<X>>;

  var arr22: array2<array2<int>>;
  var xrr22: array2<array2<X>>;

  var arr12: array<array2<int>>;
  var xrr12: array<array2<X>>;

  var xrr1111: array<array<array<array<X>>>>;
  var xrr1112: array<array<array<array2<X>>>>;
  var xrr1121: array<array<array2<array<X>>>>;
  var xrr1212: array<array2<array<array2<X>>>>;
  var xrr1221: array<array2<array2<array<X>>>>;
  var xrr2212: array2<array2<array<array2<X>>>>;
  var xrr2221: array2<array2<array2<array<X>>>>;
  var xrr2112: array2<array<array<array2<X>>>>;
  var xrr2111: array2<array<array<array<X>>>>;

  var lengths := arr.Length + srr.Length + grr.Length + xrr.Length +
    MLen(arr2) + MLen(srr2) + MLen(grr2) + MLen(xrr2) +
    MLen(arr22) + MLen(xrr22) + arr12.Length + xrr12.Length +
    xrr1111.Length + xrr1112.Length + xrr1121.Length + xrr1212.Length + xrr1221.Length +
    MLen(xrr2212) + MLen(xrr2221) + MLen(xrr2112) + MLen(xrr2111);
  print lengths, "\n"; // 0
}

function method MLen(m: array2): nat {
  m.Length0 + m.Length1
}

method MoreTests<X>() returns (r: array<array<X>>) {
  var a: array<bool>;
  var b: array<X>;
  var c: array<MyClass>;
  
  var e: array<array<bool>>;
  var d: array<array<X>>;
  var f: array<array<MyClass>>;
  
  M(a);
  M(b);
  M(c);
  M(d);
  M(e);
  M(f);

  r := d;
}

method M<X>(arr: array<X>) { }
