// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Note: in the tests below, it could be useful to experiment with the
// following triggers for some of the library axioms:
//
// axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
//   { Seq#Contains(s0, x), Seq#Append(s0, s1) }
//   { Seq#Contains(s1, x), Seq#Append(s0, s1) }
//   Seq#Contains(Seq#Append(s0, s1), x)
//      <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));
//
// axiom (forall<T> s: Seq T, v: T, x: T ::
//   { Seq#Contains(s, x), Seq#Build(s, v) }
//   Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));
//
// Another, not necessarily incompatible approach would be to explicitly add
// `assume k in s` for each element k of constant lists.

method SmallList0() {
  var s := [0, 1, 5, 6];
  // This fails: Dafny needs a hint here, because the triggers on the library axioms are pretty strict:
  assert exists n :: n in s; // WISH
}

method SmallList1() {
  var s := [0, 1, 5, 6];
  // This works
  assert 0 in s;
  assert exists n :: n in s;
}

method SmallList2() {
  var s := [0, 1, 5, 6];
  // This also works, thanks to the magic of triggering on `$Box`.
  assert exists n {:autotriggers false} :: n in s;
}

method LargeList0() {
  var s := [0, 1, 2, 3, 4, 5, 6, 7, 8, /* 9, 10, 11, */ 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, /* 119, 120, 121, */ 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136];

  // The hint fails here. Maybe because z3 gets into a loop trying to unwrap
  // this large list? This is also very slow.
  assert 0 in s; // WISH
  assert exists n :: n in s;
}

method LargeList1() {
  var s := [0, 1, 2, 3, 4, 5, 6, 7, 8, /* 9, 10, 11, */ 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, /* 119, 120, 121, */ 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136];

  // Strangely, the hint works here. Why?
  assert 122 in s;
  assert exists n :: n in s;
}

method LargeList2() {
  var s := [0, 1, 2, 3, 4, 5, 6, 7, 8, /* 9, 10, 11, */ 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, /* 119, 120, 121, */ 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136];

  // This also fails; since z3 only goes to a depth of 100, this probably
  // wouldn't work with relaxed triggers eithers
  assert exists n :: n in s && n >= 120;
}

method LargeList3() {
  var s := [0, 1, 2, 3, 4, 5, 6, 7, 8, /* 9, 10, 11, */ 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, /* 119, 120, 121, */ 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136];

  // This works: this is certainly more `triggering-on-$Box` magic, but I'm
  // not sure exactly how it works
  assert exists n {:autotriggers false} :: n in s && n >= 120;
}

method LargeList4() {
  var s := [0, 1, 2, 3, 4, 5, 6, 7, 8, /* 9, 10, 11, */ 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, /* 119, 120, 121, */ 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136];

  // `$Box` only offers limited solace, though
  assert exists n {:autotriggers false} :: n in s && n < 3;  // reports error
}
