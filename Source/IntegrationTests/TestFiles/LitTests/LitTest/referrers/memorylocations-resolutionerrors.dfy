// RUN: %exits-with 2 %resolve --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: int
  const c: int
  static const s: int
  function f(): int { 0 }
}

method TestCaller(t1: Test, t2: Test, a: array<int>, i: int) {
  ghost var error1 := t1`y; // Error: y not a field of class Test
  ghost var error2 := 3`x; // Error: 3 is not a valid object
  assert (set r: Test <- map[t1 := 1,t2 := 2]`x :: r) == {t1, t2};
                 // Error: only references, sets of objects and sequences of objects accepted before a backtick, got map.
  ghost var error3 := t1`[i]; // Error: expected field index like`i, got array index  
  ghost var error4 := t1`f; // Error: Expected constant or mutable field reference, but got function
  ghost var error5 := t1`s; // Error: static fields are not memory locations
}

method TestArray(a: array<int>, c: bool, i: int)
{
  ghost var m := a`[c];// Error: expected int, got bool
  ghost var m1 := a`i;// Error: expected array index like `[i]
  ghost var m2 := a`[i, i];// Error: expected only one dimension like a`[i], got 2
}
