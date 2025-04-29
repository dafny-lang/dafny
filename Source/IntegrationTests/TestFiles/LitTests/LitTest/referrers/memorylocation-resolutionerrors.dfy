// RUN: %resolve --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: int
  const c: int
}

method TestCaller(t1: Test, t2: Test, i: int) {
  ghost var error1 := t1`y; // Error: y not a field of class Test
  ghost var error2 := 3`x; // Error: 3 is not a valid object
  assert set r <- map[t1,t2]`x :: r.0 == {t1, t2};
                 // Error: only references, sets of objects and sequences of objects accepted before a backtick, got map.
  ghost var error3 := t1`[i]; // Error: expected field index like `i, got array index  
}


method TestArray(a: array<int>, c: bool, i: int)
{
  ghost var m := a`[c];// Error: expected int, got bool
  ghost var m := a`c;// Error: expected array index like `[c], got field index
  ghost var m := a`[i, i];// Error: expected only one dimension like a`[i], got 2
}
