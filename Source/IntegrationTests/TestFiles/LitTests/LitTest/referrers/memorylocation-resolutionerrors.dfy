// RUN: %resolve --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Test {
  var x: int
  const c: int
}

method TestCaller(t1: Test, t2: Test) {
  ghost var error1 := t1`y; // Error: y not a field of class Test
  ghost var error2 := 3`x; // Error: 3 is not a valid object
  assert set r <- map[t1,t2]`x :: r.0 == {t1, t2};
                 // Error: only references, sets of objects and sequences of objects accepted before a backtick, got map.
  
}