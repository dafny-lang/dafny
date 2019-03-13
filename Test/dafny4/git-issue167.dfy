// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The problem reported in issue 167 has not yet been fixed. However, an improvement that
// happens to avoid the problem in some cases has been implemented. The tests below
// test that behavior.

function method Rewrite(env: map<nat, nat>): map<nat, nat> {
  var p := map g: nat | g in env :: g;  // regression test: used to produce malformed Boogie
  map n: nat | n in p :: n
}

function method Rewrite_Keys(env: map<nat, nat>): map<nat, nat> {
  var p := env.Keys;  // this is an easier way to assign p like in Rewrite
  map n: nat | n in p :: n
}

function method Rewrite2(strs: set<string>): map<string, string> {
  var p := map g: string | g in strs :: g;  // regression test: used to produce malformed Boogie
  map s: string | s in p :: s
}

method Main() {
  var m := map[6 := 8, 7 := 3];
  var n := Rewrite(m);
  assert m.Keys == n.Keys;
  print n.Keys, "\n";

  var u := {"Alfons", "Milla"};
  var v := Rewrite2(u);
  assert u == v.Keys;
  print v.Keys, "\n";
}


/*
function sum(a: int, b: int): int {
  a + b
}

predicate sum_is_sum(b: int, c: int) {
  var s := a => sum(a, b);
  forall a: int :: s(a) + c == a + b + c
}
*/
