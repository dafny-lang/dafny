// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  print apply(i => i + 1, 5), "\n";
  print mapply(map[5 := 6], 5), "\n";
  var f: int -> int;
  print five(f), "\n";
}

// -----
// test that the definition axiom for function "apply" is available

function apply(f:int~>int, a:int): int
  reads f.reads
  requires f.requires(a)
{
  f(a)
}

lemma TestPost()
  ensures apply(i => i + 1, 5) == 6
{
}

lemma M() {
  assert apply(i => i + 1, 5) == 6;
}

lemma TestPre()
  requires apply(i => i + 1, 5) == 6
{
}

lemma TestPreCaller()
{
  TestPre();
}

// -----
// test that the above thing for arrows also works for maps

function mapply(m: map<int,int>, a:int): int
  requires a in m
{
  m[a]
}

lemma TestMPost()
  ensures mapply(map[5 := 6], 5) == 6
{
}

lemma N() {
  assert mapply(map[5 := 6], 5) == 6;
}

// -----
// test that g's result is known to be $Is'ed and $IsAlloc'ed

function five(f:int->int): int { 5 }

lemma P() {
  var f := i => i + 1;
  assert five(f) == 5;
}

lemma Q(g: real->int->int)
  requires g.requires(0.0)
{
  var f := g(0.0);
  assert five(f) == 5;
}
