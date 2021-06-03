// RUN: %dafny /print:"%t.print" /dprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype CheckRussell = ISet(s: iset<CheckRussell>)  // error: - recursive mentions must be used in a strict (and covariant) context

lemma russell_paradox()
ensures false
{
  var t := ISet(iset t: CheckRussell | t !in t.s );
  assert t in t.s;
  assert t !in t.s;
}
