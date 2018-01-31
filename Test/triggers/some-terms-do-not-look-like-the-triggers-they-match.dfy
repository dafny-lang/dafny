// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file shows how Dafny detects loops even for terms that are not literal
// AST matches. This file also checks that triggers are reported exactly as
// picked (that is, `x in s` yields `s[x]` for a multiset s), but matches as
// they appear in the buffer text (that is, `x+1 in s` is not translated to
// s[x+1] when highlited as a cause for a potential matching loop.

method M() {
  // This is an obvious loop
  ghost var b := forall s: multiset<int>, x: int :: s[x] > 0 ==> s[x+1] > 0;

  // x in s loops with s[x+1] due to the way [x in s] is translated
  ghost var a := forall s: multiset<int>, x: int :: x in s ==> s[x+1] > 0 && x+2 !in s;
}
