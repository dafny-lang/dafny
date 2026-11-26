// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma BadAfterRequires(lo: int, to: int)
  requires lo <= to
  decreases to - lo
  ensures false
{}

lemma BadAfterEnsures(lo: int, to: int)
  requires lo <= to
  ensures false
  decreases to - lo
{}
