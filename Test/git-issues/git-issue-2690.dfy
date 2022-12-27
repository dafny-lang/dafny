// RUN: %dafny -compile:4 -compileTarget:cs "%s" > "%t"
// RUN: %dafny -noVerify -compile:4 -compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method InSeq<T>(ts: seq<T>) returns (f: T --> bool)
  ensures forall t <- ts :: f.requires(t)
{
  ghost var pre := t => t in ts;
  f := t requires pre(t) => true;
}

method InSeq2<T>(ghost ts: seq<T>) returns (f: T --> bool)
  ensures forall t <- ts :: f.requires(t)
{
  f := t requires (ghost var b := t in ts; b) => true;
}

method Main() {
  var f := InSeq([1, 2]);
  print "2 in seq? ", f(2),"\n";
  var g := InSeq2([1, 2]);
  print "2 in seq? ", g(2),"\n";
  print "All right";
}