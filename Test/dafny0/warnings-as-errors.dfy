// RUN: %dafny_0 /compile:0 /print:"%t.print" /dprint:"%t.dprint" /warnShadowing /warningsAsErrors "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
method f(x: int) {
  var x := 0;
}
