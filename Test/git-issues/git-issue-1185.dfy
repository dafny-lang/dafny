// NONUNIFORM: https://github.com/dafny-lang/dafny/issues/4108
// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

predicate P(s: set)
  requires s != {}
{
  // In the following line, the let-such-that is compiled by TrExprOpt
  var e :| e in s;
  e == e
}

function F(s: set): int
  requires s != {}
{
  var p :=
    // In the following line, the let-such-that is compiled by TrExpr
    var e :| e in s;
    e == e;
  if p then 6 else 8
}

method Main() {
  var s := {12, 20};
  var b := P(s);
  var x := F(s);
  print s, " ", b, " ", x, "\n";
}
