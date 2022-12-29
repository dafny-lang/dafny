// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

predicate method P(s: set)
  requires s != {}
{
  // In the following line, the let-such-that is compiled by TrExprOpt
  var e :| e in s;
  e == e
}

function method F(s: set): int
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
