// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

blind method ReadsClause() {
  var o := new O;
  var before := Obj(o);
  o.x := 3;
  if (*) {
    assert Obj(o) == before; // passes, because reads clause is never hidden
  } else {
    assert Obj(o) == before by { // passes
      reveal Obj;
    }
  }
}