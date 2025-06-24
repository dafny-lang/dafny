// RUN: %verify --referrers --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


class SimpleObject {
}

///// Local fields and input parameters

method ReferrersLocal() {
  var t := new SimpleObject;
  assert referrers(t) == {locals`t};
  var alias_t := t;
  assert referrers(t) == {locals`t, locals`alias_t};
  label before_t_null:
  t := null;
  assert referrers(alias_t) == {locals`alias_t};
  assert old@before_t_null(referrers(alias_t)) == {locals`t, locals`alias_t};
  
  // Arrays too have referrers
  var u := new SimpleObject?[1](i => null);
  assert referrers(u) == {locals`u};
}

method ReferrersMethodCall(t: SimpleObject)
{
  assert locals`t in referrers(t);
}

// Input parameters are not unassigned when the method exits.
// However, local variables in scope are unassigned before a return
method EnsuresReferrersUnchanged(t2: SimpleObject)
  ensures old(referrers(t2)) == referrers(t2)
{
  var t_local := t2;
  assert old(referrers(t2)) == old(referrers(t_local)); // Local variables don't depend on any heap so they can be used in old expressions
  assert referrers(t2) == old(referrers(t2)) + {locals`t_local};
  return; // Here t_local is unassigned.
}

method CallReferrersMethodCall() {
  var t := new SimpleObject;
  assert referrers(t) == {locals`t};
  EnsuresReferrersUnchanged(t); // Here t2 is added to the referrers, then the referrers are assumed to not be changed, and t2 is unassigned.
  assert referrers(t) == {locals`t};
}

//// Ghost versions are the same //////

ghost method GhostReferrersLocals() {
  ghost var t := new SimpleObject; // Ghostly allocated
  assert referrers(t) == {};
  ghost var alias_untracked := t;    // Even in ghost context, ghost markers means non-tracking by default.
  assert referrers(t) == {};
  ghost var {:tracking} alias_tracked := t; // This is not useful in practice in ghost methods since one can just declare normal variables, but it's here for coherence
  assert referrers(t) == {locals`alias_tracked};
  
  assert (locals`t.1).IsGhost;
  assert (locals`alias_untracked.1).IsGhost;
  assert (locals`alias_tracked.1).IsGhost;
}

method ReferrersLocalWithGhostAliases() {
  var t := new SimpleObject;
  assert referrers(t) == {locals`t};
  ghost var alias_untracked := t;    // Ghost variables, like ghost fields, are non-tracking by default.
  assert referrers(t) == {locals`t};
  ghost var {:tracking} alias_tracked := t; // To make a ghost variable tracking, one must force it.
  assert referrers(t) == {locals`t, locals`alias_tracked};
  
  assert !(locals`t.1).IsGhost;
  assert (locals`alias_untracked.1).IsGhost;
  assert (locals`alias_tracked.1).IsGhost;
}


method ReferrersOnGhostConstructedInstanceInCompiledContext() {
  ghost var t := new SimpleObject; // Automatically marked as tracking when the RHS
  assert referrers(t) == {};
  ghost var alias_untracked := t;    // Ghost variables, like ghost fields, are non-tracking by default.
  assert referrers(t) == {};
  ghost var {:tracking} alias_tracked := t; // To make a ghost variable tracking, one must force it.
  assert referrers(t) == {locals`alias_tracked};
  
  assert (locals`t.1).IsGhost;
  assert (locals`alias_untracked.1).IsGhost;
  assert (locals`alias_tracked.1).IsGhost;
}


///// Object fields and object constants

class ChainingObject {
  var x: ChainingObject?
  var y: ChainingObject?
  ghost var nontracking: ChainingObject?
  ghost var {:tracking} tracking: ChainingObject?
  const tail: ChainingObject?
  constructor(chained_test: ChainingObject?) ensures x == y == nontracking == tracking == null && tail == chained_test
    ensures chained_test != null ==> referrers(chained_test) == old(referrers(chained_test)) + {this`tail}
    ensures forall o: object | o != chained_test :: referrers(o) == old(referrers(o)) // Replace by referrers clauses when they arrive
  {
    x := null;
    y := null;
    tracking := null;
    nontracking := null;
    tail := chained_test;
  }
}

// Ghost parameters are untracking by default
lemma CouldFree(t: object, compiledMemRef: (object, field))
  requires forall r: (object, field) <- referrers(t) :: !r.1.IsGhost ==> r == compiledMemRef

method ObjectFields() {
  var t := new ChainingObject(null);
  assert referrers(t) == {locals`t};
  t.x := t;
  assert referrers(t) == {locals`t, t`x};
  t.y := t;
  assert referrers(t) == {locals`t, t`x, t`y};
  t.x := null;
  assert referrers(t) == {locals`t, t`y};
  t.y := null;
  assert referrers(t) == {locals`t};
  t.tracking := t; // Ghost assignment
  assert referrers(t) == {locals`t, t`tracking};
  t.tracking := null;
  assert referrers(t) == {locals`t};
  t.nontracking := t;
  assert referrers(t) == {locals`t};  
  CouldFree(t, locals`t);
  
  var u := new ChainingObject(t);
  assert referrers(u) == {locals`u};
  assert referrers(t) == {locals`t, u`tail};
  u.x := t;
  assert referrers(t) == {locals`t, u`tail, u`x};
  assert referrers(u) == {locals`u};
  u.x := u; // Double change
  assert referrers(t) == {locals`t, u`tail};
  assert referrers(u) == {locals`u, u`x};
  
  // Assignment of array
  label before:
  var a := new ChainingObject[3](i => if i == 0 then t else u);
  assert a[0] == t;
  assert a`[0] in referrers(t) - old@before(referrers(t));
  assert a`[1] !in referrers(t) - old@before(referrers(t));
  assert a`[2] !in referrers(t) - old@before(referrers(t));
  assert a`[0] !in referrers(u) - old@before(referrers(u));
  assert a`[1] in referrers(u) - old@before(referrers(u));
  assert a`[2] in referrers(u) - old@before(referrers(u));
  assert forall r: (object, field) <- referrers(t) - old@before(referrers(t)) :: r == a`[0];
  //assert referrers(t) == {locals`t, u`tail, a`[0]};
  //assert referrers(u) == {locals`t, u`x, a`[1], a`[2]};
}