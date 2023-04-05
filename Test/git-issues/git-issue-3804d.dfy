// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(i: int)

// labelled assertions within expressions can be revealed later
method {:rlimit 1000} MethodTestNoLeak(x: bool)
  requires r: (x <==> P(12)) && P(12) != P(13)
{
  var result :=
    if x then
      assert p: P(12) by {reveal r;} 12
    else
      assert q: P(13) by {reveal r; } 13;
  reveal q, p;
  assert P(12); // Should fail because we don't know x
  assert P(13); // Should fail because we don't know x
  assert false by { // Succeeds but that's ok, we want to avoid a logic soundness issue
    reveal r;
  }
}

// labelled assertions within expressions can be revealed later
function {:rlimit 1000} FunctionTestNoLeak(x: bool): int
  requires r: (x <==> P(12)) && P(12) != P(13)
{
  var result :=
    if x then
      assert p: P(12) by {reveal r;} 12
    else
      assert q: P(13) by {reveal r; } 13;
  reveal q, p;
  assert P(12); // Should fail because we don't know x
  assert P(13); // Should fail because we don't know x
  assert false by { // Succeeds but that's ok, we want to avoid a logic soundness issue
    reveal r;
  }
  result
}

// labelled assertions within expressions can be revealed later
method {:rlimit 1000} TestDirect(x: bool)
  requires r: (x <==> P(12)) && P(12) != P(13)
{
  var result :=
    if x then
      assert p: P(12) by {reveal r;} 12
    else
      assert q: P(13) by {reveal r; } 13;
  if * {
    assert P(result) by { // Verifies
      reveal p, q;
    }
  } else if * {
    assert P(result) by { // Doesn't verify
      reveal p;
    }
  } else if * {
    assert P(result) by { // Doesn't verify
      reveal q;
    }
  } else if * {
    assert P(result); // Doesn't verify
  } else if * {
    reveal p, q;
    assert P(result); // verifies
  }
}

method {:rlimit 1000} TestConditional(x: bool)
  requires r: (x <==> P(12)) && P(12) != P(13)
{
  var result :=
    if x then
      assert p: P(12) by {reveal r;} 12
    else
      assert q: P(13) by { reveal r; } 13;
  if * {
    if x {
      reveal p;
      assert P(result); // verifies
    }
  } else if * {
    if !x {
      reveal q;
      assert P(result); // verifies
    }
  } else if * {
    if x {
      reveal q;
      assert P(result); // Does not verify
    }
  } else if * {
    if !x {
      reveal p;
      assert P(result); // Does not verify
    }
  } else if * {
    reveal p;
    assert x ==> P(result); // verifies
  } else if * {
    reveal q;
    assert !x ==> P(result); // verifies
  } else if * {
    reveal q;
    assert x ==> P(result); // Does not verify
  } else if * {
    reveal p;
    assert !x ==> P(result); // Does not verify
  }
}