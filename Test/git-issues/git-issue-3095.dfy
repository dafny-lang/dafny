// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

opaque function HasPrecondition(i: int): int
  requires i >= 2
{
  i
}

method TestOnly(i: int, k: int, o1: set<object>, o2: set<object>) returns (j :int)
  requires i >= k
  modifies o1
  ensures j > 1 // Unchecked (postconditions are unchecked if one {:only})
{               // Unchecked
  assert i >= 1;
  var x := HasPrecondition(i);     // Unchecked
  var _ := TestOnly(k, 2, o2, o1); // Unchecked
  assert {:only} i >= 2;           // Checked (proved)
  assert {:only} i >= 3;           // Checked (error)
  while x > 3
    invariant x >= 3               // Unchecked
  {
    x := x + 1;
  }
  assert {:only "Before"} i >= 4 by {  // Unchecked + raise warning because "Before" should be "before"
    assert {:only} i >= 5 by { // Checked (error)
      assert k >= 3;           // Checked (error)
    }
    assert i >= 5;             // Unchecked
  }
  assert i >= 4;               // Unchecked
  assert {:only} i >= 5;       // Checked (error)
}

method TestOnlyAfter(i: int) returns (j :int)
  ensures j >= i // Postconditions are "free" in only mode so they are not tested
{               
  assert i >= 1;                 // Unchecked
  assert i >= 2;                 // Unchecked
  assert {:only "after"} i >= 3; // Checked (error)
  assert i >= 4;                 // Checked (error)
  assert i >= 5;                 // Checked (error)
}

method TestOnlyAfter2(i: int) returns (j :int)
  ensures j >= i // Postconditions are "free" in only mode so they are not tested
{               
  assert i >= 1;                   // Unchecked
  assert {:only} i >= 5 by {       // Unchecked
    assert i >= 2;                 // Unchecked
    assert {:only "after"} i >= 3; // Checked (error)
    assert i >= 4;                 // Checked (error)
  }
  assert i >= 6;                   // Unchecked
}

method TestOnlyBefore(i: int) returns (j :int)
  ensures j >= i
{               
  assert i >= 1;                  // Checked (error)
  assert i >= 2;                  // Checked (error)
  assert {:only "before"} i >= 3; // Checked (error)
  assert i >= 4;                  // Unchecked
  assert i >= 5;                  // Unchecked
}

method TestOnlyBefore2(i: int) returns (j :int)
  ensures j >= i // Postconditions are "free" in only mode so they are not tested
{               
  assert i >= 1;                    // Unchecked
  assert {:only} i >= 5 by {        // Checked (error)
    assert i >= 2;                  // Checked (error)
    assert {:only "before"} i >= 3; // Checked (error)
    assert i >= 4;                  // Unchecked
  }
  assert i >= 6;                    // Unchecked
}

method TestOnlyAfterBefore(i: int) returns (j :int)
  ensures j >= i
{               
  assert i >= 1; // Unchecked
  assert {:only "after"} i >= 2;  // Checked (error)
  assert i >= 3;                  // Checked (error)
  assert {:only "before"} i >= 4; // Checked (error)
  assert i >= 5; // Unchecked
}

method TestOnlyBeforeAfter(i: int) returns (j :int)
  ensures j >= i
{               
  assert i >= 1;                  // Checked (error)
  assert {:only "before"} i >= 2; // Checked (error)
  assert i >= 3;                  // Unchecked
  assert {:only "after"} i >= 4;  // Checked (error)
  assert i >= 5;                  // Checked (error)
}                                 // Checked (error)

method TestOnlyOnlyBefore(i: int) returns (j :int)
  ensures j >= i
{               
  assert i >= 1;                  // Unchecked
  assert {:only} i >= 2;          // Checked (error)
  assert i >= 3;                  // Unchecked
  assert {:only "before"} i >= 4; // Unchecked
  assert i >= 5;                  // Unchecked
  assert i >= 6;                  // Unchecked
}

method TestOnlyBeforeOnlyBefore(i: int) returns (j :int)
  ensures j >= i
{               
  assert i >= 1;                  // Checked (error)
  assert {:only "before"} i >= 2; // Checked (error)
  assert i >= 3;                  // Unchecked
  assert {:only "before"} i >= 4; // Unchecked
  assert i >= 5;                  // Unchecked
  assert i >= 6;                  // Unchecked
}