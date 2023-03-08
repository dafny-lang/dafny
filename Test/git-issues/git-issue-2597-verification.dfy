// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var data: int

  lemma DataIs(x: int)
    requires data == x
  {
  }

  method VerificationIssues()
    requires data == 3
    modifies this
  {
    data := 100;
    ghost var x, y;
    x := old(5 + assert data == 3; 0);
    y := old(5 + (DataIs(3); 0));
    assert x + y == 10;

    x := 5 +
      calc {
        0;
      ==  { DataIs(100); }
        0;
      ==  { DataIs(3); } // error: precondition violation
        0;
      }
      0;
    y := old(5 +
      calc {
        0;
      ==  { DataIs(3); }
        0;
      ==  { DataIs(100); } // error: precondition violation
        0;
      }
      0);
    assert x + y == 10;

    x := 5 +
      assert data == 100 by {
        DataIs(100);
        if * {
          DataIs(3); // error: precondition violation
        }
      }
      0;
    y := old(5 +
      assert data == 3 by {
        DataIs(3);
        if * {
          DataIs(100); // error: precondition violation
        }
      }
      0);
    assert x + y == 10;

    DataIs(100); // this tests that the $Heap once again is the current one
    assert false; // error: this statement is reachable
  }

  ghost function {:opaque} OpaqueData(x: int): int
    reads this
  {
    x + data
  }

  method Reveal(x: int)
  {
    if
    case true =>
      reveal OpaqueData();
      assert OpaqueData(x) == x + data;
    case true =>
      assert OpaqueData(x) == x + data; // error: cannot prove, since OpaqueData is opaque
    case true =>
      assert reveal OpaqueData(); OpaqueData(x) == x + data;
    case true =>
      reveal OpaqueData();
      assert old(OpaqueData(x)) == x + old(data);
    case true =>
      assert old(OpaqueData(x)) == x + old(data); // error: cannot prove, since OpaqueData is opaque
    case true =>
      assert old(reveal OpaqueData(); OpaqueData(x)) == x + old(data);
  }

  method Postconditions()
    requires data == 3
    modifies this
    ensures old(97 +
      calc {
        0;
      ==  { DataIs(3); }
        0;
      ==  { DataIs(100); } // error: precondition violation
        0;
      }
      data) == data
  {
    data := 100;

    var arr := new int[100](i => 8);
    forall i | 0 <= i < arr.Length
      ensures arr[i] == old(5 +
        calc {
          0;
        ==  { DataIs(3); }
          0;
        ==  { DataIs(100); } // error: precondition violation
          0;
        }
        data)
    {
    }

    for i := 0 to arr.Length
      invariant forall j :: 0 <= j < i ==> arr[j] == old(6 +
        calc {
          0;
        ==  { DataIs(3); }
          0;
        ==  { DataIs(100); } // error: precondition violation
          0;
        }
        data)
      invariant forall j :: i <= j < arr.Length ==> arr[j] == old(5 +
        calc {
          0;
        ==  { DataIs(3); }
          0;
        ==  { DataIs(100); } // error: precondition violation
          0;
        }
        data)
      modifies arr
    {
      arr[i] := arr[i] + 1;
    }
  }
}
