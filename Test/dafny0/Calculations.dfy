// RUN: %exits-with 4 %baredafny verify %args --print="%t.dprint.dfy" "%s" > "%t"
// RUN: %baredafny resolve "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

method CalcTest0(s: seq<int>) {
  calc {
    s[0]; // error: ill-formed line
  }

  calc {
    2;
    { assert s[0] == 1; } // error: ill-formed hint
    1 + 1;
  }

  if (|s| > 0) {
    calc {
      s[0]; // OK: well-formed in this context
      <= { assert s[0] == s[0]; }
      s[0];
    }
  }
  assume forall x :: x in s ==> x >= 0;
  calc {
    0 < |s|;
  ==>  { assert s[0] in s && s[0] >= 0; }  // OK: well-formed after previous line
    s[0] >= 0;                // OK: well-formed after previous line
  <==> { assert s[0] in s && s[0] >= 0; }  // OK: well-formed when the previous line is well-formed
    s[0] > 0 || s[0] == 0;    // OK: well-formed when the previous line is well-formed
  }

  calc { // same as the last one, but well-formedness is checked in reverse order
    s[0] + 1 > 0;
  <==>
    s[0] >= 0;
  <== { assert s[0] >= 0; }
    0 < |s|;
  }
}

method CalcTest1(x: int, y: int) {
  calc {
    x + y;
    { assume x == 0; }
    y;
  }
  assert x == 0; // OK: follows from x + y == y;
}

method CalcTest2(x: int, y: int) {
  calc {
    x + y;
    { assume x == 0; }
    y + x;
  }
  assert x == 0; // error: even though assumed above, is not exported by the calculation
}

// calc expression:
function CalcTest3(s: seq<int>): int {
  calc < {
    0;
    { assume |s| == 5; }
    |s|;
  }
  s[0]
}

// dangling hints:
method CalcTest4(s: seq<int>)
  requires forall n | n in s :: n > 0;
{
  calc {
    1 + 1;
    { assert 1 + 1 == 2; }
  }
  calc {
    2;
    { assert s[0] > 0; } // error: ill-formed hint
  }
  calc {
    |s| > 0;
  ==> { assert s[0] in s && s[0] > 0; } // okay
  }

}

// ------------- tests for the pretty printer -------------

lemma CalcPrinting()
{
  calc < {
    2;
  <= { SubLemma(); }
    3;
    5;
  < { assert 5 < 6 <= 5+1; SubLemma(); assert 6 < 7; }
    7;
    11;
    { SubLemma(); } // dangling hint
  }
  calc < {
    13;
  }
  calc {
    17;
  == { SubLemma(); }  // dangling hint, following operator
  }
  calc <= {
    19;
  <=
    { SubLemma(); }
    { assert 19 + 23 == 42; }
    calc { 811; }
    { assert 42 < 100; }
    23;
    { calc < {
      71; { assert 71 % 19 != 0; } 73;
    } }
    29;
    calc < {
      311; 313; 331;
    }
    31;
  }
  calc {
  }
}

lemma SubLemma()
