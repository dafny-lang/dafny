// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var data: int

  method ResolutionIssues()
    requires old(data) == 3 // error: 'old' not allowed in this context
    requires calc { 0; { var d := old(data); } 0; } true // error: 'old' not allowed in this context
  {
    var a := old(5 + old(data)); // error: 'old' not allowed inside another 'old

    var b := 5 +
      calc {
        0;
      ==  { var a := old(data); }
        0;
      }
      0;

    var c := old(5 +
      calc {
        0;
      ==  { var a := old(data); } // error: 'old' not allowed inside another 'old
        0;
      }
      0
      );
  }

  method CallTwostate(u: int)
    requires F2(u) == u // error: twostate function not allowed in this context
    requires calc {
        0;
      ==  { assert F2(u) == u; } // error: twostate function not allowed in this context
        0;
      }
      true
  {
    var a := old(5 + F2(u)); // error: twostate function not allowed inside 'old

    var b := 5 +
      calc {
        0;
      ==  { var a := F2(u); }
        0;
      }
      0;

    var c := old(5 +
      calc {
        0;
      ==  { var a := F2(u); } // error: twostate function not allowed inside 'old
        0;
      }
      0
      );
  }

  ghost function F(u: int): int {
    5 +
    assert F2(u) == u; // error: twostate function not allowed in this context
    u
  }

  twostate function F2(u: int): int {
    u
  }
}
