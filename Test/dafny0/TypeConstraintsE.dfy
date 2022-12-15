// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Arrays_and_SubsetTypes {
  method M()
  {
    var b: array<int>;
    var n := new nat[100];  // array<nat>
    b := n; // A verification error
  }
}

module Arrays_and_SubsetTypesOK {
  method M()
  { // Type-wise, all of the following are allowed (but the verifier will complain):
    var a: array<nat>;
    var b: array<int>;
    if * {
      a := new nat[100];
    } else if * {
      b := new int[100];
    } else if * {
      var n := new nat[100];  // array<nat>
      if * {
        a := n;
      } else {
        b := n;          // Error
      }
    }
  }
}

