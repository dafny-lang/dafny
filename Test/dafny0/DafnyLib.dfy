// RUN: echo Compiled elsewhere
// This file is part of the test suite. It is compiled by DafnyLibClient.dfy,
// since the DLL from this file is a dependency of DafnyLibClient.

module Library {
  import OpaqueFunctions
  import AutoGhostRegression
  import ExternCode

  method EntryPoint() {
    print "hello from the library\n";

    OpaqueFunctions.IsFive();
    AutoGhostRegression.Q();
    ExternCode.C();
  }
}

module {:extern "ExternCode"} ExternCode {
  method {:extern} C()
}

// ---------- regression tests ---------------

module OpaqueFunctions {
  // At one time, the Dafny program stashed into the DLL as metadata
  // had included the reveal_ functions, which resulted in duplicate-definition
  // errors when the DLL was read back in.
  function {:opaque} Five(): int { 5 }
  lemma IsFive()
    ensures Five() == 5
  {
    reveal Five();
  }
}

module AutoGhostRegression {
  method P() returns (a: int, ghost b: int) {
    a, b := 9, 11;
  }
  method NeedsNonGhost(u: int) {
  }
  method Q() {
    var u, v := P();  // this auto-declares "v" as ghost
    // At one time, the line above would pretty print as
    //     ghost var u, v := P();
    // because _at least_ one of the local variables declared
    // was ghost. That results in Dafny code that won't resolve.
    // Instead, the "ghost" keyword should be printed only when
    // _all_ of the local variables declared are ghost.
    NeedsNonGhost(u);
  }
}
