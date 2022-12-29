// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
  export
    reveals F, G
    provides H

  function F(): int { 5 }
  function {:opaque} G(): int { 5 }
  function H(): int { 5 }

  lemma L0() {
    assert F() == 5;
    assert H() == 5;
  }
  lemma L1() {
    var t := *;
    if {
      case true =>
        assert G() == 5;  // error: G() is opaque
        return;
      case true =>
        reveal G();
        assert G() == 5;
      case true =>
        reveal G();
        t := 2;
      case true =>
        t := 3;
    }
    if t != 3 {
      assert G() == 5;  // fine, since G() has been revealed on this path, or it's known to be 5
    } else {
      assert G() == 5;  // error: G() may not have been revealed
    }
  }
  lemma L2() {
    assert G() == 5;  // error: G() has not yet been revealed
    reveal G();  // revealing afterwards is not good enough
  }
  lemma L3() {
    assert H() == 5;  // yes, definition of H() is known, because we're inside H's defining module
  }
}

module Client {
  import Lib = Library

  lemma L0() {
    assert Lib.F() == 5;  // yes, because F() is not opaque
    assert Lib.G() == 5;  // error: not known, since G() is opaque
  }
  lemma L1() {
    reveal Lib.G();
    assert Lib.G() == 5;  // yes, the definition has been revealed
  }
  lemma L2() {
    assert Lib.H() == 5;  // error: H() is only provided, so its definition is not available
  }
}
