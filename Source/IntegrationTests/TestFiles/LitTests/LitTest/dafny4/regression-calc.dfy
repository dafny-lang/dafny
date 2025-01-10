// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// There is a bug in Dafny that causes the error from `L` to be reported at
// position 0 in this file, instead of on a curly brace.

lemma L()
  ensures false {
    calc { true; }
}

// Empty calc statements work fine, though:

lemma L'()
  ensures false {
    calc { }
}
