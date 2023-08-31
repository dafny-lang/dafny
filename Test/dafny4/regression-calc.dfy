// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
