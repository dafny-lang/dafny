// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// See comments in Bug125.dfy

module LibA {
  function g(): int { 0 }
}

module LibB {
  function g(): int { 1 }
}

module R {
  import opened LibA
}
/*
module S0 refines R {
  // This module defines a local g().  It takes precedence over the g() that
  // comes from the (inherited) opened import

  // this is no longer possible due to too many potential clashes and generally
  // weird behaviour

  function g(): int { 2 }
  method m() {
    assert g() == 2;
  }
  method n() {
    assert g() == 1;  // error: g() resolves to S0.g(), which returns 2
  }
}

module S1 refines R {
  import opened LibB
  // This module, too, defines a local g().  It takes precedence over the
  // ambiguously imported LibA.g() and LibB.g() that come from opened imports.


  // this is no longer possible due to too many potential clashes and generally
  // weird behaviour

  function g(): int { 3 }

  method m() {
    assert g() == 3;
    assert g() == 0;  // error: g() resolves to S1.g(), which returns 3
  }
}
*/
module V {
  import opened LibA
  function g(): int { 4 }
}

module W refines V {
  method m() {
    assert g() == 4;
    assert g() == 0;  // error: g() resolves to the inherited V.g(), which returns 4
  }
}
