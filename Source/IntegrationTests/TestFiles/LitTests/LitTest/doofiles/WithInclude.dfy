// RUN: %exits-with 3 %baredafny build %args -t:lib "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "IncludedNotVerified.dfy"

module Consumer {

  import Library

  method Main() {
    Library.Kaboom();
  }
}