// RUN: %baredafny build %args -t:lib "%s" --output "%S/WithInclude" > "%t"
// RUN: %exits-with 2 %baredafny run %args "%S/WithInclude.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "IncludedNotVerified.dfy"

module Consumer {

  import Library

  method Main() {
    Library.Kaboom();
  }
}