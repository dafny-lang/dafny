// RUN: %resolve --print:- --reads-clauses-on-methods:false "%s" > "%t"
// RUN: %resolve --print:- --reads-clauses-on-methods:true "%s" >> "%t"
// RUN: %resolve --rprint:- --reads-clauses-on-methods:false "%s" >> "%t"
// RUN: %resolve --rprint:- --reads-clauses-on-methods:true "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Confirming that default reads clauses on methods are not explicitly printed.
// Worth testing because of having to set the default of `reads *` during resolution.

module JustMethods {
  method SomeMethod(x: int) returns (y: int)
    requires true
    modifies {}
    ensures true
    decreases x
  {
    y := x;
  }
}