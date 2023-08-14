// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Crash {
  export Body
    reveals *

  datatype Sort =
    | Int
    | Re
 
  datatype Func =
    | ReUnion
    | ReLoop {

      predicate wellFormedFunction(args: seq<Sort>) {
        match this {
          case ReUnion => (forall arg | arg in args :: arg.Re?)
          case _ => false
        }
      }

    }
}