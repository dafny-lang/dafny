// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t" 

module M {
  export 
  greatest predicate p() { true } // Warning: the greatest goes with the export
}

module N {
  export
    least
  predicate p() { true } // OK
}
