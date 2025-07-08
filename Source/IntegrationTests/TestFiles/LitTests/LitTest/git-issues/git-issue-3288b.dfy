// RUN: %exits-with 2 %baredafny verify --show-snippets:false --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t" 

module M {
  export least predicate p[nat]() { true } // error - the 'least' goes with export so the [nat] is illegal for a predicate
}
