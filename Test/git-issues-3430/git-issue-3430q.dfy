// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
   module
}

module B {
  module {:options "--functions-syntax:4"}
}

module C {
  module 
  const c := 6
}
