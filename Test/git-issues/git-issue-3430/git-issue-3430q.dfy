// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
   module
}

module B {
  module {:options "--function-syntax:4"}
}

module C {
  module 
  const c := 6
}

// Checks for OK behavior if module name is missing
