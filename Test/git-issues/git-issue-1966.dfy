// RUN: %dafny /compile:0 /noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// {:compile false}: no error
module {:compile false} {:extern "M"} M1 {}
module {:compile false} {:extern "M"} M2 {}

// {:compile true}: error
module {:extern "P"} P1 {}
module {:extern "P"} P2 {}
