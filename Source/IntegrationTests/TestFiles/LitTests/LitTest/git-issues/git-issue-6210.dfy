// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny build %args --no-verify -t:cs "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:js "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:cpp "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:java "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:go "%s" >> "%t"
// RUN: %baredafny build %args --no-verify -t:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module Test {
  datatype StringWrapped = String(s: string)

  method PackTupleWithStringWrapped(name : string) returns (output : (string, StringWrapped)) {
    return ("hello", String("world"));
  }
}