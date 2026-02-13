// NONUNIFORM: Testing the initialization of Rust, not relevant to other backends.
// RUN: %baredafny build -t:rs %args  --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Test {
  datatype StringWrapped = String(s: string)

  method StringWrap(name : string) returns (output : StringWrapped) {
    return String("world");
  }

  method PackTupleWithStringWrapped(name : string) returns (output : (string, StringWrapped)) {
    return ("hello", String("world"));
  }
}