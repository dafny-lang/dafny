// RUN: %dafny_0 /compile:3 /compileTarget:cs "%s" > "%t"
// RUN: %dafny_0 /compile:3 /compileTarget:java "%s" >> "%t"
// RUN: %dafny_0 /compile:3 /compileTarget:js "%s" >> "%t"
// RUN: %dafny_0 /compile:3 /compileTarget:go "%s" >> "%t"
// RUN: %dafny_0 /compile:3 /compileTarget:cpp "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// The following example should produce a compilation error, since there's
// an opaque type. It should not, however, crash.

type Opaque(0) // compilation error: this is an opaque type

datatype E = E(Opaque)

method N() returns (e: E) {
}

method Main() {
  var e := N();
  print e, "\n";
}
