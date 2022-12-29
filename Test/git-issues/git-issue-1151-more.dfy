// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:cpp "%s" >> "%t"
// RUN: %exits-with 3 %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
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
