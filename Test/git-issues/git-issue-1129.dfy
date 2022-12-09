// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:cs "%s" > "%t".abyss
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:java "%s" > "%t".abyss
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" > "%t".abyss
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:go "%s" > "%t".abyss
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:cpp "%s" > "%t".abyss
// RUN: %diff "%s.expect" "%t"

// Without providing extern code for the :extern C, Dafny will output
// target-compiler error messages when asked to compile this program.
// Some of the compilers had then thrown an exception, which caused
// Dafny to crash. That doesn't seem very friendly. The fix is to
// just print the error and exit, without crashing.
//
// Errors reported by the underlying compiler may contain absolute
// path names. These are annoying to have in .expect files. Therefore,
// the output from the Dafny invocations above are piped into the
// abyss. This testing still detects any crash.

module A {
  import B
  datatype D = D(test: B.C)
}

module B {
  class {:extern} C {
    constructor {:extern} (name: string)
  }
}

method Main() {
}
