// NONUNIFORM: tests the lib target specifically
// Building a library from code that uses target-dependent standard-library modules
// (https://github.com/dafny-lang/dafny/issues/6485): the lib target loads the
// target-agnostic standard library, and the produced .doo defers the choice of
// target-specific implementation to the eventual concrete compilation.
// RUN: %build -t=lib --standard-libraries:true "%S/Inputs/usesFileIO.dfy" --output "%S/Output/usesFileIO" > "%t"
// RUN: %run -t=cs --standard-libraries:true "%s" --input "%S/Output/usesFileIO.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"
module LibBuildMain {
  import UsesFileIO

  method Main()
    decreases *
  {
    UsesFileIO.WriteGreeting("greeting.txt");
    print "wrote greeting\n";
  }
}
