// This test just asserts what happens when you try to use a library
// that isn't available for all backends.
// Full testing of such libraries is handled in the DafnyStandardLibraries
// project rather than here.

// Valid:

// RUN: %verify --standard-libraries:true "%s" > "%t"
// RUN: %run --target:cs --standard-libraries:true "%s" >> "%t"
// RUN: %run --target:java --standard-libraries:true "%s" >> "%t"
// RUN: %run --target:go --standard-libraries:true "%s" >> "%t"
// RUN: %run --target:js --standard-libraries:true "%s" >> "%t"
// RUN: %run --target:py --standard-libraries:true "%s" >> "%t"

// Invalid:

// RUN: %exits-with 2 %run --target:cpp --standard-libraries:true "%s" >> "%t"
// RUN: %exits-with 2 %run --target:rs --standard-libraries:true "%s" >> "%t"

// RUN: %diff "%s.expect" "%t"

module UsesFileIO {

  import DafnyStdLibs.FileIO

  method Main() {
    var thisFile :- expect FileIO.ReadBytesFromFile("StandardLibraries_TargetSpecific.dfy");
  }
}
