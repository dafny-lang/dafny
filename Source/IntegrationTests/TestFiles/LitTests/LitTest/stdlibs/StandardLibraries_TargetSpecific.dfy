// This test just asserts what happens when you try to use a library
// that isn't available for all backends (see .check files).
// Full testing of such libraries is handled in the DafnyStandardLibraries
// project rather than here.

// RUN: %testDafnyForEachCompiler "%s" -- --standard-libraries:true

module UsesFileIO {
  import Std.FileIO
}
