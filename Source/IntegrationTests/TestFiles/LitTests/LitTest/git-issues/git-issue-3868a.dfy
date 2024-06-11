// RUN: %baredafny translate java %args %s --output=%S/git-issue-3868a
// RUN: %OutputCheck --file-to-check %S/git-issue-3868a-java/_System/__default.java "%s"
// CHECK: Let\(

// See comment in git-issue-3868b.dfy

method NotOptimized(s: string) returns (r: int) {
  // We expect the Java compilation of the following line to include some "Let(" calls
  return (var abc := |s|; 3 * abc) + (var xyz := |s|; xyz + xyz);
}
