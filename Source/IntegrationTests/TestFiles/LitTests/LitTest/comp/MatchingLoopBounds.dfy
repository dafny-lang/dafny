// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// Dafny breaks the matching loop through j - 1 only in the verifier's translation, so the compiled code enumerates i and
// j with their bounds as written.

method Main() {
  if j: int, i: int :| 0 <= j < 5 && 0 <= i < (j - 1) * (j - 1) + 1 && i * j == 2 {
    print i, " ", j, "\n";
  }
  var s := set x: int {:nowarn} | 0 <= x < 2 && (exists j: int, i: int | 0 <= j < 5 && 0 <= i < (j - 1) * (j - 1) + 1 :: i * j == 2);
  print |s|, "\n";
}
