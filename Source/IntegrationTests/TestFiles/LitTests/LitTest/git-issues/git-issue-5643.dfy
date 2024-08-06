// RUN: %testDafnyForEachCompiler "%s"

datatype D = A | B

const c := set d: D | true :: d

datatype {:rust_rc false} E = F | G

const h := set e: E | true :: e

method Main() {
  print |c|, |h|, "\n";
}