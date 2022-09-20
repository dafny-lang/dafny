// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  print 24 as ORDINAL <= 1507 as ORDINAL, "\n";
}
