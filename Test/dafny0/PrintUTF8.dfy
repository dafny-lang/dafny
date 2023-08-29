// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment

method Main() {
  print "Mikaël fixed UTF8\n";
}
