// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --unicode-char:false

method Main() {
  print "Hello world\n";
}
