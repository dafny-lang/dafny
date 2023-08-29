// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment --spill-translation --unicode-char:false

method Main() {
  print "Hello world\n";
}
