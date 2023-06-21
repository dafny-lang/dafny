// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --spill-translation --unicode-char:false

method Main() {
  print "Hello world\n";
}
