// RUN: %testDafnyForEachCompiler "%s" -- --main-method:HappyModule.NewMain

method Main() {
  print "not printed";
}

module HappyModule {
  method NewMain() {
    print "printed";
  }
}