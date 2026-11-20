// RUN: %testDafnyForEachCompiler "%s" -- --main-method:HappyModule.NewMain --spill-translation --enforce-determinism

method Main() {
  print "not printed";
}

module HappyModule {
  method NewMain() {
    print "printed";
  }
}