// RUN: %baredafny run %args "%s" --main-method=HappyModule.NewMain > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "not printed";
}

module HappyModule {
  method NewMain() {
    print "printed";
  }
}