// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

module SomeDependencyModule {
  datatype None = None
}

module SomeModule {
  import SomeDependencyModule

  const test := SomeDependencyModule.None
}

method Main() {
  print SomeModule.test, "\n";
}