
// RUN: dafny translate java "%s" --plugin:DafnyBenchmarkingPlugin.dll
// RUN: mkdir -p %S/java/src/jmh
// RUN: cp -r %S/SequenceRace-java %S/java/src/jmh/java
// RUN: %S/java/gradlew jmh -p %S/java

class {:benchmark} SequenceRace {

  const s: seq<int>

  constructor() {
    s := [];
    for x := 0 to 1000 {
      s := s + [x];
    }
  }

  method LazyRace() {
    // Using expect means compilers can't optimize calculations away
    // since they could lead to throwing exceptions
    expect 0 < |s|;
    expect s[0] == 0;
  }

}