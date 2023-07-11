
// RUN: dafny translate java "%s" --plugin:DafnyBenchmarkingPlugin.dll
// RUN: mkdir -p %S/java/src/jmh
// RUN: cp -r %S/SequenceRace-java %S/java/src/jmh/java
// RUN: %S/java/gradlew jmh -p %S/java

// TODO: Should expect the gradle build to fail since the bug is still present,
// but even with failOnError.set(true) it doesn't... :(

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