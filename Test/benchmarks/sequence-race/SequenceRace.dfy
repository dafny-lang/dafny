
// Ensure trying to use an unsupported compilation target results in a clean error message.
// RUN: %exits-with 3 %baredafny translate cs %args "%s" --plugin:DafnyBenchmarkingPlugin.dll > "%t"
// RUN: %diff "%s.expect" "%t"

// RUN: %baredafny translate java %args "%s" --plugin:DafnyBenchmarkingPlugin.dll
// RUN: mkdir -p %S/java/src/jmh
// RUN: cp -r %S/SequenceRace-java %S/java/src/jmh/java

// Note the intentional ">" as opposed to ">>", so we can check just the benchmark run output.
// RUN: %S/java/gradlew jmh -p %S/java > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// We manually verify the benchmark fails (since the bug isn't fixed yet), because unfortunately
// we can't trust the JMH gradle plugin to: https://github.com/melix/jmh-gradle-plugin/issues/255
// CHECK: <failure>

//
// Sanity test of the benchmarking plugin,
// and a regression test for https://github.com/dafny-lang/dafny/issues/1454.
//
// A class with {:benchmarks} will be translated to a form that target language
// benchmarking frameworks can integrate with relatively easily.
// For each method on such classes,
// a single instance of the class will be instantiated using the no-argument constructor,
// and then one or more concurrent executions of the method will be triggered.
// 
class {:benchmarks} SequenceRace {

  const s: seq<int>

  constructor() {
    s := [];
    for x := 0 to 1000 {
      s := s + [x];
    }
  }

  method LazyRace() {
    // Using expect means compilers can't optimize calculations away
    // since they could lead to throwing exceptions.
    expect 0 < |s|;
    expect s[0] == 0;
  }

}