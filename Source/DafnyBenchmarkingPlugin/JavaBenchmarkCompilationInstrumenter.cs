using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

namespace DafnyBenchmarkingPlugin;

public class JavaBenchmarkCompilationInstrumenter : GenericCompilationInstrumenter {

  public override void BeforeClass(TopLevelDecl cls, ConcreteSyntaxTree wr) {
    if (Attributes.Contains(cls.Attributes, "benchmark")) {
      wr.WriteLine("@org.openjdk.jmh.annotations.State(org.openjdk.jmh.annotations.Scope.Benchmark)");
    }
  }

  public override void BeforeMethod(Method m, ConcreteSyntaxTree wr) {
    if (Attributes.Contains(m.EnclosingClass.Attributes, "benchmark")) {
      // TODO: Only do this for the default no-arg constructor.
      // TODO: Have a rewriter reject any other constructors?
      if (m is Constructor) {
        // _ctor() needs to be explicitly invoked as usual,
        // and it's convenient (but a hack) to do this by marking it as Setup
        // TODO: Anything other than the "Benchmark" level isn't actually sound,
        // because it's not safe in general to run a Dafny compiled constructor
        // multiple times on the same object.
        // The solution is probably to maintain the benchmark object
        // as a separate object that Setup instantiates every time.
        wr.WriteLine("@org.openjdk.jmh.annotations.Setup(org.openjdk.jmh.annotations.Level.Iteration)");  
      } else {
        wr.WriteLine("@org.openjdk.jmh.annotations.Benchmark");  
      }
    }
  }
}
