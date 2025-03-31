using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

namespace DafnyBenchmarkingPlugin;

public class JavaBenchmarkCompilationInstrumenter : GenericCompilationInstrumenter {

  private readonly ErrorReporter Reporter;

  public JavaBenchmarkCompilationInstrumenter(ErrorReporter reporter) {
    Reporter = reporter;
  }

  public override void BeforeClass(TopLevelDecl cls, ConcreteSyntaxTree wr) {
    if (Attributes.Contains(cls.Attributes, "benchmarks")) {
      wr.WriteLine("@org.openjdk.jmh.annotations.State(org.openjdk.jmh.annotations.Scope.Benchmark)");
    }
  }

  public override void BeforeMethod(MethodOrConstructor m, ConcreteSyntaxTree wr) {
    if (Attributes.Contains(m.EnclosingClass.Attributes, "benchmarks")) {
      if (m is Constructor) {
        if (m.Ins.Any()) {
          Reporter.Error(MessageSource.Compiler, ResolutionErrors.ErrorId.none, m.Origin,
            $"Classes with {{:benchmarks}} can not accept parameters in their constructors");
        }

        // _ctor() needs to be explicitly invoked as usual,
        // and it's convenient (but a bit of a hack) to do this by marking it as Setup.
        // It's not safe in general to run a Dafny compiled constructor
        // multiple times on the same object,
        // so the better solution in the future is probably to maintain the benchmark object
        // as a separate object that Setup instantiates every time.
        wr.WriteLine("@org.openjdk.jmh.annotations.Setup(org.openjdk.jmh.annotations.Level.Iteration)");
      } else if (Attributes.Contains(m.Attributes, "benchmarkTearDown")) {
        if (m.Ins.Any()) {
          Reporter.Error(MessageSource.Compiler, ResolutionErrors.ErrorId.none, m.Origin,
            $"Methods with {{:benchmarkTearDown}} can not accept parameters");
        }
        wr.WriteLine("@org.openjdk.jmh.annotations.TearDown(org.openjdk.jmh.annotations.Level.Iteration)");
      } else {
        wr.WriteLine("@org.openjdk.jmh.annotations.Benchmark");
      }
    }
  }
}
