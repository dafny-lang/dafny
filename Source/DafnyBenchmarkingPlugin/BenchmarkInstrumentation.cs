using DafnyBenchmarkingPlugin;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;

public class BenchmarkingCompilerInstrumenter : CompilerInstrumenter {
  public BenchmarkingCompilerInstrumenter(ErrorReporter reporter) : base(reporter) { }

  public override void Instrument(IExecutableBackend backend, SinglePassCompiler compiler, Program program) {
    if (compiler is JavaCompiler javaCompiler) {
      javaCompiler.AddInstrumenter(new JavaBenchmarkCompilationInstrumenter(Reporter));
    } else {
      Reporter.Error(MessageSource.Compiler, ResolutionErrors.ErrorId.none, program.GetFirstTopLevelToken(),
        $"The benchmarking plugin does not support this compilation target: {compiler} (--target:{backend.TargetId})");
    }
  }
}