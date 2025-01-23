using DafnyBenchmarkingPlugin;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;

public class BenchmarkingCompilerInstrumenter(ErrorReporter reporter) : CompilerInstrumenter(reporter) {
  public override void Instrument(IExecutableBackend backend, SinglePassCodeGenerator codeGenerator, Program program) {
    if (codeGenerator is JavaCodeGenerator javaCompiler) {
      javaCompiler.AddInstrumenter(new JavaBenchmarkCompilationInstrumenter(Reporter));
    } else {
      Reporter.Error(MessageSource.Compiler, ResolutionErrors.ErrorId.none, program.GetStartOfFirstFileToken(),
        $"The benchmarking plugin does not support this compilation target: {codeGenerator} (--target:{backend.TargetId})");
    }
  }
}