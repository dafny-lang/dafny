using DafnyBenchmarkingPlugin;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;

public class BenchmarkInstrumenter : CompilerInstrumenter {
  public override void Instrument(SinglePassCompiler compiler) {
    if (compiler is JavaCompiler javaCompiler) {
      javaCompiler.AddInstrumenter(new JavaBenchmarkInstrumenter());
    } else {
      throw new ArgumentException($"Unsupported compiler: {compiler}");
    }
  }
}