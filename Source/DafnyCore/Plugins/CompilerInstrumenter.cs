using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny.Plugins; 

/// <summary>
/// A hook for plugins to customize some of the code generation of other IExecutableBackends.
/// </summary>
public abstract class CompilerInstrumenter : ErrorReportingBase {

  public CompilerInstrumenter(ErrorReporter reporter) : base(reporter) { }

  /// <summary>
  /// Instrument the given compiler.
  /// 
  /// Unlike with Rewriters, there is less consistent structure
  /// to the implementation of the various compilers.
  /// Therefore there isn't a single generic interface for instrumentation support
  /// for an arbitrary SinglePassCompiler subclass.
  /// CompilerInstrumenters will generally want to check for known subtypes
  /// and downcast to interface with them,
  /// possibly reporting an error if they don't recognize the compiler.
  /// </summary>
  public virtual void Instrument(IExecutableBackend backend, SinglePassCompiler compiler, Program program) {
  }
}