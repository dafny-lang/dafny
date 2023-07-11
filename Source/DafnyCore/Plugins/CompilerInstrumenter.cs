using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny.Plugins; 

// A hook for plugins to customize some of the code generation of other ExecutableBackends.
public abstract class CompilerInstrumenter {
  public virtual void Instrument(SinglePassCompiler compiler) {
  }
}