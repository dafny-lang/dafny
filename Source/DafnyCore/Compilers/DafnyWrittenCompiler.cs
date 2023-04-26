
using Dafny;

namespace Microsoft.Dafny.Compilers {

  public abstract class DafnyWrittenCompiler {
    public DafnyOptions Options { get; }

    public abstract void Compile(ISequence<Rune> program);
    
  }

}