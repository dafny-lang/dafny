
using Dafny;

namespace Microsoft.Dafny.Compilers {

  public abstract class DafnyWrittenCompiler {

    public abstract ISequence<Rune> Compile(ISequence<Rune> program);
    
  }

}