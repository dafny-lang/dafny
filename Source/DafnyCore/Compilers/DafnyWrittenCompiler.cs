
using Dafny;

namespace Microsoft.Dafny.Compilers {

  public abstract class DafnyWrittenCompiler {

    public abstract string Compile(ISequence<Rune> program);
    
  }

}