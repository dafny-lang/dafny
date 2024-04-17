
using Dafny;

namespace Microsoft.Dafny.Compilers {

  public abstract class DafnyWrittenCodeGenerator {

    public abstract ISequence<Rune> Compile(Sequence<DAST.Module> program);

    public abstract ISequence<Rune> EmitCallToMain(string fullName);

  }

}