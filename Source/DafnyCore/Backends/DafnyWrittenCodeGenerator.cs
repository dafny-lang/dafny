
using Dafny;

namespace Microsoft.Dafny.Compilers {

  public abstract class DafnyWrittenCodeGenerator {

    public abstract ISequence<Rune> Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles);

    public abstract ISequence<Rune> EmitCallToMain(string fullName);

  }

}