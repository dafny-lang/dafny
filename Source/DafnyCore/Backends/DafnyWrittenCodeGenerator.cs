
using Dafny;

namespace Microsoft.Dafny.Compilers {

  public abstract class DafnyWrittenCodeGenerator {

    public abstract void Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles, ConcreteSyntaxTree w);

    public abstract ISequence<Rune> EmitCallToMain(
      DAST.Expression companion,
      Sequence<Rune> mainMethodName,
      bool hasArguments);

  }

}