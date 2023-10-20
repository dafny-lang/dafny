using Dafny;
using ResolvedDesugaredExecutableDafnyPlugin;

namespace Microsoft.Dafny.Compilers;

class ResolvedDesugaredExecutableDafnyCompiler : DafnyWrittenCompiler {

  public override ISequence<Rune> Compile(Sequence<DAST.Module> program) {
    return COMP.Compile(program);
  }
}
