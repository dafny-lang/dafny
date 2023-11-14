using Dafny;
using DCOMP;

namespace Microsoft.Dafny.Compilers;

class RustCompiler : DafnyWrittenCompiler {

  public override ISequence<Rune> Compile(Sequence<DAST.Module> program) {
    return COMP.Compile(program);
  }
}
