using Dafny;
using DCOMP;

namespace Microsoft.Dafny.Compilers {

  class RustCompiler : DafnyWrittenCompiler {

    public override ISequence<Rune> Compile(ISequence<Rune> program) {
      return COMP.Compile(program);
    }
    
  }

}