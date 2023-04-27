using Dafny;
using DAST;

namespace Microsoft.Dafny.Compilers {

  class RustCompiler : DafnyWrittenCompiler {

    public override string Compile(ISequence<Rune> program) {
      return "hello";
    }
    
  }

}