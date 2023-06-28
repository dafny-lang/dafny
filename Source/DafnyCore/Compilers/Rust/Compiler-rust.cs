using System;
using System.Linq;
using Dafny;
using DCOMP;

namespace Microsoft.Dafny.Compilers {

  class RustCompiler : DafnyWrittenCompiler {

    public override ISequence<Rune> Compile(Sequence<DAST.TopLevel> program) {
      return COMP.Compile(program);
    }

    public override ISequence<Rune> EmitCallToMain(string fullName) {
      var splitByDot = fullName.Split('.');
      var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
      return COMP.EmitCallToMain(convertedToUnicode);
    }

  }

}