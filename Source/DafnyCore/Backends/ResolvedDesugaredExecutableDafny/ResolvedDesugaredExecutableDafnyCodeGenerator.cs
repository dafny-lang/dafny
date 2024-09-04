using System;
using System.IO;
using System.Linq;
using Dafny;
using ResolvedDesugaredExecutableDafnyPlugin;

namespace Microsoft.Dafny.Compilers;

class ResolvedDesugaredExecutableDafnyCodeGenerator : DafnyWrittenCodeGenerator {

  public override ISequence<Rune> Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles) {
    return COMP.Compile(program);
  }

  public override ISequence<Rune> EmitCallToMain(string fullName) {
    var splitByDot = fullName.Split('.');
    var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
    return COMP.EmitCallToMain(convertedToUnicode);
  }
}
