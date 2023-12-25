using System.Linq;
using Dafny;
using ResolvedDesugaredExecutableDafnyPlugin;

namespace Microsoft.Dafny.Compilers;

class ResolvedDesugaredExecutableDafnyCompiler : DafnyWrittenCompiler {

  public Sequence<DAST.Module> Program;
  public override ISequence<Rune> Compile(Sequence<DAST.Module> program) {
    Program = program;
    return COMP.Compile(program);
  }

  public override ISequence<Rune> EmitCallToMain(string fullName) {
    var splitByDot = fullName.Split('.');
    var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
    return COMP.EmitCallToMain(convertedToUnicode);
  }
}
