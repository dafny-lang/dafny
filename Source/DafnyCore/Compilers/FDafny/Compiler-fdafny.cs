using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Dafny;
using DCOMP;

namespace Microsoft.Dafny.Compilers {

  class FDafnyCompiler : DafnyWrittenCompiler {

    public override ISequence<Rune> Compile(Sequence<DAST.Module> program) {
      using var writer = new StreamWriter("TEST.dfy");
      {
        Console.SetOut(writer);
        Console.WriteLine("include \"Source/DafnyCore/Compilers/Dafny/AST.dfy\"");
        Console.WriteLine("const program := ");
        return COMP.Compile(program);
      }
    }

    public override ISequence<Rune> EmitCallToMain(string fullName) {
      var splitByDot = fullName.Split('.');
      var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
      return COMP.EmitCallToMain(convertedToUnicode);
    }

  }

}