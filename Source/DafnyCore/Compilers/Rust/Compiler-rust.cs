using System;
using System.IO;
using System.Linq;
using Dafny;
using DCOMP;

namespace Microsoft.Dafny.Compilers {

  class RustCompiler : DafnyWrittenCompiler {

    public override ISequence<Rune> Compile(Sequence<DAST.Module> program) {
      var assembly = System.Reflection.Assembly.Load("DafnyPipeline");
      var stream = assembly.GetManifestResourceStream("DafnyRuntimeRust.rs");
      var contents = new StreamReader(stream).ReadToEnd();

      return COMP.Compile(program, Sequence<Rune>.UnicodeFromString(contents));
    }

    public override ISequence<Rune> EmitCallToMain(string fullName) {
      var splitByDot = fullName.Split('.');
      var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
      return COMP.EmitCallToMain(convertedToUnicode);
    }

  }

}