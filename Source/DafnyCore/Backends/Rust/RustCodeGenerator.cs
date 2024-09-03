using System;
using System.CommandLine;
using System.Configuration;
using System.IO;
using System.Linq;
using Dafny;
using DCOMP;

namespace Microsoft.Dafny.Compilers {

  class RustCodeGenerator : DafnyWrittenCodeGenerator {
    public DafnyOptions Options { get; set; }

    public RustCodeGenerator(DafnyOptions options) {
      this.Options = options;
    }

    public override ISequence<Rune> Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles) {
      var c = new DCOMP.COMP();
      c.__ctor(
        Options.Get(CommonOptionBag.UnicodeCharacters)
          ? DCOMP.CharType.create_Unicode()
          : DCOMP.CharType.create_UTF16(),
        Options.Get(CommonOptionBag.RawPointers) ? PointerType.create_Raw() : PointerType.create_RcMut(),
        RootType.create_RootCrate()
        );
      var s = c.Compile(program, otherFiles);
      if (!Options.Get(CommonOptionBag.EmitUncompilableCode) && c.error.is_Some) {
        throw new UnsupportedInvalidOperationException(c.error.dtor_value.ToVerbatimString(false));
      }
      return s;
    }

    public override ISequence<Rune> EmitCallToMain(string fullName) {
      var splitByDot = fullName.Split('.');
      var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
      return DCOMP.COMP.EmitCallToMain(convertedToUnicode);
    }
  }

}