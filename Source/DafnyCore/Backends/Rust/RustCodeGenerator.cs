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

    public override void Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles, ConcreteSyntaxTree w) {
      var c = new DCOMP.COMP();
      var charType = Options.Get(CommonOptionBag.UnicodeCharacters)
        ? DCOMP.CharType.create_Unicode()
        : DCOMP.CharType.create_UTF16();
      var pointerType = Options.Get(CommonOptionBag.RawPointers)
        ? PointerType.create_Raw()
        : PointerType.create_RcMut();
      var rootType = Options.Get(RustBackend.RustModuleNameOption) is var opt && opt != "" ?
          RootType.create_RootPath(Sequence<Rune>.UnicodeFromString(opt))
          : RootType.create_RootCrate();
      c.__ctor(charType, pointerType, rootType);
      var s = c.Compile(program, otherFiles);
      if (!Options.Get(CommonOptionBag.EmitUncompilableCode) && c.error.is_Some) {
        throw new UnsupportedInvalidOperationException(c.error.dtor_value.ToVerbatimString(false));
      }
      w.Write(s.ToVerbatimString(false));
    }

    public override ISequence<Rune> EmitCallToMain(string fullName) {
      var splitByDot = fullName.Split('.');
      var convertedToUnicode = Sequence<Sequence<Rune>>.FromArray(splitByDot.Select(s => (Sequence<Rune>)Sequence<Rune>.UnicodeFromString(s)).ToArray());
      return DCOMP.COMP.EmitCallToMain(convertedToUnicode);
    }
  }

}