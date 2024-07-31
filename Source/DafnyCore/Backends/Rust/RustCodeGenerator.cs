using System;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using Dafny;
using DCOMP;

namespace Microsoft.Dafny.Compilers {

  public class RustCodeGenerator : DafnyWrittenCodeGenerator {
    public DafnyOptions Options { get; set; }

    public ISequence<Rune> ModuleName { get; set; }
    
    public RustCodeGenerator(DafnyOptions options) {
      this.Options = options;
    }

    public override ISequence<Rune> Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles) {
      Contract.Requires(ModuleName is not null);
      var c = new DCOMP.COMP();
      c.__ctor(Options.Get(CommonOptionBag.UnicodeCharacters),
        Options.Get(CommonOptionBag.RawPointers) ? ObjectType.create_RawPointers() : ObjectType.create_RcMut(), ModuleName);
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