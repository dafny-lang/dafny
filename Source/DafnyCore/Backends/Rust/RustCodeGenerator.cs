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

    private COMP CreateCompiler() {
      var c = new DCOMP.COMP();
      var charType = Options.Get(CommonOptionBag.UnicodeCharacters)
        ? Defs.CharType.create_UTF32()
        : Defs.CharType.create_UTF16();
      var pointerType = Options.Get(CommonOptionBag.RawPointers)
        ? Defs.PointerType.create_Raw()
        : Defs.PointerType.create_RcMut();
      var rootType = Options.Get(RustBackend.RustModuleNameOption) is { } opt && opt != "" ?
        Defs.RootType.create_RootPath(Sequence<Rune>.UnicodeFromString(opt))
        : Defs.RootType.create_RootCrate();
      var syncType = Options.Get(RustBackend.RustSyncOption)
        ? Defs.SyncType.create_Sync()
        : Defs.SyncType.create_NoSync();
      c.__ctor(charType, pointerType, rootType, syncType);
      return c;
    }

    public override void Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles, ConcreteSyntaxTree w) {
      var c = CreateCompiler();
      var s = c.Compile(program, otherFiles);
      if (!Options.Get(CommonOptionBag.EmitUncompilableCode) && c.error.is_Some) {
        throw new UnsupportedInvalidOperationException(c.error.dtor_value.ToVerbatimString(false));
      }
      w.Write(s.ToVerbatimString(false));
    }

    public override ISequence<Rune> EmitCallToMain(
      DAST.Expression companion,
      Sequence<Rune> mainMethodName,
      bool hasArguments) {
      var c = CreateCompiler();
      var result = c.EmitCallToMain(companion, mainMethodName, hasArguments);
      if (!Options.Get(CommonOptionBag.EmitUncompilableCode) && c.error.is_Some) {
        throw new UnsupportedInvalidOperationException(c.error.dtor_value.ToVerbatimString(false));
      }

      return result;
    }
  }

}