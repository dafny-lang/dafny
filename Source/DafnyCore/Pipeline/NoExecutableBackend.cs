using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

public class NoExecutableBackend : IExecutableBackend {
  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string>();
  public override string TargetName => throw new NotSupportedException();
  public override bool IsStable => throw new NotSupportedException();
  public override string TargetExtension => "doesNotExist";
  public override string PublicIdProtect(string name) {
    throw new NotSupportedException();
  }

  public override bool TextualTargetIsExecutable => throw new NotSupportedException();

  public override bool SupportsInMemoryCompilation => throw new NotSupportedException();
  public override string ModuleSeparator => ".";

  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    throw new NotSupportedException();
  }

  public override Task<bool> OnPostGenerate(string dafnyProgramName, string targetFilename, IDafnyOutputWriter outputWriter) {
    throw new NotSupportedException();
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    throw new NotSupportedException();
  }

  public override Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, IDafnyOutputWriter outputWriter) {
    throw new NotSupportedException();
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string pathsFilename,
    ReadOnlyCollection<string> otherFileNames, object compilationResult,
    IDafnyOutputWriter outputWriter) {
    throw new NotSupportedException();
  }

  public override void InstrumentCompiler(CompilerInstrumenter instrumenter, Program dafnyProgram) {
    throw new NotSupportedException();
  }

  public NoExecutableBackend([NotNull] DafnyOptions options) : base(options) {
  }
}