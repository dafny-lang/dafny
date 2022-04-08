using System;
using System.Collections.ObjectModel;
using System.IO;

namespace Microsoft.Dafny.Compilers.SelfHosting;

public abstract class SelfHostingCompiler : Plugins.Compiler {
  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string pathsFilename, ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter,
    out object compilationResult) {
    throw new NotImplementedException();
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string pathsFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult,
    TextWriter outputWriter) {
    throw new NotImplementedException();
  }
}
