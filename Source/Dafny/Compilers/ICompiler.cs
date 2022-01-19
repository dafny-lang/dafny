using System.Collections.ObjectModel;
using System.IO;

namespace Microsoft.Dafny;

public interface ICompiler {
  public CompilerFactory Factory { get; }

  void Compile(Program dafnyProgram, ConcreteSyntaxTree output);

  void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree);
  bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string pathsFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter, out object compilationResult);
  bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string pathsFilename,
    ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter);

  void WriteCoverageLegendFile();
}