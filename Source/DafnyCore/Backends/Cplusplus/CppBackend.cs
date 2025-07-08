using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class CppBackend : ExecutableBackend {

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new CppCodeGenerator(Options, Reporter, OtherFileNames);
  }

  private string ComputeExeName(string targetFilename) {
    return Path.ChangeExtension(Path.GetFullPath(targetFilename), "exe");
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, IDafnyOutputWriter outputWriter) {
    var assemblyLocation = System.Reflection.Assembly.GetExecutingAssembly().Location;
    Contract.Assert(assemblyLocation != null);
    var codebase = Path.GetDirectoryName(assemblyLocation);
    Contract.Assert(codebase != null);
    var psi = PrepareProcessStartInfo("g++", new List<string> {
      "-Wall",
      "-Wextra",
      "-Wpedantic",
      "-Wno-unused-variable",
      "-Wno-deprecated-copy",
      "-Wno-unused-label",
      "-Wno-unused-but-set-variable",
      "-Wno-unknown-warning-option",
      "-g",
      "-std=c++17",
      "-I", codebase,
      "-o", ComputeExeName(targetFilename),
      targetFilename
    });
    await using var statusWriter = outputWriter.StatusWriter();
    return (0 == await RunProcess(psi, statusWriter, statusWriter, "Error while compiling C++ files."), null);
  }

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, IDafnyOutputWriter outputWriter) {
    var psi = PrepareProcessStartInfo(ComputeExeName(targetFilename), Options.MainArgs);

    await using var sw = outputWriter.StatusWriter();
    await using var ew = outputWriter.ErrorWriter();
    return 0 == await RunProcess(psi, sw, ew);
  }

  public override Command GetCommand() {
    var cmd = base.GetCommand();
    cmd.Description = $@"Translate Dafny sources to {TargetName} source and build files.

This back-end has various limitations (see Docs/Compilation/Cpp.md).
This includes lack of support for BigIntegers (aka int), most higher order functions,
and advanced features like traits or co-inductive types.";
    return cmd;
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".h" };

  public override string TargetName => "C++";
  public override bool IsStable => true;
  public override string TargetExtension => "cpp";

  public override bool SupportsInMemoryCompilation => false;

  public override bool TextualTargetIsExecutable => false;

  public CppBackend(DafnyOptions options) : base(options) {
  }
}