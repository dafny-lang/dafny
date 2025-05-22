using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Runtime.InteropServices;
using System.Threading.Tasks;
using DafnyCore.Options;

namespace Microsoft.Dafny.Compilers;

public class PythonBackend : ExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".py" };

  public override string TargetName => "Python";
  public override bool IsStable => true;
  public override string TargetExtension => "py";
  public override int TargetIndentSize => 4;

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-py";

  public override string TargetBasename(string dafnyProgramName) => "__main__";

  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => true;

  public bool PythonModuleMode { get; set; } = true;
  public string PythonModuleName;

  public static readonly Option<string> PythonModuleNameCliOption = new("--python-module-name",
    @"This Option is used to specify the Python Module Name for the translated code".TrimStart()) {
  };
  public override IEnumerable<Option<string>> SupportedOptions => new List<Option<string>> { PythonModuleNameCliOption };

  static PythonBackend() {
    OptionRegistry.RegisterOption(PythonModuleNameCliOption, OptionScope.Translation);
  }

  public override IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "number", "ulong", "long" };

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    var pythonModuleName = Options.Get(PythonModuleNameCliOption);
    PythonModuleMode = pythonModuleName != null;
    if (PythonModuleMode) {
      PythonModuleName = pythonModuleName;
    }
    return new PythonCodeGenerator(Options, Reporter);
  }

  private static readonly Regex ModuleLine = new(@"^\s*#\s*Module:\s+([a-zA-Z0-9_]+(.[a-zA-Z0-9_]+)*)\s*$");

  private static string FindModuleName(string externFilename) {
    using var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read));
    while (rd.ReadLine() is { } line) {
      var match = ModuleLine.Match(line);
      if (match.Success) {
        rd.Close();
        return match.Groups[1].Value;
      }
    }
    rd.Close();
    return Path.GetExtension(externFilename) == ".py" ? Path.GetFileNameWithoutExtension(externFilename) : null;
  }

  private static readonly Dictionary<OSPlatform, string> PlatformDefaults = new() {
    { OSPlatform.Linux, "python3" },
    { OSPlatform.Windows, "python" },
    { OSPlatform.FreeBSD, "python3" },
    { OSPlatform.OSX, "python3" },
  };
  private static string DefaultPythonCommand => PlatformDefaults.SingleOrDefault(
      kv => RuntimeInformation.IsOSPlatform(kv.Key),
      new(OSPlatform.Linux, "python3")
    ).Value;

  async Task<bool> CopyExternLibraryIntoPlace(string externFilename, string mainProgram, IDafnyOutputWriter outputWriter) {
    // Grossly, we need to look in the file to figure out where to put it
    var moduleName = FindModuleName(externFilename);
    if (moduleName == null) {
      await outputWriter.Status($"Unable to determine module name: {externFilename}");
      return false;
    }
    var mainDir = Path.GetDirectoryName(mainProgram);
    Contract.Assert(mainDir != null);
    var modulePath = moduleName.Replace('.', Path.DirectorySeparatorChar);
    var tgtFilename = Path.Combine(mainDir, $"{modulePath}.py");
    var file = new FileInfo(externFilename);
    Directory.CreateDirectory(Path.GetDirectoryName(tgtFilename)!);
    file.CopyTo(tgtFilename, true);
    if (Options.Verbose) {
      await outputWriter.Status($"Additional input {externFilename} copied to {tgtFilename}");
    }
    return true;
  }

  public override void CleanSourceDirectory(string sourceDirectory) {
    var cacheDirectory = Path.Combine(sourceDirectory, "__pycache__");
    try {
      Directory.Delete(cacheDirectory, true);
    } catch (DirectoryNotFoundException) {
    }
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, IDafnyOutputWriter outputWriter) {
    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) != ".py") {
        await outputWriter.Status($"Unrecognized file as extra input for Python compilation: {otherFileName}");
        return (false, null);
      }
      if (!await CopyExternLibraryIntoPlace(otherFileName, targetFilename, outputWriter)) {
        return (false, null);
      }
    }
    if (!runAfterCompile) {
      var psi = PrepareProcessStartInfo(DefaultPythonCommand);
      psi.Arguments = $"-m compileall -q {Path.GetDirectoryName(targetFilename)}";
      await using var sw = outputWriter.StatusWriter();
      return (0 == await RunProcess(psi, sw, sw, "Error while compiling Python files."), null);
    }
    return (true, null);
  }

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult,
    IDafnyOutputWriter outputWriter) {
    Contract.Requires(targetFilename != null || otherFileNames.Count == 0);
    var psi = PrepareProcessStartInfo(DefaultPythonCommand, Options.MainArgs.Prepend(targetFilename));
    psi.EnvironmentVariables["PYTHONIOENCODING"] = "utf8";

    await using var sw = outputWriter.StatusWriter();
    await using var ew = outputWriter.ErrorWriter();
    return 0 == await RunProcess(psi, sw, ew);
  }

  public PythonBackend(DafnyOptions options) : base(options) {
  }
}