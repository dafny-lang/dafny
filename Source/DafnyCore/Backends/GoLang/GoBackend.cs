using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Options;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public class GoBackend : ExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".go" };

  public override string TargetName => "Go";
  public override bool IsStable => true;
  public override string TargetExtension => "go";

  public override string TargetBaseDir(string dafnyProgramName) {
    var topLevelDir = $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-go";
    if (GoModuleMode) {
      return topLevelDir;
    }

    return $"{topLevelDir}/src";
  }

  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public bool GoModuleMode { get; set; } = true;
  public string GoModuleName;

  public static readonly Option<string> GoModuleNameCliOption = new("--go-module-name",
    @"This Option is used to specify the Go Module Name for the translated code".TrimStart()) {
  };
  public override IEnumerable<Option<string>> SupportedOptions => new List<Option<string>> { GoModuleNameCliOption };

  static GoBackend() {
    OptionRegistry.RegisterOption(GoModuleNameCliOption, OptionScope.Translation);
  }

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    var goModuleName = Options.Get(GoModuleNameCliOption);
    GoModuleMode = goModuleName != null;
    if (GoModuleMode) {
      GoModuleName = goModuleName;
    }
    return new GoCodeGenerator(Options, Reporter);
  }

  public override async Task<bool> OnPostGenerate(string dafnyProgramName, string targetDirectory, IDafnyOutputWriter outputWriter) {
    return await base.OnPostGenerate(dafnyProgramName, targetDirectory, outputWriter) && await OptimizeImports(targetDirectory, outputWriter);
  }

  private async Task<bool> OptimizeImports(string targetFilename, IDafnyOutputWriter outputWriter) {
    var goArgs = new List<string> {
      "-w",
      targetFilename
    };

    var writer = new StringWriter();
    var psi = PrepareProcessStartInfo("goimports", goArgs);

    var result = await RunProcess(psi, writer, writer);
    if (result != 0) {
      await outputWriter.Status("Error occurred while invoking goimports:" + writer);
    }
    return 0 == result;
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain, /*?*/
    string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, IDafnyOutputWriter outputWriter) {
    if (runAfterCompile) {
      Contract.Assert(callToMain != null);  // this is part of the contract of CompileTargetProgram
      // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
      // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'go run'
      // will run the program.
      return (true, null);
    } else {
      // compile now
      return (await SendToNewGoProcess(dafnyProgramName, targetFilename, otherFileNames,
        outputWriter, callToMain != null, run: false), null);
    }
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, IDafnyOutputWriter outputWriter) {

    return SendToNewGoProcess(dafnyProgramName, targetFilename, otherFileNames, outputWriter, hasMain: true, run: true);
  }

  private async Task<bool> SendToNewGoProcess(string dafnyProgramName, string targetFilename,
    ReadOnlyCollection<string> otherFileNames,
    IDafnyOutputWriter outputWriter, bool hasMain, bool run) {

    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) != ".go") {
        await outputWriter.Status($"Unrecognized file as extra input for Go compilation: {otherFileName}");
        return false;
      }

      if (!await CopyExternLibraryIntoPlace(mainProgram: targetFilename, externFilename: otherFileName, outputWriter: outputWriter)) {
        return false;
      }
    }

    // Dafny used to compile to the old Go package system only, but Go has moved on to a module
    // system. Although compiler has moved to new system, it still doesn't generate the go.mod file which
    // is required by go run. It also supports backwards compatability with GOPATH hence those env variables
    // are still being used while running in GOPATH mode.
    if (GoModuleMode) {
      Reporter.Info(MessageSource.Compiler, Token.Cli, "go build/run skipped in Go Module Mode");
      return true;
    }

    List<string> goArgs = [];
    if (run) {
      goArgs.Add("run");
    } else {
      string output;
      var outputToFile = !Options.RunAfterCompile;

      if (outputToFile) {
        string extension;
        if (hasMain) {
          switch (Environment.OSVersion.Platform) {
            case PlatformID.Unix:
            case PlatformID.MacOSX:
            case (PlatformID)128: // early Mono
              extension = null;
              break;
            default:
              extension = "exe";
              break;
          }
        } else {
          extension = "a";
        }
        output = Path.ChangeExtension(dafnyProgramName, extension);
      } else {
        // This is used when there is no main method but user has invoked dafny run.
        switch (Environment.OSVersion.Platform) {
          case PlatformID.Unix:
          case PlatformID.MacOSX:
          case (PlatformID)128: // early Mono
            output = "/dev/null";
            break;
          default:
            output = "NUL";
            break;
        }
      }

      goArgs.Add("build");
      goArgs.Add("-o");
      goArgs.Add(output);
    }

    goArgs.Add(targetFilename);
    goArgs.AddRange(Options.MainArgs);

    var psi = PrepareProcessStartInfo("go", goArgs);

    psi.EnvironmentVariables["GOPATH"] = GoPath(targetFilename);
    psi.EnvironmentVariables["GO111MODULE"] = "auto";

    await using var sw = outputWriter.StatusWriter();
    await using var ew = outputWriter.ErrorWriter();
    return 0 == await RunProcess(psi, sw, ew);
  }

  static string GoPath(string filename) {
    var dirName = Path.GetDirectoryName(Path.GetDirectoryName(filename));

    Contract.Assert(dirName != null);

    // Filename is Foo-go/src/Foo.go, so go two directories up
    return Path.GetFullPath(dirName);
  }

  async Task<bool> CopyExternLibraryIntoPlace(string externFilename, string mainProgram, IDafnyOutputWriter outputWriter) {
    // Grossly, we need to look in the file to figure out where to put it
    var pkgName = FindPackageName(externFilename);
    if (pkgName == null) {
      await outputWriter.Status($"Unable to determine package name: {externFilename}");
      return false;
    }
    if (pkgName.StartsWith("_")) {
      // Check this here because otherwise Go acts like the package simply doesn't exist, which is confusing
      await outputWriter.Status($"Go packages can't start with underscores: {pkgName}");
      return false;
    }

    var mainDir = Path.GetDirectoryName(mainProgram);

    Contract.Assert(mainDir != null);

    var tgtDir = Path.Combine(mainDir, pkgName);
    var tgtFilename = Path.Combine(tgtDir, pkgName + ".go");

    Directory.CreateDirectory(tgtDir);
    File.Copy(externFilename, tgtFilename, overwrite: true);

    string relTgtFilename;
    var cwd = Directory.GetCurrentDirectory();
    if (tgtFilename.StartsWith(cwd)) {
      relTgtFilename = tgtFilename.Substring(cwd.Length + 1); // chop off relative path and '/'
    } else {
      relTgtFilename = tgtFilename;
    }
    if (Options.Verbose) {
      await outputWriter.Status($"Additional input {externFilename} copied to {relTgtFilename}");
    }
    return true;
  }

  private static string FindPackageName(string externFilename) {
    using var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read));
    while (rd.ReadLine() is { } line) {
      var match = PackageLine.Match(line);
      if (match.Success) {
        return match.Groups[1].Value;
      }
    }
    return null;
  }

  private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*$");

  public GoBackend(DafnyOptions options) : base(options) {
  }
}