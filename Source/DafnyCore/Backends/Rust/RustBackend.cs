using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class RustBackend : DafnyExecutableBackend {
  protected override bool PreventShadowing => false;

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".rs" };
  public override string TargetName => "Rust";
  public override bool IsStable => true;
  public override bool IsInternal => true;
  public override string TargetExtension => "rs";
  public override int TargetIndentSize => 4;
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public override IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "ulong", "long", "udoublelong", "doublelong" };

  public override string TargetBasename(string dafnyProgramName) =>
    Regex.Replace(base.TargetBasename(dafnyProgramName), "[^_A-Za-z0-9]", "_");

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-rust/src";

  protected override DafnyWrittenCodeGenerator CreateDafnyWrittenCompiler() {
    return new RustCodeGenerator();
  }

  private string ComputeExeName(string targetFilename) {
    var targetDirectory = Path.GetDirectoryName(Path.GetDirectoryName(targetFilename));
    if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
      return Path.Combine(targetDirectory, "target", "debug", Path.GetFileNameWithoutExtension(targetFilename) + ".exe");
    } else {
      return Path.Combine(targetDirectory, "target", "debug", Path.GetFileNameWithoutExtension(targetFilename));
    }
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter) {
    var targetDirectory = Path.GetDirectoryName(Path.GetDirectoryName(targetFilename));
    var runtimeDirectory = Path.Combine(targetDirectory, "runtime");
    if (Directory.Exists(runtimeDirectory)) {
      Directory.Delete(runtimeDirectory, true);
    }
    Directory.CreateDirectory(runtimeDirectory);

    var assembly = System.Reflection.Assembly.Load("DafnyPipeline");
    assembly.GetManifestResourceNames().Where(f => f.StartsWith("DafnyPipeline.DafnyRuntimeRust")).ToList().ForEach(f => {
      var stream = assembly.GetManifestResourceStream(f);
      var dotToSlashPath = "";
      var parts = f.Replace("DafnyPipeline.DafnyRuntimeRust.", "").Split('.');
      for (var i = 0; i < parts.Length; i++) {
        dotToSlashPath += parts[i];

        if (i < parts.Length - 2) {
          dotToSlashPath += "/";
        } else if (i == parts.Length - 2) {
          // extension
          dotToSlashPath += ".";
        }
      }

      var containingDirectory = Path.Combine(runtimeDirectory, Path.GetDirectoryName(dotToSlashPath));
      if (!Directory.Exists(containingDirectory)) {
        Directory.CreateDirectory(containingDirectory);
      }

      using var outFile = new FileStream(Path.Combine(runtimeDirectory, dotToSlashPath), FileMode.Create, FileAccess.Write);
      stream.CopyTo(outFile);
    });

    using (var cargoToml = new FileStream(Path.Combine(targetDirectory, "Cargo.toml"), FileMode.Create, FileAccess.Write)) {
      using var cargoTomlWriter = new StreamWriter(cargoToml);
      await cargoTomlWriter.WriteLineAsync("[package]");
      var packageName = Path.GetFileNameWithoutExtension(targetFilename);
      // package name cannot start with a digit
      if (char.IsDigit(packageName[0])) {
        packageName = "_" + packageName;
      }
      await cargoTomlWriter.WriteLineAsync($"name = \"{packageName}\"");
      await cargoTomlWriter.WriteLineAsync("version = \"0.1.0\"");
      await cargoTomlWriter.WriteLineAsync("edition = \"2021\"");
      await cargoTomlWriter.WriteLineAsync();
      await cargoTomlWriter.WriteLineAsync("[dependencies]");
      await cargoTomlWriter.WriteLineAsync("dafny_runtime = { path = \"runtime\" }");
      await cargoTomlWriter.WriteLineAsync("num = \"0.4\"");
      await cargoTomlWriter.WriteLineAsync();

      if (callToMain == null) {
        await cargoTomlWriter.WriteLineAsync("[lib]");
        await cargoTomlWriter.WriteLineAsync("path = \"src/" + Path.GetFileName(targetFilename) + "\"");
        await cargoTomlWriter.WriteLineAsync();
      } else {
        await cargoTomlWriter.WriteLineAsync("[[bin]]");
        await cargoTomlWriter.WriteLineAsync($"name = \"{Path.GetFileNameWithoutExtension(targetFilename)}\"");
        await cargoTomlWriter.WriteLineAsync("path = \"src/" + Path.GetFileName(targetFilename) + "\"");
        await cargoTomlWriter.WriteLineAsync();
      }
    }

    var args = new List<string> {
      "build",
      "--quiet"
    };

    if (callToMain == null) {
      args.Add("--lib");
    } else {
      args.Add("--bin");
      args.Add(Path.GetFileNameWithoutExtension(targetFilename));
    }

    var psi = PrepareProcessStartInfo("cargo", args);
    psi.WorkingDirectory = targetDirectory;
    return (0 == await RunProcess(psi, outputWriter, outputWriter, "Error while compiling Rust files."), null);
  }
  public override Encoding OutputWriterEncoding => Encoding.UTF8;

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter,
    TextWriter errorWriter) {
    Contract.Requires(targetFilename != null || otherFileNames.Count == 0);
    var psi = PrepareProcessStartInfo(ComputeExeName(targetFilename), Options.MainArgs);
    return 0 == await RunProcess(psi, outputWriter, errorWriter);
  }

  public RustBackend(DafnyOptions options) : base(options) {
  }
}