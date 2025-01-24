using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Reflection;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.Compilers;

public class CsharpBackend : ExecutableBackend {

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new CsharpCodeGenerator(Options, Reporter);
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".cs", ".dll" };

  public override string TargetName => "C#";
  public override bool IsStable => true;
  public override string TargetExtension => "cs";

  // True if the most recently visited AST has a method annotated with {:synthesize}:

  public override string GetCompileName(bool isDefaultModule, string moduleName, string compileName) {
    return isDefaultModule
      ? PublicIdProtect(compileName)
      : base.GetCompileName(isDefaultModule, moduleName, compileName);
  }

  public override bool SupportsInMemoryCompilation => true;
  public override bool TextualTargetIsExecutable => false;

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter) {

    var outputDir = targetFilename == null ? Directory.GetCurrentDirectory() : Path.GetDirectoryName(Path.GetFullPath(targetFilename));
    var fileNames = Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName));
    var sourcePath = Path.Join(outputDir, fileNames + ".cs");
    var csprojPath = Path.Join(outputDir, fileNames + ".csproj");
    Directory.CreateDirectory(outputDir);

    var source = callToMain == null ? targetProgramText : targetProgramText + callToMain;
    await File.WriteAllTextAsync(sourcePath, source);

    var outputType = callToMain == null ? "Library" : "Exe";

    var itemGroupExtra = @"";
    if (!Options.IncludeRuntime) {
      var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
      var runtimePath = Path.Join(libPath, "DafnyRuntime.dll");
      itemGroupExtra = @$"
    <Reference Include=""DafnyRuntime"">
      <HintPath>{runtimePath}</HintPath>
    </Reference>";
    }

    var sourceFiles = new StringBuilder();
    sourceFiles.AppendLine(@$"<Compile Include=""{sourcePath}"" />");

    foreach (var file in otherFileNames) {
      string extension = Path.GetExtension(file);
      if (extension != null) { extension = extension.ToLower(); }
      if (extension == ".cs") {
        var normalizedPath = Path.Combine(Path.GetDirectoryName(file), Path.GetFileName(file));
        if (File.Exists(normalizedPath)) {
          sourceFiles.AppendLine(@$"<Compile Include=""{normalizedPath}"" />");
        } else {
          await outputWriter.WriteLineAsync($"Errors compiling program: Could not find {file}");
          return (false, null);
        }
      } else if (extension == ".dll") {
        sourceFiles.Append(@$"
    <Reference Include=""{Path.GetFileNameWithoutExtension(file)}"">
      <HintPath>{Path.GetFullPath(file)}</HintPath>
    </Reference>");
      }
    }

    var itemGroup = @$"
  <ItemGroup>
      {sourceFiles}
      <PackageReference Include=""System.Runtime.Numerics"" Version=""4.3.0"" />
      <PackageReference Include=""System.Collections.Immutable"" Version=""1.7.1"" />
      {itemGroupExtra}
  </ItemGroup>";

    var projectFile = @$"<Project Sdk=""Microsoft.NET.Sdk"">

  <PropertyGroup>
    <OutputType>{outputType}</OutputType>
    <TargetFramework>net8.0</TargetFramework>
    <ImplicitUsings>enable</ImplicitUsings>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
    <NoWarn>CS8600;CS8603;CS8604;CS8605;CS8625;CS8629;CS8714;CS8765;CS8769;CS8981</NoWarn>
    <Nullable>enable</Nullable>
    <RollForward>Major</RollForward>
  </PropertyGroup>

  {itemGroup}
</Project>
";

    await File.WriteAllTextAsync(csprojPath, projectFile);

    var arguments = new[] { "build", csprojPath, "-o", outputDir };
    var psi = PrepareProcessStartInfo("dotnet", arguments);
    var dotnetOutputWriter = new StringWriter();
    var dotnetErrorWriter = new StringWriter();
    var exitCode = await RunProcess(psi, dotnetOutputWriter, dotnetErrorWriter);
    var dllPath = Path.Combine(outputDir, fileNames + ".dll");
    if (exitCode != 0 || !File.Exists(dllPath)) {
      await outputWriter.WriteLineAsync($@"Failed to compile C# source code using 'dotnet {string.Join(" ", arguments)}'. Command output was:");
      await outputWriter.WriteAsync(dotnetOutputWriter.ToString());
      await outputWriter.WriteAsync(dotnetErrorWriter.ToString());
    } else {
      if (Options.Verbose) {
        await outputWriter.WriteLineAsync($"Compiled assembly into {Path.GetFileName(dllPath)}");
      }
    }
    return (exitCode == 0, dllPath);
  }

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {

    var dllPath = (string)compilationResult;
    var dllFolder = Path.GetDirectoryName(dllPath)!;

    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) == ".dll") {
        var destination = Path.Combine(dllFolder, Path.GetFileName(otherFileName));
        if (Path.GetFullPath(otherFileName) != Path.GetFullPath(destination)) {
          File.Copy(otherFileName, destination, true);
        }
      }
    }

    var psi = PrepareProcessStartInfo("dotnet", new[] { dllPath }.Concat(Options.MainArgs));
    return await RunProcess(psi, outputWriter, errorWriter) == 0;
  }

  public override void PopulateCoverageReport(CoverageReport coverageReport) {
    codeGenerator.Coverage.PopulateCoverageReport(coverageReport);
  }

  public CsharpBackend(DafnyOptions options) : base(options) {
  }
}
