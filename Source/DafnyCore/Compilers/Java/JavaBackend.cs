using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class JavaBackend : ExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".java" };

  public override string TargetName => "Java";
  public override string TargetExtension => "java";

  public override string TargetBasename(string dafnyProgramName) =>
    JavaCompiler.TransformToClassName(base.TargetBasename(dafnyProgramName));

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-java";

  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public override void CleanSourceDirectory(string sourceDirectory) {
    try {
      Directory.Delete(sourceDirectory, true);
    } catch (DirectoryNotFoundException) {
    }
  }

  protected override SinglePassCompiler CreateCompiler() {
    return new JavaCompiler(Options, Reporter);
  }

  private void EmitRuntimeJar(string targetDirectory) {
    // Since DafnyRuntime.jar is binary, we can't use ReadRuntimeSystem
    var jarName = "DafnyRuntime.jar";
    var assembly = System.Reflection.Assembly.Load("DafnyPipeline");
    var stream = assembly.GetManifestResourceStream(jarName);
    if (stream == null) {
      throw new Exception($"Cannot find embedded resource: {jarName}");
    }

    var fullJarName = $"{targetDirectory}/{jarName}";
    FileStream outStream = new FileStream(fullJarName, FileMode.Create, FileAccess.Write);
    stream.CopyTo(outStream);
    outStream.Close();
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain, string /*?*/ targetFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    compilationResult = null;
    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) != ".java") {
        outputWriter.WriteLine($"Unrecognized file as extra input for Java compilation: {otherFileName}");
        return false;
      }
      if (!CopyExternLibraryIntoPlace(mainProgram: targetFilename, externFilename: otherFileName, outputWriter: outputWriter)) {
        return false;
      }
    }

    var targetDirectory = Path.GetDirectoryName(targetFilename);

    var files = new List<string>();
    foreach (string file in Directory.EnumerateFiles(targetDirectory, "*.java", SearchOption.AllDirectories)) {
      files.Add(Path.GetFullPath(file));
    }

    // Compile the generated source to .class files, adding the output directory to the classpath
    var compileProcess = PrepareProcessStartInfo("javac", new List<string> { "-encoding", "UTF8" }.Concat(files));
    compileProcess.WorkingDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
    compileProcess.EnvironmentVariables["CLASSPATH"] = GetClassPath(targetFilename);
    if (0 != RunProcess(compileProcess, outputWriter, outputWriter, "Error while compiling Java files.")) {
      return false;
    }

    var classFiles = Directory.EnumerateFiles(targetDirectory, "*.class", SearchOption.AllDirectories)
        .Select(file => Path.GetRelativePath(targetDirectory, file)).ToList();

    var simpleProgramName = Path.GetFileNameWithoutExtension(targetFilename);
    var jarPath = Path.GetFullPath(Path.ChangeExtension(dafnyProgramName, ".jar"));
    if (!CreateJar(callToMain == null ? null : simpleProgramName,
                   jarPath,
                   Path.GetFullPath(Path.GetDirectoryName(targetFilename)),
                   classFiles,
                   outputWriter)) {
      return false;
    }

    // Keep the build artifacts if --spill-translation is true
    // But keep them for legacy CLI so as not to break old behavior
    if (Options.UsingNewCli) {
      if (Options.SpillTargetCode == 0) {
        Directory.Delete(targetDirectory, true);
      } else {
        classFiles.ForEach(f => File.Delete(f));
      }
    }

    if (Options.CompileVerbose) {
      // For the sake of tests, just write out the filename and not the directory path
      var fileKind = callToMain != null ? "executable" : "library";
      outputWriter.WriteLine($"Wrote {fileKind} jar {Path.GetFileName(jarPath)}");
    }

    return true;
  }


  public bool CreateJar(string/*?*/ entryPointName, string jarPath, string rootDirectory, List<string> files, TextWriter outputWriter) {
    Directory.CreateDirectory(Path.GetDirectoryName(jarPath));
    var args = entryPointName == null ? // If null, then no entry point is added
        new List<string> { "cf", jarPath }
        : new List<string> { "cfe", jarPath, entryPointName };
    var jarCreationProcess = PrepareProcessStartInfo("jar", args.Concat(files));
    jarCreationProcess.WorkingDirectory = rootDirectory;
    return 0 == RunProcess(jarCreationProcess, outputWriter, outputWriter, "Error while creating jar file: " + jarPath);
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string targetFilename, /*?*/
    ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter,
    TextWriter errorWriter) {
    string jarPath = Path.ChangeExtension(dafnyProgramName, ".jar"); // Must match that in CompileTargetProgram
    var psi = PrepareProcessStartInfo("java",
      new List<string> { "-Dfile.encoding=UTF-8", "-jar", jarPath }
        .Concat(Options.MainArgs));
    // Run the target program in the user's working directory and with the user's classpath
    psi.EnvironmentVariables["CLASSPATH"] = GetClassPath(null);
    return 0 == RunProcess(psi, outputWriter, errorWriter);
  }

  private string GetClassPath(string targetFilename) {
    var classpath = Environment.GetEnvironmentVariable("CLASSPATH"); // String.join converts null to ""
    // Note that the items in the CLASSPATH must have absolute paths because the compilation is performed in a subfolder of where the command-line is executed
    if (targetFilename != null) {
      var targetDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
      var parts = new List<string> { ".", targetDirectory, classpath };
      if (!Options.IncludeRuntime) {
        EmitRuntimeJar(targetDirectory);
        parts.Add(Path.Combine(targetDirectory, "DafnyRuntime.jar"));
      }
      return string.Join(Path.PathSeparator, parts);
    }

    return classpath;
  }

  bool CopyExternLibraryIntoPlace(string externFilename, string mainProgram, TextWriter outputWriter) {
    // Grossly, we need to look in the file to figure out where to put it
    var pkgName = FindPackageName(externFilename);
    if (pkgName == null) {
      outputWriter.WriteLine($"Unable to determine package name: {externFilename}");
      return false;
    }
    string baseName = Path.GetFileNameWithoutExtension(externFilename);
    var mainDir = Path.GetDirectoryName(mainProgram);
    Contract.Assert(mainDir != null);
    var tgtDir = Path.Combine(mainDir, pkgName);
    var tgtFilename = Path.Combine(tgtDir, baseName + ".java");
    Directory.CreateDirectory(tgtDir);
    FileInfo file = new FileInfo(externFilename);
    file.CopyTo(tgtFilename, true);
    if (Options.CompileVerbose) {
      outputWriter.WriteLine($"Additional input {externFilename} copied to {tgtFilename}");
    }
    return true;
  }

  private static string FindPackageName(string externFilename) {
    using var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read));
    while (rd.ReadLine() is string line) {
      var match = PackageLine.Match(line);
      if (match.Success) {
        return match.Groups[1].Value;
      }
    }
    return null;
  }

  private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*;$");

  public JavaBackend(DafnyOptions options) : base(options) {
  }
}
