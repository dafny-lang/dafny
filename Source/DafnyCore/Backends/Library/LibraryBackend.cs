using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;

namespace Microsoft.Dafny.Compilers;

public class LibraryBackend : ExecutableBackend {
  public LibraryBackend(DafnyOptions options) : base(options) {
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { };

  public override string TargetName => "Dafny Library (.doo)";

  /// Some tests still fail when using the lib back-end, for example due to disallowed assumptions being present in the test,
  /// such as empty constructors with ensures clauses, generated from iterators
  public override bool IsStable => false;

  public override string TargetExtension => "doo";
  public override string TargetId => "lib";

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-lib";

  public override bool TextualTargetIsExecutable => false;

  public override bool SupportsInMemoryCompilation => false;

  public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
    Feature.LegacyCLI,
    Feature.RuntimeCoverageReport
  };

  // Necessary since Compiler is null
  public override string ModuleSeparator => ".";

  public string DooPath { get; set; }

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return null;
  }

  public override async Task<bool> OnPostGenerate(string dafnyProgramName, string targetFilename, IDafnyOutputWriter outputWriter) {
    // Not calling base.OnPostCompile() since it references `compiler`
    foreach (var message in embeddedLibraryMessages) {
      await outputWriter.Status(message);
    }
    return true;
  }

  public override string PublicIdProtect(string name) {
    throw new NotSupportedException();
  }

  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    if (!Options.UsingNewCli) {
      throw new UnsupportedFeatureException(dafnyProgram.GetStartOfFirstFileToken(), Feature.LegacyCLI);
    }

    ReportEmbeddedLibraries(dafnyProgram);

    var dooFile = new DooFile(dafnyProgram.AfterParsingClone);
    dooFile.Write(output);
  }

  private readonly List<string> embeddedLibraryMessages = [];

  /// <summary>
  /// A .doo file passed as a source input (as opposed to via --library) is compiled along with the
  /// rest of the program, which for this backend means its modules are copied into the produced library.
  /// Each copy is a separate module declaration, so using two libraries that embed the same module
  /// together later fails with "Duplicate module name" (see issue #6486). Notify so that users who did
  /// not intend to bundle their dependencies find out at the point where the embedding happens.
  /// This is a plain status message rather than a diagnostic: warnings fail the build by default,
  /// and working around that with --allow-warnings would force the same flag onto every consumer
  /// of the produced library (that option is part of the recorded library options), while Info
  /// diagnostics are only shown with --show-hints.
  /// </summary>
  private void ReportEmbeddedLibraries(Program dafnyProgram) {
    var embeddedByDoo = EmbeddedDeclarations(dafnyProgram, dafnyProgram.DefaultModuleDef, "")
      .Where(embedded => embedded.Uri is { IsFile: true } uri &&
                         uri.LocalPath.EndsWith(DooFile.Extension, StringComparison.Ordinal))
      .GroupBy(embedded => embedded.Uri);
    foreach (var group in embeddedByDoo) {
      var names = string.Join(", ", group.Select(embedded => embedded.Name).Distinct().OrderBy(name => name));
      embeddedLibraryMessages.Add(
        $"Note: the library {Options.GetPrintPath(group.Key.LocalPath)} was passed as a source file, " +
        $"so a copy of its declarations ({names}) is embedded in the produced library. " +
        "If that is not intended, pass it with --library instead; combining two libraries that embed " +
        "the same declaration fails with a \"Duplicate module name\" or \"duplicate name of top-level " +
        "declaration\" error.");
    }
  }

  /// Whether declarations from "uri" get embedded in the output rather than merely referenced. A .doo
  /// passed with --library is recorded in AlreadyCompiledRoots and is not embedded, so it must not be
  /// reported.
  ///
  /// This is the only test used here, for every kind of declaration. ModuleDefinition.ShouldCompile answers
  /// the same question for a module -- it agrees with this on every case exercised by the tests, including
  /// excluding a --library module -- but it returns true unconditionally for the default module, which is
  /// where a top-level type declaration and a default-class member live. Using it for modules and something
  /// else for the rest is what let a --library .doo be reported as embedded.
  private static bool IsEmbeddedFrom(Program dafnyProgram, Uri uri) {
    return uri != null && dafnyProgram.Compilation.AlreadyCompiledRoots?.Contains(uri) is not true;
  }

  /// <summary>
  /// The declarations of "module" that came from another file, paired with that file. Anything a .doo
  /// contributes can collide when two libraries embed the same one, so this covers more than modules:
  /// a .doo may hold only top-level type declarations, or only members of the default class, and a
  /// dotted module name (module A.B) introduces a synthesized parent that has no origin of its own,
  /// so the real declarations are one level down.
  /// </summary>
  private IEnumerable<(Uri Uri, string Name)> EmbeddedDeclarations(Program dafnyProgram,
      ModuleDefinition module, string prefix) {
    foreach (var decl in module.TopLevelDecls) {
      var qualified = prefix + decl.Name;
      if (decl is LiteralModuleDecl nested) {
        if (nested.Origin.Uri == null) {
          foreach (var embedded in EmbeddedDeclarations(dafnyProgram, nested.ModuleDef, qualified + ".")) {
            yield return embedded;
          }
        } else if (IsEmbeddedFrom(dafnyProgram, nested.Origin.Uri)) {
          yield return (nested.Origin.Uri, qualified);
        }
      } else if (decl is DefaultClassDecl defaultClass) {
        foreach (var member in defaultClass.Members.Where(member => IsEmbeddedFrom(dafnyProgram, member.Origin.Uri))) {
          yield return (member.Origin.Uri, prefix + member.Name);
        }
      } else if (IsEmbeddedFrom(dafnyProgram, decl.Origin.Uri)) {
        yield return (decl.Origin.Uri, qualified);
      }
    }
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    // No-op
  }

  private string DooFilePath(string dafnyProgramName) {
    return Path.GetFullPath(Path.ChangeExtension(dafnyProgramName, DooFile.Extension));
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, IDafnyOutputWriter outputWriter) {

    var targetDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
    DooPath = DooFilePath(dafnyProgramName);

    File.Delete(DooPath);

    try {
      ZipFile.CreateFromDirectory(targetDirectory, DooPath);
    } catch (IOException) {
      if (File.Exists(DooPath)) {
        await outputWriter.Status($"Failed to delete doo file at {Options.GetPrintPath(DooPath)}");
      }

      throw;
    }
    if (Options.Verbose) {
      await outputWriter.Status($"Wrote Dafny library to {Options.GetPrintPath(DooPath)}");
    }

    return (true, null);
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, object compilationResult,
    IDafnyOutputWriter outputWriter) {
    var dooPath = DooFilePath(dafnyProgramName);
    return RunTargetDafnyProgram(dooPath, outputWriter, true);
  }
}