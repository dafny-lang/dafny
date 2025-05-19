using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.Compilers;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using static Microsoft.Dafny.ParseErrors;

namespace Microsoft.Dafny;

public record DfyParseFileResult(
  int? Version,
  Uri Uri,
  IReadOnlyList<Uri> NewRootUris,
  BatchErrorReporter ErrorReporter,
  FileModuleDefinition Module,
  IReadOnlyList<Action<SystemModuleManager>> ModifyBuiltins
  );

public class ProgramParser {
  protected readonly ILogger<ProgramParser> logger;
  private readonly IFileSystem fileSystem;

  public ProgramParser(ILogger<ProgramParser> logger, IFileSystem fileSystem) {
    this.logger = logger;
    this.fileSystem = fileSystem;
  }

  public virtual async Task<ProgramParseResult> ParseFiles(string programName, IReadOnlyList<DafnyFile> files,
    ErrorReporter errorReporter,
    CancellationToken cancellationToken) {
    var options = errorReporter.Options;
    var builtIns = new SystemModuleManager(options);
    var defaultModule = new DefaultModuleDefinition();

    var rootSourceUris = files.Select(f => f.Uri).ToList();
    var verifiedRoots = files.Where(df => df.ShouldNotVerify).Select(df => df.Uri).ToHashSet();
    var compiledRoots = files.Where(df => df.ShouldNotCompile).Select(df => df.Uri).ToHashSet();
    var compilation = new CompilationData(errorReporter, defaultModule.Includes, rootSourceUris, verifiedRoots,
      compiledRoots);
    var program = new Program(
      programName,
      new LiteralModuleDecl(options, defaultModule, null, Guid.NewGuid()),
      builtIns,
      errorReporter, compilation
    );
    var versionedFiles = new Dictionary<Uri, int>();

    foreach (var dafnyFile in files) {
      cancellationToken.ThrowIfCancellationRequested();
      if (options.Trace) {
        await options.OutputWriter.WriteLineAsync("Parsing " + dafnyFile.FilePath);
      }

      if (options.XmlSink is { IsOpen: true } && dafnyFile.Uri.IsFile) {
        options.XmlSink.WriteFileFragment(dafnyFile.Uri.LocalPath);
      }

      var parseResult = ParseFileWithErrorHandling(
        dafnyFile.FileOptions,
        dafnyFile.GetContent,
        dafnyFile.Origin,
        dafnyFile.Uri,
        cancellationToken);
      if (parseResult.ErrorReporter.HasErrors) {
        logger.LogDebug($"encountered {parseResult.ErrorReporter.ErrorCount} errors while parsing {dafnyFile.Uri}");
      }

      AddParseResultToProgram(parseResult, program, versionedFiles);
    }

    if (!(options.DisallowIncludes || options.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate)) {
      var includedModules = TryParseIncludes(files, defaultModule.Includes.ToList(),
        builtIns, errorReporter, cancellationToken);

      foreach (var module in includedModules) {
        AddParseResultToProgram(module, program, versionedFiles);
      }
    }

    if (options.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate) {
      var dependencyMap = new DependencyMap();
      dependencyMap.AddIncludes(defaultModule.Includes);
      dependencyMap.PrintMap(options);
    }

    if (!errorReporter.HasErrors) {
      DafnyMain.MaybePrintProgram(program, options.DafnyPrintFile, false);

      // Capture the original program text before resolution
      // if we're building a .doo file.
      // See comment on LibraryBackend.DooFile.
      if (program.Options.Backend is LibraryBackend libBackend) {
        program.AfterParsingClone = new Program(new Cloner(true), program);
      }
    }

    ShowWarningsForIncludeCycles(program);

    return new ProgramParseResult(program, versionedFiles);
  }

  private DfyParseFileResult ParseFileWithErrorHandling(DafnyOptions options,
    Func<FileSnapshot> getSnapShot,
    IOrigin origin,
    Uri uri,
    CancellationToken cancellationToken) {
    var fileSnapshot = getSnapShot();
    try {
      return ParseFile(options, fileSnapshot, uri, cancellationToken);
    } catch (IOException e) {
      if (origin == null) {
        throw;
      }

      var reporter = new BatchErrorReporter(options);
      reporter.Error(MessageSource.Parser, origin,
        $"Unable to open the file {uri} because {e.Message}.");
      return new DfyParseFileResult(fileSnapshot.Version, uri, [], reporter, new FileModuleDefinition(Token.NoToken),
        new Action<SystemModuleManager>[] { });
    } catch (OperationCanceledException) {
      throw;
    } catch (Exception e) {
      var internalErrorDummyToken = new Token {
        Uri = uri,
        line = 1,
        col = 1,
        pos = 0,
        val = string.Empty
      };

      var reporter = new BatchErrorReporter(options);
      reporter.Error(MessageSource.Parser, ErrorId.p_internal_exception, internalErrorDummyToken,
        "[internal error] Parser exception: " + e.Message + "\n" + e.StackTrace);
      return new DfyParseFileResult(fileSnapshot.Version, uri, [], reporter, new FileModuleDefinition(Token.NoToken),
        new Action<SystemModuleManager>[] { });
    }
  }

  private void ShowWarningsForIncludeCycles(Program program) {
    var graph = new Graph<Uri>();
    foreach (var edgesForUri in program.Compilation.Includes.GroupBy(i => i.IncluderFilename)) {
      foreach (var edge in edgesForUri) {
        graph.AddEdge(edge.IncluderFilename, edge.IncludedFilename);
      }
    }

    var sortedSccRoots = graph.TopologicallySortedComponents();
    var includeCycles = sortedSccRoots.Select(graph.GetSCC).Where(scc => scc.Count > 1);
    foreach (var cycle in includeCycles) {
      program.Reporter.Info(MessageSource.Parser, program.GetStartOfFirstFileToken(),
        $"Program contains a cycle of includes, consisting of:\n{string.Join("\n", cycle.Select(c => c.LocalPath))}");
    }
  }

  private static void AddParseResultToProgram(DfyParseFileResult parseFileResult, Program program,
    Dictionary<Uri, int> versionedFiles) {
    program.Compilation.RootSourceUris.AddRange(parseFileResult.NewRootUris);

    if (parseFileResult.Version != null) {
      versionedFiles.Add(parseFileResult.Uri, parseFileResult.Version.Value);
    }

    var defaultModule = program.DefaultModuleDef;
    var fileModule = parseFileResult.Module;
    program.Files.Add(fileModule);

    foreach (var modify in parseFileResult.ModifyBuiltins) {
      modify(program.SystemModuleManager);
    }

    parseFileResult.ErrorReporter.CopyDiagnostics(program.Reporter);

    ModuleDefinition sourceModule = fileModule;
    ModuleDefinition targetModule = defaultModule;

    MoveModuleContents(sourceModule, targetModule);

    foreach (var include in fileModule.Includes) {
      defaultModule.Includes.Add(include);
    }

    foreach (var prefixNamedModule in fileModule.PrefixNamedModules) {
      defaultModule.PrefixNamedModules.Add(prefixNamedModule);
    }

    defaultModule.DefaultClass.SetMembersBeforeResolution();
  }

  public static void MoveModuleContents(ModuleDefinition sourceModule, ModuleDefinition targetModule) {
    foreach (var declToMove in sourceModule.DefaultClasses.Concat(sourceModule.SourceDecls)) {
      declToMove.EnclosingModuleDefinition = targetModule;
      if (declToMove is LiteralModuleDecl literalModuleDecl) {
        literalModuleDecl.ModuleDef.EnclosingModule = targetModule;
      }

      if (declToMove is ClassLikeDecl { NonNullTypeDecl: { } nonNullTypeDecl }) {
        nonNullTypeDecl.EnclosingModuleDefinition = targetModule;
      }

      if (declToMove is DefaultClassDecl defaultClassDecl) {
        foreach (var member in defaultClassDecl.Members) {
          targetModule.DefaultClass.Members.Add(member);
          member.EnclosingClass = targetModule.DefaultClass;
        }
      } else {
        targetModule.SourceDecls.Add(declToMove);
      }
    }
  }

  public IList<DfyParseFileResult> TryParseIncludes(
    IReadOnlyList<DafnyFile> files,
    IEnumerable<Include> roots,
    SystemModuleManager systemModuleManager,
    ErrorReporter errorReporter,
    CancellationToken cancellationToken
  ) {
    var stack = new Stack<DafnyFile>();
    var result = new List<DfyParseFileResult>();
    var resolvedFiles = new HashSet<Uri>();
    foreach (var rootFile in files) {
      resolvedFiles.Add(rootFile.Uri);
    }

    foreach (var root in roots) {
      var dafnyFile = IncludeToDafnyFile(errorReporter, root);
      if (dafnyFile != null) {
        stack.Push(dafnyFile);
      }
    }

    while (stack.Any()) {
      var top = stack.Pop();
      if (!resolvedFiles.Add(top.Uri)) {
        continue;
      }

      cancellationToken.ThrowIfCancellationRequested();
      var parseIncludeResult = ParseFileWithErrorHandling(
        top.FileOptions,
        top.GetContent,
        top.Origin,
        top.Uri,
        cancellationToken);
      result.Add(parseIncludeResult);

      foreach (var include in parseIncludeResult.Module.Includes) {
        var dafnyFile = IncludeToDafnyFile(errorReporter, include);
        if (dafnyFile != null) {
          stack.Push(dafnyFile);
        }
      }
    }

    return result;
  }

  private DafnyFile IncludeToDafnyFile(ErrorReporter errorReporter, Include include) {
    return DafnyFile.HandleDafnyFile(fileSystem, errorReporter, include.ParseOptions, include.IncludedFilename, include.PathOrigin, false);
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members) from "filename"
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner.
  ///</summary>
  protected virtual DfyParseFileResult ParseFile(DafnyOptions options, FileSnapshot fileSnapshot,
    Uri uri, CancellationToken cancellationToken) /* throws System.IO.IOException */ {
    Contract.Requires(uri != null);
    using var reader = fileSnapshot.Reader;
    CommonOptionBag.InputTypeEnum inputType;
    if (uri == DafnyFile.StdInUri) {
      inputType = options.Get(CommonOptionBag.InputType);
    } else {
      inputType = uri.LocalPath.EndsWith(DafnyFile.DafnyBinaryExtension)
        ? CommonOptionBag.InputTypeEnum.Binary
        : CommonOptionBag.InputTypeEnum.Source;
    }
    if (inputType == CommonOptionBag.InputTypeEnum.Source) {
      var text = SourcePreprocessor.ProcessDirectives(reader, []);
      return ParseFile(options, fileSnapshot.Version, text, uri, cancellationToken);
    }

    var syntaxDeserializer = new SyntaxDeserializer(new TextDecoder(reader.ReadToEnd()));
    var filesContainer = syntaxDeserializer.ReadFilesContainer();
    var filesModule = new FileModuleDefinition(SourceOrigin.NoToken);
    filesModule.SourceDecls.AddRange(
      filesContainer.Files.SelectMany(f => f.TopLevelDecls));

    return new DfyParseFileResult(null, uri,
      filesContainer.Files.Select(f => new Uri(f.Uri)).ToList(),
      new BatchErrorReporter(options), filesModule, syntaxDeserializer.SystemModuleModifiers);
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members)
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner with the given Errors sink.
  ///</summary>
  private static DfyParseFileResult ParseFile(DafnyOptions options, int? version, string /*!*/ content, Uri /*!*/ uri, CancellationToken cancellationToken) {
    var batchErrorReporter = new BatchErrorReporter(options);
    Parser parser = SetupParser(content, uri, batchErrorReporter, cancellationToken);
    parser.Parse();

    return new DfyParseFileResult(version, uri, [], batchErrorReporter, parser.theModule, parser.SystemModuleModifiers);
  }

  private static Parser SetupParser(string s /*!*/, Uri uri /*!*/,
    ErrorReporter errorReporter /*!*/, CancellationToken cancellationToken) {
    Contract.Requires(s != null);
    Contract.Requires(uri != null);
    System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(typeof(ParseErrors).TypeHandle);
    System.Runtime.CompilerServices.RuntimeHelpers.RunClassConstructor(typeof(ResolutionErrors).TypeHandle);
    byte[] /*!*/ buffer = cce.NonNull(Encoding.Default.GetBytes(s));
    var ms = new MemoryStream(buffer, false);
    var firstToken = new Token {
      Uri = uri
    };

    var errors = new Errors(errorReporter);

    var scanner = new Scanner(ms, errors, uri, firstToken: firstToken);
    return new Parser(errorReporter.Options, scanner, errors, cancellationToken);
  }

  public static async Task<ProgramParseResult> Parse(string source, Uri uri, ErrorReporter reporter) {
    var fs = new InMemoryFileSystem(ImmutableDictionary<Uri, string>.Empty.Add(uri, source));
    var parser = new ProgramParser(NullLogger<ProgramParser>.Instance, fs);
    var file = DafnyFile.HandleDafnyFile(fs, reporter, reporter.Options, uri, Token.NoToken, false);
    var files = new[] { file };
    return await parser.ParseFiles(uri.ToString(), files, reporter, CancellationToken.None);
  }
}
