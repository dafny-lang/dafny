using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using static Microsoft.Dafny.ParseErrors;

namespace Microsoft.Dafny;

public record DfyParseResult(
  BatchErrorReporter ErrorReporter,
  FileModuleDefinition Module,
  IReadOnlyList<Action<SystemModuleManager>> ModifyBuiltins
  );

public class ProgramParser {
  protected readonly ILogger<ProgramParser> logger;
  private readonly IFileSystem fileSystem;

  public ProgramParser() : this(NullLogger<ProgramParser>.Instance, OnDiskFileSystem.Instance) {
  }

  public ProgramParser(ILogger<ProgramParser> logger, IFileSystem fileSystem) {
    this.logger = logger;
    this.fileSystem = fileSystem;
  }

  public virtual Program ParseFiles(string programName, IReadOnlyList<DafnyFile> files,
    ErrorReporter errorReporter,
    CancellationToken cancellationToken) {
    var options = errorReporter.Options;
    var builtIns = new SystemModuleManager(options);
    var defaultModule = new DefaultModuleDefinition(files.Where(f => !f.IsPreverified).Select(f => f.Uri).ToList());

    var verifiedRoots = files.Where(df => df.IsPreverified).Select(df => df.Uri).ToHashSet();
    var compiledRoots = files.Where(df => df.IsPrecompiled).Select(df => df.Uri).ToHashSet();
    var compilation = new CompilationData(errorReporter, defaultModule.Includes, defaultModule.RootSourceUris, verifiedRoots,
      compiledRoots);
    var program = new Program(
      programName,
      new LiteralModuleDecl(defaultModule, null, Guid.NewGuid()),
      builtIns,
      errorReporter, compilation
    );

    foreach (var dafnyFile in files) {
      cancellationToken.ThrowIfCancellationRequested();
      if (options.Trace) {
        options.OutputWriter.WriteLine("Parsing " + dafnyFile.FilePath);
      }

      if (options.XmlSink is { IsOpen: true } && dafnyFile.Uri.IsFile) {
        options.XmlSink.WriteFileFragment(dafnyFile.Uri.LocalPath);
      }

      var parseResult = ParseFileWithErrorHandling(
        errorReporter.Options,
        dafnyFile.GetContent,
        dafnyFile.Origin,
        dafnyFile.Uri,
        cancellationToken
      );
      if (parseResult.ErrorReporter.ErrorCount != 0) {
        logger.LogDebug($"encountered {parseResult.ErrorReporter.ErrorCount} errors while parsing {dafnyFile.Uri}");
      }

      AddParseResultToProgram(parseResult, program);
    }

    if (!(options.DisallowIncludes || options.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate)) {
      var includedModules = TryParseIncludes(files, defaultModule.Includes.ToList(),
        builtIns, errorReporter, cancellationToken);

      foreach (var module in includedModules) {
        AddParseResultToProgram(module, program);
      }
    }

    if (options.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate) {
      var dependencyMap = new DependencyMap();
      dependencyMap.AddIncludes(defaultModule.Includes);
      dependencyMap.PrintMap(options);
    }

    if (errorReporter.ErrorCount == 0) {
      DafnyMain.MaybePrintProgram(program, options.DafnyPrintFile, false);
    }

    ShowWarningsForIncludeCycles(program);

    return program;
  }

  private DfyParseResult ParseFileWithErrorHandling(DafnyOptions options,
    Func<TextReader> getContent,
    IToken origin,
    Uri uri,
    CancellationToken cancellationToken) {
    try {
      return ParseFile(options, getContent, uri, cancellationToken);
    } catch (IOException e) {
      if (origin == null) {
        throw;
      }

      var reporter = new BatchErrorReporter(options);
      reporter.Error(MessageSource.Parser, origin,
        $"Unable to open the file {uri} because {e.Message}.");
      return new DfyParseResult(reporter, new FileModuleDefinition(Token.NoToken), new Action<SystemModuleManager>[] { });
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
        "[internal error] Parser exception: " + e.Message + (!options.Verbose ? "" :
          "\n" + e.StackTrace));
      return new DfyParseResult(reporter, new FileModuleDefinition(Token.NoToken), new Action<SystemModuleManager>[] { });
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

  private static void AddParseResultToProgram(DfyParseResult parseResult, Program program) {
    var defaultModule = program.DefaultModuleDef;
    var fileModule = parseResult.Module;
    program.Files.Add(fileModule);

    foreach (var modify in parseResult.ModifyBuiltins) {
      modify(program.SystemModuleManager);
    }

    parseResult.ErrorReporter.CopyDiagnostics(program.Reporter);

    foreach (var declToMove in fileModule.DefaultClasses.Concat(fileModule.SourceDecls)) {
      declToMove.EnclosingModuleDefinition = defaultModule;
      if (declToMove is LiteralModuleDecl literalModuleDecl) {
        literalModuleDecl.ModuleDef.EnclosingModule = defaultModule;
      }

      if (declToMove is ClassLikeDecl { NonNullTypeDecl: { } nonNullTypeDecl }) {
        nonNullTypeDecl.EnclosingModuleDefinition = defaultModule;
      }
      if (declToMove is DefaultClassDecl defaultClassDecl) {
        foreach (var member in defaultClassDecl.Members) {
          defaultModule.DefaultClass.Members.Add(member);
          member.EnclosingClass = defaultModule.DefaultClass;
        }
      } else {
        defaultModule.SourceDecls.Add(declToMove);
      }
    }

    foreach (var include in fileModule.Includes) {
      defaultModule.Includes.Add(include);
    }

    foreach (var prefixNamedModule in fileModule.PrefixNamedModules) {
      defaultModule.PrefixNamedModules.Add(prefixNamedModule);
    }

    defaultModule.DefaultClass.SetMembersBeforeResolution();
  }

  public IList<DfyParseResult> TryParseIncludes(
    IReadOnlyList<DafnyFile> files,
    IEnumerable<Include> roots,
    SystemModuleManager systemModuleManager,
    ErrorReporter errorReporter,
    CancellationToken cancellationToken
  ) {
    var stack = new Stack<DafnyFile>();
    var result = new List<DfyParseResult>();
    var resolvedFiles = new HashSet<Uri>();
    foreach (var rootFile in files) {
      resolvedFiles.Add(rootFile.Uri);
    }

    foreach (var root in roots) {
      var dafnyFile = IncludeToDafnyFile(systemModuleManager, errorReporter, root);
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
        errorReporter.Options,
        top.GetContent,
        top.Origin,
        top.Uri,
        cancellationToken
      );
      result.Add(parseIncludeResult);

      foreach (var include in parseIncludeResult.Module.Includes) {
        var dafnyFile = IncludeToDafnyFile(systemModuleManager, errorReporter, include);
        if (dafnyFile != null) {
          stack.Push(dafnyFile);
        }
      }
    }

    return result;
  }

  private DafnyFile IncludeToDafnyFile(SystemModuleManager systemModuleManager, ErrorReporter errorReporter, Include include) {
    try {
      return new DafnyFile(systemModuleManager.Options, include.IncludedFilename, include.tok,
        () => fileSystem.ReadFile(include.IncludedFilename));
    } catch (IllegalDafnyFile) {
      errorReporter.Error(MessageSource.Parser, include.tok,
        $"Unable to open the include {include.IncludedFilename}.");
      return null;
    }
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members) from "filename"
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner.
  ///</summary>
  protected virtual DfyParseResult ParseFile(DafnyOptions options, Func<TextReader> getReader,
    Uri uri, CancellationToken cancellationToken) /* throws System.IO.IOException */ {
    Contract.Requires(uri != null);
    using var reader = getReader();
    var text = SourcePreprocessor.ProcessDirectives(reader, new List<string>());
    return ParseFile(options, text, uri, cancellationToken);
  }

  ///<summary>
  /// Parses top-level things (modules, classes, datatypes, class members)
  /// and appends them in appropriate form to "module".
  /// Returns the number of parsing errors encountered.
  /// Note: first initialize the Scanner with the given Errors sink.
  ///</summary>
  private static DfyParseResult ParseFile(DafnyOptions options, string /*!*/ s, Uri /*!*/ uri, CancellationToken cancellationToken) {
    var batchErrorReporter = new BatchErrorReporter(options);
    Parser parser = SetupParser(s, uri, batchErrorReporter, cancellationToken);
    parser.Parse();

    if (parser.theModule.DefaultClass.Members.Count == 0 && parser.theModule.Includes.Count == 0 && !parser.theModule.SourceDecls.Any()
        && (parser.theModule.PrefixNamedModules == null || parser.theModule.PrefixNamedModules.Count == 0)) {
      batchErrorReporter.Warning(MessageSource.Parser, ErrorId.p_file_has_no_code, new Token(1, 1) { Uri = uri }, "File contains no code");
    }

    return new DfyParseResult(batchErrorReporter, parser.theModule, parser.SystemModuleModifiers);
  }

  private static Parser SetupParser(string /*!*/ s, Uri /*!*/ uri, ErrorReporter /*!*/ errorReporter, CancellationToken cancellationToken) {
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

  public Program Parse(string source, Uri uri, ErrorReporter reporter) {
    var files = new[] { new DafnyFile(reporter.Options, uri, null, () => new StringReader(source)) };
    return ParseFiles(uri.ToString(), files, reporter, CancellationToken.None);
  }
}
