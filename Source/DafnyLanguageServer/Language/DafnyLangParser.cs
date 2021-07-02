using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Parser implementation that makes use of the parse of dafny-lang. It may only be initialized exactly once since
  /// it requires initial setup of static members.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this parser serializes all invocations.
  /// </remarks>
  public sealed class DafnyLangParser : IDafnyParser, IDisposable {
    private static readonly object _initializationSyncObject = new();
    private static bool _initialized;

    private readonly ILogger _logger;
    private readonly SemaphoreSlim _mutex = new(1);

    private DafnyLangParser(ILogger<DafnyLangParser> logger) {
      _logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the parser. It ensures that global/static
    /// settings are set exactly ones.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this parser instance.</param>
    /// <returns>A safely created dafny parser instance.</returns>
    public static DafnyLangParser Create(ILogger<DafnyLangParser> logger) {
      lock(_initializationSyncObject) {
        if(!_initialized) {
          // TODO no error reporter is supplied at this time since it appears that there is not any usage inside dafny.
          DafnyOptions.Install(new DafnyOptions());
          DafnyOptions.Clo.ApplyDefaultOptions();
          DafnyOptions.O.PrintIncludesMode = DafnyOptions.IncludesModes.None;
          _initialized = true;
        }
        logger.LogTrace("initialized the dafny pipeline...");
        return new DafnyLangParser(logger);
      }
    }

    public async Task<Dafny.Program> ParseAsync(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      await _mutex.WaitAsync(cancellationToken);
      try {
        // Ensure that the statically kept scopes are empty when parsing a new document.
        Type.ResetScopes();
        var module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        var builtIns = new BuiltIns();
        var parseErrors = Parser.Parse(
          document.Text,
          document.Uri.GetFileSystemPath(),
          // We use the full path as filename so we can better re-construct the DocumentUri for the definition lookup.
          document.Uri.GetFileSystemPath(),
          module,
          builtIns,
          errorReporter
        );
        if(parseErrors != 0) {
          _logger.LogDebug("encountered {ErrorCount} errors while parsing {DocumentUri}", parseErrors, document.Uri);
        }
        if(!TryParseIncludesOfModule(module, builtIns, errorReporter)) {
          _logger.LogDebug("encountered error while parsing the includes of {DocumentUri}", document.Uri);
        }
        // TODO Remove PoC workaround: the file system path is used as a program name to
        return new Dafny.Program(document.Uri.GetFileSystemPath(), module, builtIns, errorReporter);
      } finally {
        _mutex.Release();
      }
    }

    public void Dispose() {
      _mutex.Dispose();
    }

    // TODO The following methods are based on the ones from DafnyPipeline/DafnyMain.cs.
    //      It could be convenient to adapt them in the main-repo so location info could be extracted.
    public bool TryParseIncludesOfModule(ModuleDecl module, BuiltIns builtIns, ErrorReporter errorReporter) {
      var errors = new Errors(errorReporter);
      // Issue #40:
      // A HashSet must not be used here since equals treats A included by B not equal to A included by C.
      // In contrast, the compareTo-Method treats them as the same.
      var resolvedIncludes = new SortedSet<Include>();
      var dependencyMap = new DependencyMap();
      dependencyMap.AddIncludes(resolvedIncludes);

      bool newIncludeParsed = true;
      while(newIncludeParsed) {
        newIncludeParsed = false;
        // Parser.Parse appears to modify the include list; thus, we create a copy to avoid concurrent modifications.
        var moduleIncludes = new List<Include>(((LiteralModuleDecl)module).ModuleDef.Includes);
        dependencyMap.AddIncludes(moduleIncludes);
        foreach(var include in moduleIncludes) {
          bool isNewInclude = resolvedIncludes.Add(include);
          if(isNewInclude) {
            newIncludeParsed = true;
            if(!TryParseInclude(include, module, builtIns, errorReporter, errors)) {
              return false;
            }
          }
        }
      }

      return true;
    }

    private bool TryParseInclude(Include include,  ModuleDecl module, BuiltIns builtIns, ErrorReporter errorReporter, Errors errors) {
      try {
        var dafnyFile = new DafnyFile(include.includedFilename);
        int errorCount = Parser.Parse(
          useStdin: false,
          dafnyFile.SourceFileName,
          include,
          module,
          builtIns,
          errors,
          verifyThisFile: false,
          compileThisFile: false
        );
        if(errorCount != 0) {
          errorReporter.Error(MessageSource.Parser, include.tok, $"{errorCount} parse error(s) detected in {include.includedFilename}");
          return false;
        }
      } catch(IllegalDafnyFile e) {
        errorReporter.Error(MessageSource.Parser, include.tok, $"Include of file {include.includedFilename} failed.");
        _logger.LogDebug(e, "encountered include of illegal dafny file {Filename}", include.includedFilename);
        return false;
      } catch(IOException e) {
        errorReporter.Error(MessageSource.Parser, include.tok, $"Unable to open the include {include.includedFilename}.");
        _logger.LogDebug(e, "could not open file {Filename}", include.includedFilename);
        return false;
      }
      return true;
    }
  }
}
