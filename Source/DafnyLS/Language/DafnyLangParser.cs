using DafnyLS.Util;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Language {
  /// <summary>
  /// Parser implementation that makes use of the parse of dafny-lang. It may only be initialized exactly once since
  /// it requires initial setup of static members.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this parser serializes all invocations.
  /// </remarks>
  public sealed class DafnyLangParser : IDafnyParser, IDisposable {
    private static readonly object _initializationSyncObject = new object();
    private static bool _initialized;

    private readonly ILogger _logger;
    private readonly SemaphoreSlim _mutex = new SemaphoreSlim(1);

    private DafnyLangParser(ILogger<DafnyLangParser> logger) {
      _logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the parser. It may only be invoked
    /// once per application lifetime.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this parser instance.</param>
    /// <returns>A safely created dafny parser instance.</returns>
    /// <exception cref="InvalidOperationException">Thrown in case of multiple invocations of this factory method.</exception>
    public static DafnyLangParser Create(ILogger<DafnyLangParser> logger) {
      lock(_initializationSyncObject) {
        if(_initialized) {
          throw new InvalidOperationException($"{nameof(DafnyLangParser)} may only be initialized once");
        }
        // TODO no error reporter is supplied at this time since it appears that there is not any usage inside dafny.
        DafnyOptions.Install(new DafnyOptions());
        DafnyOptions.Clo.ApplyDefaultOptions();
        DafnyOptions.O.PrintIncludesMode = DafnyOptions.IncludesModes.None;
        // TODO Provide a counter-example model file.
        //DafnyOptions.O.ModelViewFile = ...;
        _initialized = true;
        logger.LogTrace("initialized the dafny pipeline...");
        return new DafnyLangParser(logger);
      }
    }

    public async Task<Microsoft.Dafny.Program> ParseAsync(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      await _mutex.WaitAsync(cancellationToken);
      try {
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
          _logger.LogDebug("encountered {} errors while parsing {}", parseErrors, document.Uri);
        }
        // TODO handle include errors
        // TODO handle errors of an include?
        // TODO includes that are opened by the editor (i.e. managed by the DocumentDatabase) should be taken from there.
        var includeError = Main.ParseIncludes(module, builtIns, new List<string>(), new Errors(errorReporter));
        if(includeError != null) {
          // TODO currently the diagnostic publisher ignores errors of foreign files. It should at least report
          //      that there were some errors.
          _logger.LogDebug("encountered error while parsing includes: {}", includeError);
        }
        // TODO Remove PoC workaround: the file system path is used as a program name to 
        return new Microsoft.Dafny.Program(document.Uri.GetFileSystemPath(), module, builtIns, errorReporter);
      } finally {
        _mutex.Release();
      }
    }

    public void Dispose() {
      _mutex.Dispose();
    }
  }
}
