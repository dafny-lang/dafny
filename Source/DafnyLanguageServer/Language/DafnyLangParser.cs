using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using Microsoft.Boogie;

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

    private readonly ILogger logger;
    private readonly SemaphoreSlim mutex = new(1);

    private DafnyLangParser(ILogger<DafnyLangParser> logger) {
      this.logger = logger;
    }

    /// <summary>
    /// Factory method to safely create a new instance of the parser.
    /// </summary>
    /// <param name="logger">A logger instance that may be used by this parser instance.</param>
    /// <returns>A safely created dafny parser instance.</returns>
    public static DafnyLangParser Create(ILogger<DafnyLangParser> logger) {
      return new DafnyLangParser(logger);
    }

    public Dafny.Program CreateUnparsed(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);
      try {
        return NewDafnyProgram(document, errorReporter);
      }
      finally {
        mutex.Release();
      }
    }

    public Dafny.Program Parse(TextDocumentItem document, ErrorReporter errorReporter, CancellationToken cancellationToken) {
      mutex.Wait(cancellationToken);
      var program = NewDafnyProgram(document, errorReporter);
      try {
        var parseErrors = Parser.Parse(
          document.Text,
          // We use the full path as filename so we can better re-construct the DocumentUri for the definition lookup.
          document.Uri.ToString(),
          document.Uri.ToString(),
          program.DefaultModule,
          program.BuiltIns,
          errorReporter
        );
        if (parseErrors != 0) {
          logger.LogDebug("encountered {ErrorCount} errors while parsing {DocumentUri}", parseErrors, document.Uri);
        }

        if (!TryParseIncludesOfModule(program.DefaultModule, program.BuiltIns, errorReporter, cancellationToken)) {
          logger.LogDebug("encountered error while parsing the includes of {DocumentUri}", document.Uri);
        }

        return program;
      } catch (Exception e) {
        logger.LogDebug(e, "encountered an exception while parsing {DocumentUri}", document.Uri);
        var internalErrorDummyToken = new Token {
          Filename = document.Uri.ToString(),
          line = 1,
          col = 1,
          pos = 0,
          val = string.Empty
        };
        errorReporter.Error(MessageSource.Parser, internalErrorDummyToken, "[internal error] Parser exception: " + e.Message);
        return program;
      }
      finally {
        mutex.Release();
      }
    }

    private static Dafny.Program NewDafnyProgram(TextDocumentItem document, ErrorReporter errorReporter) {
      // Ensure that the statically kept scopes are empty when parsing a new document.
      Type.ResetScopes();
      return new Dafny.Program(
        document.Uri.ToString(),
        new LiteralModuleDecl(new DefaultModuleDecl(), null),
        // BuiltIns cannot be initialized without Type.ResetScopes() before.
        new BuiltIns(),
        errorReporter
      );
    }

    public void Dispose() {
      mutex.Dispose();
    }

    // TODO The following methods are based on the ones from DafnyPipeline/DafnyMain.cs.
    //      It could be convenient to adapt them in the main-repo so location info could be extracted.
    private bool TryParseIncludesOfModule(
      ModuleDecl module,
      BuiltIns builtIns,
      ErrorReporter errorReporter,
      CancellationToken cancellationToken
    ) {
      var errors = new Errors(errorReporter);
      // Issue #40:
      // A HashSet must not be used here since equals treats A included by B not equal to A included by C.
      // In contrast, the compareTo-Method treats them as the same.
      var resolvedIncludes = new SortedSet<Include>();
      var dependencyMap = new DependencyMap();
      dependencyMap.AddIncludes(resolvedIncludes);

      bool newIncludeParsed = true;
      while (newIncludeParsed) {
        cancellationToken.ThrowIfCancellationRequested();
        newIncludeParsed = false;
        // Parser.Parse appears to modify the include list; thus, we create a copy to avoid concurrent modifications.
        var moduleIncludes = new List<Include>(((LiteralModuleDecl)module).ModuleDef.Includes);
        dependencyMap.AddIncludes(moduleIncludes);
        foreach (var include in moduleIncludes) {
          bool isNewInclude = resolvedIncludes.Add(include);
          if (isNewInclude) {
            newIncludeParsed = true;
            if (!TryParseInclude(include, module, builtIns, errorReporter, errors)) {
              return false;
            }
          }
        }
      }

      return true;
    }

    private bool TryParseInclude(Include include, ModuleDecl module, BuiltIns builtIns, ErrorReporter errorReporter, Errors errors) {
      try {
        var dafnyFile = new DafnyFile(include.IncludedFilename);
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
        if (errorCount != 0) {
          errorReporter.Error(MessageSource.Parser, include.tok, $"{errorCount} parse error(s) detected in {include.IncludedFilename}");
          return false;
        }
      } catch (IllegalDafnyFile e) {
        errorReporter.Error(MessageSource.Parser, include.tok, $"Include of file '{include.IncludedFilename}' failed.");
        logger.LogDebug(e, "encountered include of illegal dafny file {Filename}", include.IncludedFilename);
        return false;
      } catch (IOException e) {
        errorReporter.Error(MessageSource.Parser, include.tok, $"Unable to open the include {include.IncludedFilename}.");
        logger.LogDebug(e, "could not open file {Filename}", include.IncludedFilename);
        return false;
      }
      return true;
    }
  }
}
