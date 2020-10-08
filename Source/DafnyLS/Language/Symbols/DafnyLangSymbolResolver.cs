using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Language.Symbols {
  /// <summary>
  /// Symbol resolver that utilizes dafny-lang to resolve the symbols.
  /// </summary>
  /// <remarks>
  /// dafny-lang makes use of static members and assembly loading. Since thread-safety of this is not guaranteed,
  /// this parser serializes all invocations.
  /// </remarks>
  internal class DafnyLangSymbolResolver : ISymbolResolver {
    private readonly ILogger _logger;

    public DafnyLangSymbolResolver(ILogger<DafnyLangSymbolResolver> logger) {
      _logger = logger;
    }

    public async Task<SymbolTable> ResolveSymbolsAsync(TextDocumentItem textDocument, Microsoft.Dafny.Program program, CancellationToken cancellationToken) {
      var rootSymbolTable = new SymbolTable();
      int parserErrors = GetErrorCount(program);
      if(parserErrors > 0) {
        _logger.LogTrace("document {} had {} parser errors, skipping symbol resolution", textDocument.Uri, parserErrors);
        return rootSymbolTable;
      }
      if(RunDafnyResolver(textDocument, program)) {
        // TODO Unsafe assumption: This requires that the previous step (parser) defines the parsed document as the default module.
        // TODO Any reason to retrieve the symbols defined in other modules (aka documents)?
        var visitor = new SymbolResolvingVisitor(_logger, rootSymbolTable);
        visitor.Visit(program.DefaultModuleDef);
      }
      return rootSymbolTable;
    }

    private static int GetErrorCount(Microsoft.Dafny.Program program) {
      return program.reporter.AllMessages[ErrorLevel.Error].Count;
    }

    private bool RunDafnyResolver(TextDocumentItem document, Microsoft.Dafny.Program program) {
      var resolver = new Resolver(program);
      resolver.ResolveProgram(program);
      int resolverErrors = GetErrorCount(program);
      if(resolverErrors > 0) {
        _logger.LogDebug("encountered {} errors while resolving {}", resolverErrors, document.Uri);
        return false;
      }
      return true;
    }
  }
}
