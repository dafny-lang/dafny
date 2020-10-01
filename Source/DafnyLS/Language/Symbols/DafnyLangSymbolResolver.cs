using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
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
      RunDafnyResolver(textDocument, program);
      foreach(var module in program.Modules()) {
        //module.Accept();
        var visitor = new DafnyVisitor();
        foreach(var declaration in module.TopLevelDecls) {
          cancellationToken.ThrowIfCancellationRequested();
          //visitor.Visit(declaration);
        }
      }
      return new SymbolTable();
    }

    private void RunDafnyResolver(TextDocumentItem document, Microsoft.Dafny.Program program) {
      var errorReporter = program.reporter;
      var errorsBefore = errorReporter.AllMessages[ErrorLevel.Error].Count;
      var resolver = new Resolver(program);
      resolver.ResolveProgram(program);
      var resolverErrors = errorReporter.AllMessages[ErrorLevel.Error].Count - errorsBefore;
      if(resolverErrors > 0) {
        _logger.LogDebug("encountered {} errors while resolving {}", resolverErrors, document.Uri);
      }
    }

    private class DafnyVisitor : TopDownVisitor<Unit> {
      public DafnyVisitor() {
      }
    }
  }
}
