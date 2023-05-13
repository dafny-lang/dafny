using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors {
  public class Relocator : IRelocator {
    public const string OutdatedPrefix = "Outdated: ";

    private readonly ILogger logger;
    private readonly ILogger<SignatureAndCompletionTable> loggerSymbolTable;

    public Relocator(
      ILogger<Relocator> logger,
      ILogger<SignatureAndCompletionTable> loggerSymbolTable
      ) {
      this.logger = logger;
      this.loggerSymbolTable = loggerSymbolTable;
    }

    public ChangeProcessor GetChangeProcessor(DidChangeTextDocumentParams changes, CancellationToken cancellationToken) {
      return new ChangeProcessor(logger, loggerSymbolTable, changes.ContentChanges, cancellationToken);
    }
  }
}
