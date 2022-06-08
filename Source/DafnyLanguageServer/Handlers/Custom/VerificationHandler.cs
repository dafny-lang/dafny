using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom;

[Parallel]
[Method(DafnyRequestNames.VerifySymbol, Direction.ClientToServer)]
public record VerificationParams : TextDocumentPositionParams, IRequest {
}

[Parallel]
[Method(DafnyRequestNames.CancelVerifySymbol, Direction.ClientToServer)]
public record CancelVerificationParams : TextDocumentPositionParams, IRequest {

}

public class VerificationHandler : IJsonRpcNotificationHandler<VerificationParams>, IJsonRpcNotificationHandler<CancelVerificationParams> {
  private readonly ILogger logger;
  private readonly IDocumentDatabase documents;
  private readonly DafnyTextDocumentHandler documentHandler;
  private readonly ITextDocumentLoader documentLoader;

  public VerificationHandler(ILogger<VerificationHandler> logger, IDocumentDatabase documents,
    DafnyTextDocumentHandler documentHandler,
    ITextDocumentLoader documentLoader) {
    this.logger = logger;
    this.documents = documents;
    this.documentHandler = documentHandler;
    this.documentLoader = documentLoader;
  }

  public async Task<Unit> Handle(VerificationParams request, CancellationToken cancellationToken) {
    if (!documents.Documents.TryGetValue(request.TextDocument.Uri, out var documentEntry)) {
      return Unit.Value;

    }

    var translatedDocument = await documentEntry.TranslatedDocument;
    var requestPosition = request.Position;
    var tasks = GetTasksAtPosition(translatedDocument, requestPosition).ToList();
    foreach (var taskToRun in tasks) {
      var verifiedDocuments = documentLoader.Verify(translatedDocument, taskToRun, CancellationToken.None);
      documentHandler.ForwardDiagnostics(request.TextDocument.Uri, verifiedDocuments);
    }

    return Unit.Value;
  }

  private static IEnumerable<IImplementationTask> GetTasksAtPosition(DafnyDocument translatedDocument, Position requestPosition) {
    return translatedDocument.VerificationTasks!.Where(t => {
      var lspPosition = t.Implementation.tok.GetLspPosition();
      return lspPosition.Equals(requestPosition);
    });
  }

  public async Task<Unit> Handle(CancelVerificationParams request, CancellationToken cancellationToken) {
    if (!documents.Documents.TryGetValue(request.TextDocument.Uri, out var documentEntry)) {
      return Unit.Value;
    }

    var translatedDocument = await documentEntry.TranslatedDocument;
    var requestPosition = request.Position;
    foreach (var taskToRun in GetTasksAtPosition(translatedDocument, requestPosition)) {
      try {
        taskToRun.Cancel();
      } catch (InvalidOperationException e) {
        if (!e.Message.Contains("run")) {
          throw;
        }
      }
    }

    return Unit.Value;
  }
}