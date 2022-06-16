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
public record VerificationParams : TextDocumentPositionParams, IRequest<bool>;

[Parallel]
[Method(DafnyRequestNames.CancelVerifySymbol, Direction.ClientToServer)]
public record CancelVerificationParams : TextDocumentPositionParams, IRequest<bool>;

public class VerificationHandler : IJsonRpcRequestHandler<VerificationParams, bool>, IJsonRpcRequestHandler<CancelVerificationParams, bool> {
  private readonly ILogger logger;
  private readonly IDocumentDatabase documents;
  private readonly ITextDocumentLoader documentLoader;

  public VerificationHandler(
    ILogger<VerificationHandler> logger,
    IDocumentDatabase documents,
    ITextDocumentLoader documentLoader) {
    this.logger = logger;
    this.documents = documents;
    this.documentLoader = documentLoader;
  }

  public async Task<bool> Handle(VerificationParams request, CancellationToken cancellationToken) {
    if (!documents.Documents.TryGetValue(request.TextDocument.Uri, out var documentEntry)) {
      return false;
    }

    var translatedDocument = await documentEntry.TranslatedDocument;
    var requestPosition = request.Position;
    var tasks = GetTasksAtPosition(translatedDocument, requestPosition).ToList();
    foreach (var taskToRun in tasks) {
      var verifiedDocuments = documentLoader.Verify(translatedDocument, taskToRun, CancellationToken.None);
      documentEntry.Observe(verifiedDocuments);
    }

    return !documentEntry.Idle;
  }

  private static IEnumerable<IImplementationTask> GetTasksAtPosition(DafnyDocument translatedDocument, Position requestPosition) {
    return translatedDocument.VerificationTasks!.Where(t => {
      var lspPosition = t.Implementation.tok.GetLspPosition();
      return lspPosition.Equals(requestPosition);
    });
  }

  public async Task<bool> Handle(CancelVerificationParams request, CancellationToken cancellationToken) {
    if (!documents.Documents.TryGetValue(request.TextDocument.Uri, out var documentEntry)) {
      return false;
    }

    var translatedDocument = await documentEntry.TranslatedDocument;
    var requestPosition = request.Position;
    foreach (var taskToRun in GetTasksAtPosition(translatedDocument, requestPosition)) {
      taskToRun.Cancel();
    }

    return true;
  }
}