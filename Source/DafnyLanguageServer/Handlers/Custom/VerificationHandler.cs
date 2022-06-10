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
using OmniSharp.Extensions.JsonRpc.Server;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Handlers.Custom;

[Parallel]
[Method(DafnyRequestNames.VerifySymbol, Direction.ClientToServer)]
public record VerificationParams : TextDocumentPositionParams, IRequest;

[Parallel]
[Method(DafnyRequestNames.CancelVerifySymbol, Direction.ClientToServer)]
public record CancelVerificationParams : TextDocumentPositionParams, IRequest;

public class VerificationHandler : IJsonRpcRequestHandler<VerificationParams, Unit>, IJsonRpcRequestHandler<CancelVerificationParams, Unit> {
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
    var failedTaskRuns = 0;
    Exception? lastException = null;
    foreach (var taskToRun in tasks) {
      try {
        var verifiedDocuments = documentLoader.Verify(translatedDocument, taskToRun, CancellationToken.None);
        documentHandler.ForwardDiagnostics(request.TextDocument.Uri, verifiedDocuments);
      } catch (InvalidOperationException e) {
        if (e.Message.Contains("already completed") || e.Message.Contains("ongoing run")) {
          failedTaskRuns++;
          lastException = e;
        } else {
          throw;
        }
      }
    }

    if (failedTaskRuns == tasks.Count) {
      throw new RequestException(412,
        "No verification can be started at this position because it's already running or completed", null, lastException!);
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
        if (e.Message.Contains("no ongoing run")) {
          throw new RequestException(412,
            "Verification can not be cancelled at this position because there is none running", null, e);
        }

        throw;
      }
    }

    return Unit.Value;
  }
}