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
  private readonly IDocumentDatabase documents;

  public VerificationHandler(
    IDocumentDatabase documents) {
    this.documents = documents;
  }

  public async Task<bool> Handle(VerificationParams request, CancellationToken cancellationToken) {
    var documentManager = documents.GetDocumentManager(request.TextDocument);
    if (documentManager == null) {
      return false;
    }

    var translatedDocument = await documentManager.Compilation.TranslatedDocument;
    var requestPosition = request.Position;
    var someTasksAreRunning = false;
    var tasksAtPosition = GetTasksAtPosition(translatedDocument, requestPosition);
    foreach (var taskToRun in tasksAtPosition) {
      someTasksAreRunning |= documentManager.Compilation.VerifyTask(translatedDocument, taskToRun);
    }
    return someTasksAreRunning;
  }

  private static IEnumerable<IImplementationTask> GetTasksAtPosition(DocumentAfterTranslation document, Position requestPosition) {
    return document.VerificationTasks.Where(t => {
      var lspPosition = t.Implementation.tok.GetLspPosition();
      return lspPosition.Equals(requestPosition);
    });
  }

  public async Task<bool> Handle(CancelVerificationParams request, CancellationToken cancellationToken) {
    var documentManager = documents.GetDocumentManager(request.TextDocument);
    if (documentManager == null) {
      return false;
    }

    var translatedDocument = await documentManager.Compilation.TranslatedDocument;
    var requestPosition = request.Position;
    foreach (var taskToRun in GetTasksAtPosition(translatedDocument, requestPosition)) {
      taskToRun.Cancel();
    }

    return true;
  }
}
