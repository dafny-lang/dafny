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
  private readonly IProjectDatabase projects;

  public VerificationHandler(
    IProjectDatabase projects) {
    this.projects = projects;
  }

  public async Task<bool> Handle(VerificationParams request, CancellationToken cancellationToken) {
    var projectManager = await projects.GetProjectManager(request.TextDocument);
    if (projectManager == null) {
      return false;
    }

    var translatedCompilation = await projectManager.CompilationManager.TranslatedCompilation;
    var someTasksAreRunning = false;
    var tasksAtPosition = GetTasksAtPosition(translatedCompilation, request);
    foreach (var taskToRun in tasksAtPosition) {
      someTasksAreRunning |= projectManager.CompilationManager.VerifyTask(translatedCompilation, taskToRun);
    }
    return someTasksAreRunning;
  }

  private static IEnumerable<IImplementationTask> GetTasksAtPosition(CompilationAfterTranslation compilation, TextDocumentPositionParams request) {
    var uri = request.TextDocument.Uri.ToUri();
    return compilation.VerificationTasks.Where(t => {
      if (((IToken)t.Implementation.tok).Uri != uri) {
        return false;
      }
      var lspPosition = t.Implementation.tok.GetLspPosition();
      return lspPosition.Equals(request.Position);
    });
  }

  public async Task<bool> Handle(CancelVerificationParams request, CancellationToken cancellationToken) {
    var projectManager = await projects.GetProjectManager(request.TextDocument);
    if (projectManager == null) {
      return false;
    }

    var translatedDocument = await projectManager.CompilationManager.TranslatedCompilation;
    foreach (var taskToRun in GetTasksAtPosition(translatedDocument, request)) {
      taskToRun.Cancel();
    }

    return true;
  }
}
