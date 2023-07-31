using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Util;
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

    var resolvedCompilation = await projectManager.CompilationManager.ResolvedCompilation;
    if (resolvedCompilation.Program.FindNode(request.TextDocument.Uri.ToUri(), request.Position.ToDafnyPosition()) is ICanVerify verifiable) {
      return await projectManager.CompilationManager.VerifyTask(resolvedCompilation, verifiable);
    }

    return false;
  }

  public async Task<bool> Handle(CancelVerificationParams request, CancellationToken cancellationToken) {
    var projectManager = await projects.GetProjectManager(request.TextDocument);
    if (projectManager == null) {
      return false;
    }

    
    var resolvedCompilation = await projectManager.CompilationManager.ResolvedCompilation;
    if (resolvedCompilation.Program.FindNode(request.TextDocument.Uri.ToUri(), request.Position.ToDafnyPosition()) is ICanVerify verifiable) {
      var implementations = resolvedCompilation.ImplementationsPerVerifiable[verifiable].Values;
      foreach (var (taskToRun,_) in implementations) {
        taskToRun.Cancel();
      }
    }
    

    return true;
  }
}
