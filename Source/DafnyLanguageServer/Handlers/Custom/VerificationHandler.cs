using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using MediatR;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
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

    return await projectManager.CompilationManager.VerifyTask(new FilePosition(request.TextDocument.Uri.ToUri(), request.Position));
  }

  public async Task<bool> Handle(CancelVerificationParams request, CancellationToken cancellationToken) {
    var projectManager = await projects.GetProjectManager(request.TextDocument);
    if (projectManager == null) {
      return false;
    }


    var resolvedCompilation = await projectManager.CompilationManager.ResolvedCompilation;
    if (resolvedCompilation.Program.FindNode(request.TextDocument.Uri.ToUri(), request.Position.ToDafnyPosition()) is ICanVerify verifiable) {
      var implementations = resolvedCompilation.ImplementationsPerVerifiable.TryGetValue(verifiable, out var implementationsPerName)
        ? implementationsPerName.Values : Enumerable.Empty<ImplementationView>();
      foreach (var view in implementations) {
        view.Task.Cancel();
      }
    }


    return true;
  }
}
