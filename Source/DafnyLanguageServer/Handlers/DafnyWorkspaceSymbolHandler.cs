using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Workspace;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyWorkspaceSymbolHandler : WorkspaceSymbolsHandlerBase {
    private readonly ILogger logger;
    private readonly IProjectDatabase projects;
    private readonly DafnyOptions dafnyOptions;

    public DafnyWorkspaceSymbolHandler(ILogger<DafnyWorkspaceSymbolHandler> logger, IProjectDatabase projects, DafnyOptions dafnyOptions) {
      this.logger = logger;
      this.projects = projects;
      this.dafnyOptions = dafnyOptions;
    }

    protected override WorkspaceSymbolRegistrationOptions CreateRegistrationOptions(WorkspaceSymbolCapability capability,
      ClientCapabilities clientCapabilities) {
      return new WorkspaceSymbolRegistrationOptions {
        WorkDoneProgress = false
      };
    }

    public override async Task<Container<SymbolInformation>?> Handle(WorkspaceSymbolParams request, CancellationToken cancellationToken) {
      var queryText = request.Query.ToLower();
      var result = new Dictionary<SymbolInformation, int>();
      foreach (var projectManager in projects.Managers) {
        cancellationToken.ThrowIfCancellationRequested();
        var state = await projectManager.GetStateAfterParsingAsync();
        foreach (var def in state.SymbolTable.Symbols) {
          cancellationToken.ThrowIfCancellationRequested();

          if (!def.Kind.HasValue) {
            logger.LogWarning($"Definition without kind in symbol table: {def}");
            continue;
          }

          // CreateLocation called below uses the .Uri field of Tokens which
          // seems to occasionally be null while testing this from VSCode
          if (def.NavigationToken == null || def.NavigationToken.Uri == null) {
            logger.LogWarning($"Definition without name token in symbol table: {def}");
            continue;
          }
          if (def.NavigationToken.val == null) {
            logger.LogWarning($"Definition without name in symbol table: {def}");
            continue;
          }

          // This matching could be improved by using the qualified name of the symbol here.
          var name = def.NavigationToken.val;
          if (name.ToLower().Contains(queryText)) {
            // The fewer extra characters there are in the string, the
            // better the match.
            var matchDistance = name.Length - queryText.Length;
            result.TryAdd(new SymbolInformation {
              Name = name,
              ContainerName = def.Kind.ToString(),
              Kind = def.Kind.Value,
              Location = DiagnosticUtil.CreateLocation(def.NavigationToken)
            }, matchDistance);
          }
        }
      }

      return result.OrderBy(kvPair => kvPair.Value).Select(kvPair => kvPair.Key).ToImmutableList();
    }
  }
}