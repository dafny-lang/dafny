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
        foreach (var def in state.SymbolTable.Definitions) {
          cancellationToken.ThrowIfCancellationRequested();
          // CreateLocation called below uses the .Uri field of Tokens which
          // seems to occasionally be null while testing this from VSCode
          if (def.NameToken == null || def.NameToken.Uri == null) {
            logger.LogWarning($"Definition without name token in symbol table: {def}");
            continue;
          }
          if (def.NameToken.val == null) {
            logger.LogWarning($"Definition without name in symbol table: {def}");
            continue;
          }

          // This matching could be improved by using the qualified name of the symbol here.
          var name = def.NameToken.val;
          if (name.ToLower().Contains(queryText)) {
            // The fewer extra characters there are in the string, the
            // better the match.
            var matchDistance = name.Length - queryText.Length;
            result.TryAdd(new SymbolInformation {
              Name = name,
              ContainerName = def.Kind.ToString(),
              Kind = FromDafnySymbolKind(def.Kind),
              Location = Workspace.Util.CreateLocation(def.NameToken)
            }, matchDistance);
          }
        }
      }

      return result.OrderBy(kvPair => kvPair.Value).Select(kvPair => kvPair.Key).ToImmutableList();
    }

    private SymbolKind FromDafnySymbolKind(DafnySymbolKind dafnySymbolKind) {
      // DafnySymbolKind is a copy of SymbolKind as described in its documentation.
      // This conversion function can be removed once it is no longer a copy.
      switch (dafnySymbolKind) {
        case DafnySymbolKind.File: return SymbolKind.File;
        case DafnySymbolKind.Module: return SymbolKind.Module;
        case DafnySymbolKind.Namespace: return SymbolKind.Namespace;
        case DafnySymbolKind.Package: return SymbolKind.Package;
        case DafnySymbolKind.Class: return SymbolKind.Class;
        case DafnySymbolKind.Method: return SymbolKind.Method;
        case DafnySymbolKind.Property: return SymbolKind.Property;
        case DafnySymbolKind.Field: return SymbolKind.Field;
        case DafnySymbolKind.Constructor: return SymbolKind.Constructor;
        case DafnySymbolKind.Enum: return SymbolKind.Enum;
        case DafnySymbolKind.Interface: return SymbolKind.Interface;
        case DafnySymbolKind.Function: return SymbolKind.Function;
        case DafnySymbolKind.Variable: return SymbolKind.Variable;
        case DafnySymbolKind.Constant: return SymbolKind.Constant;
        case DafnySymbolKind.String: return SymbolKind.String;
        case DafnySymbolKind.Number: return SymbolKind.Number;
        case DafnySymbolKind.Boolean: return SymbolKind.Boolean;
        case DafnySymbolKind.Array: return SymbolKind.Array;
        case DafnySymbolKind.Object: return SymbolKind.Object;
        case DafnySymbolKind.Key: return SymbolKind.Key;
        case DafnySymbolKind.Null: return SymbolKind.Null;
        case DafnySymbolKind.EnumMember: return SymbolKind.EnumMember;
        case DafnySymbolKind.Struct: return SymbolKind.Struct;
        case DafnySymbolKind.Event: return SymbolKind.Event;
        case DafnySymbolKind.Operator: return SymbolKind.Operator;
        case DafnySymbolKind.TypeParameter: return SymbolKind.TypeParameter;
        default: throw new ArgumentException($"Unknown Dafny symbol kind: {dafnySymbolKind}");
      }
    }
  }
}