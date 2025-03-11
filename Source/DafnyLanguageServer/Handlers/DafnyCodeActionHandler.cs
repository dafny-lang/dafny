using System;
using System.Collections.Concurrent;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Newtonsoft.Json.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol;

namespace Microsoft.Dafny.LanguageServer.Handlers;

public class DafnyCodeActionHandler : CodeActionHandlerBase {
  private readonly DafnyOptions options;
  private readonly ILogger<DafnyCodeActionHandler> logger;
  private readonly IProjectDatabase projects;

  public DafnyCodeActionHandler(DafnyOptions options, ILogger<DafnyCodeActionHandler> logger, IProjectDatabase projects) {
    this.options = options;
    this.logger = logger;
    this.projects = projects;
  }

  public record DafnyCodeActionWithId(DafnyCodeAction DafnyCodeAction, int Id);

  protected override CodeActionRegistrationOptions CreateRegistrationOptions(CodeActionCapability capability,
    ClientCapabilities clientCapabilities) {
    return new CodeActionRegistrationOptions {
      DocumentSelector = DocumentSelector.ForLanguage("dafny"),
      ResolveProvider = true,
      CodeActionKinds = Container<CodeActionKind>.From(
        CodeActionKind.QuickFix
      ),
      WorkDoneProgress = false
    };
  }

  /// <summary>
  /// Returns the fixes along with a unique identifier
  /// </summary>
  private IEnumerable<DafnyCodeActionWithId> GetFixesWithIds(IEnumerable<DafnyCodeActionProvider> fixers, IdeState state, CodeActionParams request) {
    var id = 0;
    var uri = request.TextDocument.Uri.ToUri();
    return fixers.SelectMany(fixer => {
      var fixerInput = new DafnyCodeActionInput(state, uri);
      var quickFixes = fixer.GetDafnyCodeActions(fixerInput, request.Range);
      var fixerCodeActions = quickFixes.Select(quickFix =>
        new DafnyCodeActionWithId(quickFix, id++));
      return fixerCodeActions;
    });
  }

  private readonly ConcurrentDictionary<string, IReadOnlyList<DafnyCodeActionWithId>> documentUriToDafnyCodeActions = new();

  public override async Task<CommandOrCodeActionContainer> Handle(CodeActionParams request, CancellationToken cancellationToken) {
    var projectManager = await projects.GetProjectManager(request.TextDocument);
    if (projectManager == null) {
      logger.LogWarning("dafny code actions requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
      return new CommandOrCodeActionContainer();
    }

    var uri = request.TextDocument.Uri.ToUri();

    var ideState = await projectManager.GetStateAfterResolutionAsync();
    var quickFixers = GetDafnyCodeActionProviders();
    var fixesWithId = GetFixesWithIds(quickFixers, ideState, request).ToArray();
    var key = uri.ToString();
    documentUriToDafnyCodeActions.AddOrUpdate(key, _ => fixesWithId, (_, _) => fixesWithId);
    var codeActions = fixesWithId.Select(fixWithId => {
      CommandOrCodeAction t = new CodeAction {
        Title = fixWithId.DafnyCodeAction.Title,
        Data = new JArray(key, fixWithId.Id),
        Diagnostics = fixWithId.DafnyCodeAction.Diagnostics,
        Kind = CodeActionKind.QuickFix
      };
      return t;
    }
    ).ToArray();
    return new CommandOrCodeActionContainer(codeActions);
  }

  private DafnyCodeActionProvider[] GetDafnyCodeActionProviders() {
    return new List<DafnyCodeActionProvider>() {
      new PostConditionAssertDafnyCodeActionProvider(logger)
    , new ErrorMessageDafnyCodeActionProvider(logger)
    , new ImplicitFailingAssertionCodeActionProvider(logger, options)
    }
    .Concat(
      options.Plugins.SelectMany(plugin =>
        plugin is ConfiguredPlugin { Configuration: PluginConfiguration configuration } ?
            configuration.GetDafnyCodeActionProviders() : [])).ToArray();
  }

  public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
    var command = request.Data;
    if (command == null || command.Count() < 2 || command[1] == null) {
      return Task.FromResult(request);
    }

    string? documentUri = command[0]?.Value<string>();
    if (documentUri == null || !documentUriToDafnyCodeActions.TryGetValue(documentUri, out var quickFixes)) {
      return Task.FromResult(request);
    }

    int? id = command[1]?.Value<int>();
    if (id == null) {
      return Task.FromResult(request);
    }

    DafnyCodeActionWithId? selectedDafnyCodeAction = quickFixes.Where(pluginDafnyCodeAction => pluginDafnyCodeAction.Id == id)
      .FirstOrDefault((DafnyCodeActionWithId?)null);
    if (selectedDafnyCodeAction == null) {
      return Task.FromResult(request);
    }

    return Task.FromResult(new CodeAction {
      Edit = new WorkspaceEdit() {
        DocumentChanges = new Container<WorkspaceEditDocumentChange>(
          new WorkspaceEditDocumentChange(new TextDocumentEdit() {
            TextDocument = new OptionalVersionedTextDocumentIdentifier() {
              Uri = documentUri
            },
            Edits = new TextEditContainer(GetTextEdits(selectedDafnyCodeAction.DafnyCodeAction.GetEdits()))
          }))
      }
    });
  }

  private IEnumerable<TextEdit> GetTextEdits(IEnumerable<DafnyCodeActionEdit> quickFixEdits) {
    var edits = new List<TextEdit>();
    foreach (var (range, toReplace) in quickFixEdits) {
      edits.Add(new TextEdit() {
        NewText = toReplace,
        Range = range.ToLspRange()
      });
    }
    return edits;
  }
}

public class DafnyCodeActionInput : IDafnyCodeActionInput {
  private readonly Uri uri;

  public DafnyCodeActionInput(IdeState state, Uri uri) {
    this.uri = uri;
    IdeState = state;
  }

  public DocumentUri Uri => uri;

  public Node Program => IdeState.Program;
  public IdeState IdeState { get; }

  public IEnumerable<FileDiagnostic> Diagnostics => IdeState.GetAllDiagnostics();
  public VerificationTree? VerificationTree => IdeState.VerificationTrees.GetValueOrDefault(uri);
}
