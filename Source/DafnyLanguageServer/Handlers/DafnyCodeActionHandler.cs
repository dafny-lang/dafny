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
using Newtonsoft.Json.Linq;

namespace Microsoft.Dafny.LanguageServer.Handlers; 

public class DafnyCodeActionHandler : CodeActionHandlerBase {
  private readonly ILogger<DafnyCodeActionHandler> logger;
  private readonly IDocumentDatabase documents;

  public DafnyCodeActionHandler(ILogger<DafnyCodeActionHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
    this.logger = logger;
    this.documents = documents;
  }

  public record QuickFixWithId(QuickFix QuickFix, int Id);

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
  public IEnumerable<QuickFixWithId> GetFixesWithIds(QuickFixer[] fixers, DafnyDocument document, CodeActionParams request) {
    var ID = 0;
    foreach (var fixer in fixers) {
      // Maybe we could set the program only once, when resolved, instead of for every code action?
      var fixerInput = new VerificationQuickFixerInput(document);
      var quickFixes = fixer.GetQuickFixes(fixerInput, request.Range);
      var fixerCodeActions = quickFixes.Select(quickFix =>
        new QuickFixWithId(quickFix, ID++));
      foreach (var codeAction in fixerCodeActions) {
        yield return codeAction;
      }
    }
  }

  private readonly ConcurrentDictionary<string, IReadOnlyList<QuickFixWithId>> documentUriToQuickFixes = new();

  public override async Task<CommandOrCodeActionContainer> Handle(CodeActionParams request, CancellationToken cancellationToken) {
    var document = await documents.GetDocumentAsync(request.TextDocument);
    if (document == null) {
      logger.LogWarning("quick fixes requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
      return new CommandOrCodeActionContainer();
    }
    var quickFixers = GetQuickFixers();
    var fixesWithId = GetFixesWithIds(quickFixers, document, request).ToArray();

    var documentUri = document.Uri.ToString();
    documentUriToQuickFixes.AddOrUpdate(documentUri,
      _ => fixesWithId, (_, _) => fixesWithId);
    var codeActions = fixesWithId.Select(fixWithId => {
      CommandOrCodeAction t = new CodeAction {
        Title = fixWithId.QuickFix.Title,
        Data = new JArray(documentUri, fixWithId.Id)
      };
      return t;
    }
    ).ToArray();
    return new CommandOrCodeActionContainer(codeActions);
  }

  private QuickFixer[] GetQuickFixers() {
    return new List<QuickFixer>() {
      new VerificationQuickFixer(documents, logger)
    }.Concat(
      DafnyOptions.O.Plugins.SelectMany(plugin =>
        plugin is ConfiguredPlugin configuredPlugin &&
          configuredPlugin.Configuration is PluginConfiguration configuration ?
            configuration.GetQuickFixers() : new QuickFixer[] { })).ToArray();
  }

  public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
    var command = request.Data;
    if (command != null) {
      string documentUri = command[0].Value<string>();
      int id = command[1].Value<int>();
      if (documentUriToQuickFixes.TryGetValue(documentUri, out var quickFixes)) {
        QuickFixWithId? selectedQuickFix = quickFixes.Where(pluginQuickFix => pluginQuickFix.Id == id).FirstOrDefault((QuickFixWithId?)null!);
        if (selectedQuickFix != null) {
          return Task.FromResult(new CodeAction() {
            Edit = new WorkspaceEdit() {
              DocumentChanges = new Container<WorkspaceEditDocumentChange>(
                new WorkspaceEditDocumentChange(new TextDocumentEdit() {
                  TextDocument = new OptionalVersionedTextDocumentIdentifier() {
                    Uri = documentUri
                  },
                  Edits = new TextEditContainer(GetTextEdits(selectedQuickFix.QuickFix.GetEdits()))
                }))
            }
          });
        }
      }
    }

    return Task.FromResult(request);
  }

  private IEnumerable<TextEdit> GetTextEdits(QuickFixEdit[] quickFixEdits) {
    var edits = new List<TextEdit>();
    foreach (var (range, toReplace) in quickFixEdits) {
      edits.Add(new TextEdit() {
        NewText = toReplace,
        Range = range
      });
    }
    return edits.ToArray();
  }
}

public class VerificationQuickFixerInput : IQuickFixInput {
  public VerificationQuickFixerInput(
    DafnyDocument document) {
    Document = document;
  }

  public string Uri => Document.Uri.GetFileSystemPath();
  public int Version => Document.Version;
  public string Code => Document.TextDocumentItem.Text;
  public Dafny.Program? Program => Document.Program;
  public DafnyDocument Document { get; }

  public Diagnostic[] Diagnostics {
    get {
      var result = Document.Diagnostics.ToArray();
      if (result.Length == 0) {
        // For anonymous documents opened in VSCode
        result = Document.Diagnostics.ToArray();
      }

      return result;
    }
  }

  public string DocumentUri => Document.Uri.GetFileSystemPath();
}