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
using MediatR;
using Microsoft.Boogie;
using Microsoft.Dafny.Plugins;
using Newtonsoft.Json.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Workspace;

namespace Microsoft.Dafny.LanguageServer.Handlers; 

public class DafnyCodeActionHandler : CodeActionHandlerBase {
  private readonly ILogger<DafnyCodeActionHandler> logger;
  private readonly IDocumentDatabase documents;
  private readonly QuickFixer[] quickFixers;
  /*
    class Test : CodeActionPartialHandlerBase {
      public Test(Guid id, [NotNull] IProgressManager progressManager) : base(id, progressManager)
      {
      }

      public Test([NotNull] IProgressManager progressManager) : base(progressManager)
      {
      }

      protected override CodeActionRegistrationOptions CreateRegistrationOptions(CodeActionCapability capability,
        ClientCapabilities clientCapabilities) {
        throw new NotImplementedException();
      }

      protected override void Handle(CodeActionParams request, IObserver<IEnumerable<CommandOrCodeAction>> results, CancellationToken cancellationToken) {
        throw new NotImplementedException();
      }

      public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
        throw new NotImplementedException();
      }
    }*/

  public DafnyCodeActionHandler(ILogger<DafnyCodeActionHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
    this.logger = logger;
    this.documents = documents;
    this.quickFixers =
      new List<QuickFixer>() {
        new VerificationQuickFixer(documents, logger)
      }.Concat(
        DafnyOptions.O.Plugins.SelectMany(plugin => plugin.GetQuickFixers())).ToArray();
  }

  public static (IToken, string, string, bool)
    Edit(IToken position, string leftInsert = "", string rightInsert = "", bool removeToken = false) {
    return (position, leftInsert, rightInsert, removeToken);
  }

  public static (string, TextEdit[]) CodeAction(string title, params QuickFixEdit[] input) {
    var edits = new List<TextEdit>();
    foreach (var (token, toReplace) in input) {
      var range = token.GetLspRange();
      edits.Add(new TextEdit() {
        NewText = toReplace,
        Range = range
      });
    }

    return (title, edits.ToArray());
  }

  private class CodeActionProcessor {
    private readonly QuickFixer[] fixers;
    private readonly DafnyDocument document;
    private readonly CodeActionParams request;
    private readonly CancellationToken cancellationToken;
    private readonly string documentUri;
    private readonly string documentText;

    public CodeActionProcessor(QuickFixer[] fixers, DafnyDocument document, CodeActionParams request,
      CancellationToken cancellationToken) {
      this.fixers = fixers;
      this.document = document;
      this.request = request;
      this.cancellationToken = cancellationToken;
      this.documentText = document.Text.Text;
      this.documentUri = document.Uri.GetFileSystemPath();
    }

    /// <summary>
    /// Returns the fixes as set up by plugins
    /// </summary>
    /// <param name="uri">The URI of the document, used as an unique key</param>
    public IEnumerable<PluginQuickFix> GetPluginFixes() {
      var ID = 0;
      foreach (var fixer in fixers) {
        // Maybe we could set the program only once, when resolved, instead of for every code action?
        var fixerInput = new VerificationQuickFixerInput(document);
        var fixRange = request.Range.ToBoogieToken(documentText);
        var quickFixes = fixer.GetQuickFixes(fixerInput, fixRange);
        var fixerCodeActions = quickFixes.Select(quickFix =>
          new PluginQuickFix(quickFix, ID++));
        foreach (var codeAction in fixerCodeActions) {
          yield return codeAction;
        }
      }
    }
  }


  public record PluginQuickFix(QuickFix QuickFix, int Id);

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

  public ConcurrentDictionary<string, IReadOnlyList<PluginQuickFix>> ConcurrentDictionary = new();

  public override async Task<CommandOrCodeActionContainer> Handle(CodeActionParams request, CancellationToken cancellationToken) {
    var document = await documents.GetDocumentAsync(request.TextDocument);
    if (document == null) {
      logger.LogWarning("quick fixes requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
      return new CommandOrCodeActionContainer();
    }
    var pluginQuickFixes = new CodeActionProcessor(this.quickFixers, document, request, cancellationToken).GetPluginFixes().ToArray();

    var documentUri = document.Uri.ToString();
    ConcurrentDictionary.AddOrUpdate(documentUri,
      _ => pluginQuickFixes, (_, _) => pluginQuickFixes);
    var codeActions = pluginQuickFixes.Select(pluginQuickFix => {
      CommandOrCodeAction t = new CodeAction {
        Title = pluginQuickFix.QuickFix.Title,
        Data = new JArray(documentUri, pluginQuickFix.Id)
      };
      return t;
    }
    ).ToArray();
    return new CommandOrCodeActionContainer(codeActions);
  }

  public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
    var command = request.Data;
    string documentUri = command[0].Value<string>();
    int id = command[1].Value<int>();
    if (ConcurrentDictionary.TryGetValue(documentUri, out var quickFixes)) {
      var selectedQuickFix = quickFixes.Where(pluginQuickFix => pluginQuickFix.Id == id).FirstOrDefault((PluginQuickFix)null!);
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

    return Task.FromResult(request);
  }

  private IEnumerable<TextEdit> GetTextEdits(QuickFixEdit[] quickFixEdits) {
    var edits = new List<TextEdit>();
    foreach (var (token, toReplace) in quickFixEdits) {
      var range = token.GetLspRange();
      edits.Add(new TextEdit() {
        NewText = toReplace,
        Range = range
      });
    }
    return edits.ToArray();
  }
}

internal class VerificationQuickFixerInput : IQuickFixInput {
  public VerificationQuickFixerInput(
    DafnyDocument document) {
    Document = document;
  }

  public string Uri => Document.Uri.GetFileSystemPath();
  public int Version => Document.Version;
  public string Code => Document.Text.Text;
  public Dafny.Program Program => Document.Program;
  public DafnyDocument Document { get; }

  public Diagnostic[] Diagnostics {
    get {
      var result = Document.Errors.GetDiagnostics(Document.Uri).ToArray();
      if (result.Length == 0) {
        // For anonymous documents opened in VSCode
        result = Document.Errors.GetDiagnostics(DocumentUri).ToArray();
      }

      return result;
    }
  }

  public string DocumentUri => Document.Uri.GetFileSystemPath();
}