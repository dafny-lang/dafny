using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny.LanguageServer.Handlers; 

public class DafnyCodeActionHandler : CodeActionHandlerBase {
  private readonly ILogger logger;
  private readonly IDocumentDatabase documents;
  private readonly QuickFixer[] quickFixers;

  public DafnyCodeActionHandler(ILogger<DafnyCompletionHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
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

    public (string, WorkspaceEdit)[] ToWorkspaceEdit(params
      (string, TextEdit[])[] edits) {
      return edits.Select(titleEdit =>
        (titleEdit.Item1, new WorkspaceEdit() {
          DocumentChanges = new Container<WorkspaceEditDocumentChange>(
            new WorkspaceEditDocumentChange(new TextDocumentEdit() {
              TextDocument = new OptionalVersionedTextDocumentIdentifier() {
                Uri = document.Uri,
                Version = document.Version
              },
              Edits = new TextEditContainer(titleEdit.Item2)
            })
          )
        })).ToArray();
    }

    public CommandOrCodeActionContainer GetCommandOrCodeActionContainer() {
      var edits = GetPossibleFixes();
      var workspaceEdit = ToWorkspaceEdit(edits);
      var codeActions = workspaceEdit.Select(titleEdit => {
        CommandOrCodeAction t = new CodeAction() {
          Kind = CodeActionKind.QuickFix,
          Title = titleEdit.Item1,
          Edit = titleEdit.Item2
        };
        return t;
      }
      ).ToArray();
      return new CommandOrCodeActionContainer(codeActions);
    }

    /// <summary>
    /// Returns the fixes as set up by plugins
    /// </summary>
    /// <param name="uri">The URI of the document, used as an unique key</param>
    private IEnumerable<(string, TextEdit[])> GetPluginFixes() {
      foreach (var fixer in fixers) {
        // Maybe we could set the program only once, when resolved, instead of for every code action?
        var fixerInput = new VerificationQuickFixerInput(document);
        fixer.SetQuickFixInput(fixerInput.DocumentUri, fixerInput, CancellationToken.None);
        var fixRange = request.Range.ToBoogieToken(documentText);
        var quickFixes = fixer.GetQuickFixes(documentUri, fixRange);
        var fixerCodeActions = quickFixes.Select(quickFix =>
          CodeAction(quickFix.Title, quickFix.Edits));
        foreach (var codeAction in fixerCodeActions) {
          yield return codeAction;
        }
      }
    }

    /// <summary>
    /// Returns a built-in list of possible code actions
    /// Includes plugin-created code actions
    /// </summary>
    private (string, TextEdit[])[] GetPossibleFixes() {
      var possibleFixes = new List<(string, TextEdit[])>() { };
      possibleFixes.AddRange(GetPluginFixes());
      return possibleFixes.ToArray();
    }
  }

  protected override CodeActionRegistrationOptions CreateRegistrationOptions(CodeActionCapability capability,
    ClientCapabilities clientCapabilities) {
    return new CodeActionRegistrationOptions {
      DocumentSelector = DocumentSelector.ForLanguage("dafny"),
      ResolveProvider = false,
      CodeActionKinds = Container<CodeActionKind>.From(
        CodeActionKind.QuickFix
      ),
      WorkDoneProgress = false
    };
  }

  public override async Task<CommandOrCodeActionContainer> Handle(CodeActionParams request, CancellationToken cancellationToken) {
    var document = await documents.GetDocumentAsync(request.TextDocument);
    if (document == null) {
      logger.LogWarning("quick fixes requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
      return new CommandOrCodeActionContainer();
    }
    return new CodeActionProcessor(this.quickFixers, document, request, cancellationToken).GetCommandOrCodeActionContainer();
  }

  public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
    return Task.FromResult(request);
  }
}

internal class VerificationQuickFixerInput : IQuickFixInput {
  public VerificationQuickFixerInput(
    DafnyDocument document) {
    Document = document;
  }

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