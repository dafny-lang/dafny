using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyCodeActionHandler : CodeActionHandlerBase {
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;

    public DafnyCodeActionHandler(ILogger<DafnyCompletionHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
      this.logger = logger;
      this.documents = documents;
    }

    public static (IToken, string, string, bool)
      Edit(IToken position, string leftInsert = "", string rightInsert = "", bool removeToken = false) {
      return (position, leftInsert, rightInsert, removeToken);
    }

    public static List<TextEdit> ToTextEdits(params (IToken token, string leftInsert, string rightInsert, bool remove)[] input) {
      var edits = new List<TextEdit>();
      foreach (var (token, leftInsert, rightInsert, removeToken) in input) {
        if (removeToken) {
          var range = token.GetLspRange();
          edits.Add(new TextEdit() {
            NewText = leftInsert + rightInsert,
            Range = range
          });
        } else {
          if (leftInsert != "") {
            var startPos = token.GetLspPosition();
            edits.Add(new TextEdit() {
              NewText = leftInsert,
              Range = (startPos, startPos)
            });
          }

          if (rightInsert != "") {
            var endPos = BoogieExtensions.ToLspPosition(token.line, token.col + token.val.Length);
            edits.Add(new TextEdit() {
              NewText = leftInsert,
              Range = (endPos, endPos)
            });
          }
        }
      }

      return edits;
    }

    private class CodeActionProcessor {
      private readonly DafnyDocument document;
      private readonly CodeActionParams request;
      private readonly CancellationToken cancellationToken;

      public CodeActionProcessor(DafnyDocument document, CodeActionParams request, CancellationToken cancellationToken) {
        this.document = document;
        this.request = request;
        this.cancellationToken = cancellationToken;
      }

      public WorkspaceEdit ToWorkspaceEdit(params
        TextEdit[] edits) {
        return new WorkspaceEdit() {
          DocumentChanges = new Container<WorkspaceEditDocumentChange>(
            new WorkspaceEditDocumentChange(new TextDocumentEdit() {
              TextDocument = new OptionalVersionedTextDocumentIdentifier() {
                Uri = document.Uri,
                Version = document.Version
              },
              Edits = new TextEditContainer(edits)
            })
          )
        };
      }

      public CommandOrCodeActionContainer Process() {
        var edits = GetPossibleEdits();
        var workspaceEdit = ToWorkspaceEdit(edits);
        return new CommandOrCodeActionContainer(
          new CodeAction() {
            Kind = CodeActionKind.QuickFix,
            Title = "Mark the first token with a comment",
            Edit = workspaceEdit
          });
      }

      private TextEdit[] GetPossibleEdits() {
        var firstToken = document.Program.GetFirstTopLevelToken();
        var position = firstToken.GetLspPosition();
        if (position.Line == request.Range.Start.Line) {
          return ToTextEdits(Edit(
            firstToken,
            "/* This is the first token */"
          )).ToArray();
        }

        return new TextEdit[] { };
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
        logger.LogWarning("location requested for unloaded document {DocumentUri}", request.TextDocument.Uri);
        return new CommandOrCodeActionContainer();
      }
      return new CodeActionProcessor(document, request, cancellationToken).Process();
    }

    public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
      return Task.FromResult(request);
    }
  }
}
