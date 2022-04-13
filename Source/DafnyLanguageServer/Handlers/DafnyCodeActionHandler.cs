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
using Microsoft.Dafny.Plugins;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Handlers {
  public class DafnyCodeActionHandler : CodeActionHandlerBase {
    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;
    private readonly QuickFixer[] quickFixers;

    public DafnyCodeActionHandler(ILogger<DafnyCompletionHandler> logger, IDocumentDatabase documents, ISymbolGuesser symbolGuesser) {
      this.logger = logger;
      this.documents = documents;
      this.quickFixers = DafnyOptions.O.Plugins.SelectMany(plugin => plugin.GetQuickFixers()).ToArray();
    }

    public static (IToken, string, string, bool)
      Edit(IToken position, string leftInsert = "", string rightInsert = "", bool removeToken = false) {
      return (position, leftInsert, rightInsert, removeToken);
    }

    public static (string, TextEdit[]) CodeAction(string title, params QuickFixEdit[] input) {
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
              NewText = rightInsert,
              Range = (endPos, endPos)
            });
          }
        }
      }

      return (title, edits.ToArray());
    }

    private class CodeActionProcessor {
      private readonly QuickFixer[] fixers;
      private readonly DafnyDocument document;
      private readonly CodeActionParams request;
      private readonly CancellationToken cancellationToken;
      private string documentText;

      public CodeActionProcessor(QuickFixer[] fixers, DafnyDocument document, CodeActionParams request,
        CancellationToken cancellationToken) {
        this.fixers = fixers;
        this.document = document;
        this.request = request;
        this.cancellationToken = cancellationToken;
        this.documentText = document.Text.Text;
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

      public CommandOrCodeActionContainer Process() {
        var edits = GetPossibleEdits();
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

      private string Extract(Range range, string text) {
        var token = range.ToBoogieToken(text);
        var startTokenPos = token.StartToken.pos;
        var endTokenPos = token.EndToken.pos + token.EndToken.val.Length;
        var length = endTokenPos - startTokenPos;
        if (startTokenPos < 0 || endTokenPos < startTokenPos || endTokenPos >= text.Length) {
          return ""; // Safeguard
        }

        return text.Substring(startTokenPos, length);
      }

      private string GetIndentationAfter(Range rangeToken, string text) {
        var token = rangeToken.ToBoogieToken(text);
        var pos = token.pos + token.val.Length;
        var c = text[pos];
        var indentation = "";
        while (pos < text.Length && (text[pos] == ' ' || text[pos] == '\n' || text[pos] == '\r')) {
          if (text[pos] == ' ') {
            indentation += " ";
          } else {
            indentation = "";
          }
          pos++;
        }

        if (pos < text.Length && text[pos] == '}') {
          indentation += "  ";
        }

        return indentation;
      }

      private (string, TextEdit[])[] GetPossibleEdits() {
        var possibleEdits = new List<(string, TextEdit[])>() { };

        var uri = document.Uri.GetFileSystemPath();
        var diagnostics = document.Errors.GetDiagnostics(uri);
        foreach (var diagnostic in diagnostics) {
          if (diagnostic.Range.Contains(request.Range) && diagnostic.Source == MessageSource.Verifier.ToString()) {
            if (diagnostic.RelatedInformation?.FirstOrDefault() is { } relatedInformation) {
              if (relatedInformation.Location.Uri == uri) {
                var relatedRange = relatedInformation.Location.Range;
                var expression = Extract(relatedRange, documentText);
                var indentation = GetIndentationAfter(diagnostic.Range, documentText);
                possibleEdits.Add(CodeAction("Insert the failing error", new QuickFixEdit(
                    diagnostic.Range.ToBoogieToken(documentText),
                    insertAfter: $"\n{indentation}assert {expression};"
                  )));
              }
            }
          }
        }

        foreach (var fixer in fixers) {
          var uniqueKey = document.Uri.ToString();
          // Maybe we could set the program only once, when resolved, insteda of for every code action?
          fixer.SetProgram(uniqueKey, document.Program, documentText, cancellationToken);
          var fixRange = request.Range.ToBoogieToken(documentText);
          var quickFixes = fixer.GetQuickFixes(uniqueKey, fixRange);
          var fixerCodeActions = quickFixes.Select(quickFix =>
            CodeAction(quickFix.Title, quickFix.Edits));
          possibleEdits.AddRange(fixerCodeActions);
        }

        return possibleEdits.ToArray();
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
      return new CodeActionProcessor(this.quickFixers, document, request, cancellationToken).Process();
    }

    public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
      return Task.FromResult(request);
    }
  }
}
