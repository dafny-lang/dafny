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

      /// <summary>
      /// Given a LSP range and some text, extract the corresponding substring
      /// </summary>
      /// <param name="range">The range to extract</param>
      /// <param name="text">The document</param>
      /// <returns>The substring of the document in the range</returns>
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

      /// <summary>
      /// Given the position of a closing brace '}', returns spacing that can be used to insert a statement before it
      /// </summary>
      /// <param name="token">The position of the closing brace</param>
      /// <param name="text">The document text</param>
      /// <returns>(extra indentation for a statement, current indentation)</returns>
      private (string, string) GetIndentationBefore(IToken token, string text) {
        var pos = token.pos + token.val.Length - 1;
        var indentation = 0;
        var indentationBrace = token.col - 1;
        var firstNewline = true;
        var useTabs = false;
        // Look for the first newline
        while (0 <= pos && pos < text.Length && (text[pos] != '\n' || firstNewline)) {
          if (text[pos] == '\t') {
            useTabs = true;
          }
          if (text[pos] == '\n') {
            if (!firstNewline) {
              break;
            }
            firstNewline = false;
          }

          if (!firstNewline) {
            if (text[pos] == ' ') {
              indentation++;
            } else {
              indentation = 0;
            }
          }

          pos--;
        }

        indentation = Math.Max(indentationBrace, indentation);

        return (
          new string(useTabs ? '\t' : ' ', indentation - indentationBrace),
          new string(useTabs ? '\t' : ' ', indentationBrace));
      }

      /// <summary>
      /// Given an opening brace (typically where an error is detected),
      /// finds and returns the closing brace token.
      /// </summary>
      /// <param name="openingBrace">A token whose pos is the absolute position of the opening brace</param>
      /// <returns>The token of a matching closing brace, typically the `ÈndTok` of a BlockStmt</returns>
      private IToken? GetMatchingEndToken(IToken openingBrace) {
        // Look in methods for BlockStmt with the IToken as opening brace
        // Return the EndTok of them.
        var uri = document.Uri.GetFileSystemPath();
        foreach (var module in document.Program.Modules()) {
          foreach (var topLevelDecl in module.TopLevelDecls) {
            if (topLevelDecl is ClassDecl classDecl) {
              foreach (var member in classDecl.Members) {
                if (member is Method method && method.tok.filename == uri && method.Body != null &&
                  GetMatchingEndToken(openingBrace, method.Body) is { } token) {
                  return token;
                }
                if (member is Function { ByMethodBody: { } } function &&
                    GetMatchingEndToken(openingBrace, function.ByMethodBody) is { } token2) {
                  return token2;
                }
              }
            }
          }
        }

        return null;
      }

      /// <summary>
      /// Given an opening brace and a statement, if the statement's token is openingBrace
      /// returns the closing brace token, else null.
      /// Visit sub-statements recursively
      /// </summary>
      private IToken? GetMatchingEndToken(IToken openingBrace, Statement stmt) {
        // Look in methods for BlockStmt with the IToken as opening brace
        // Return the EndTok of them.
        if (stmt is BlockStmt blockStmt && blockStmt.Tok.pos == openingBrace.pos) {
          return blockStmt.EndTok;
        }

        foreach (var subStmt in stmt.SubStatements) {
          if (GetMatchingEndToken(openingBrace, subStmt) is { } token) {
            return token;
          }
        }

        return null;
      }

      private IEnumerable<(string, TextEdit[])> GetVerificationDiagnosticFixes(string uri) {
        var diagnostics = document.Errors.GetDiagnostics(uri);
        foreach (var diagnostic in diagnostics) {
          if (diagnostic.Range.Contains(request.Range) && diagnostic.Source == MessageSource.Verifier.ToString()) {
            if (diagnostic.RelatedInformation?.FirstOrDefault() is { } relatedInformation) {
              if (relatedInformation.Location.Uri == uri) {
                var relatedRange = relatedInformation.Location.Range;
                var expression = Extract(relatedRange, documentText);
                var endToken = GetMatchingEndToken(diagnostic.Range.Start.ToBoogieToken(documentText));
                if (endToken != null) {
                  var (indentation, indentationBrace) = GetIndentationBefore(endToken, documentText);
                  yield return CodeAction("Insert the failing error", new QuickFixEdit(
                    endToken,
                    $"{indentation}assert {expression};\n{indentationBrace}"
                  ));
                }
              }
            }
          }
        }
      }

      public IEnumerable<(string, TextEdit[])> GetPluginFixes(string uri) {
        foreach (var fixer in fixers) {
          // Maybe we could set the program only once, when resolved, insteda of for every code action?
          fixer.SetProgram(uri, document.Program, documentText, cancellationToken);
          var fixRange = request.Range.ToBoogieToken(documentText);
          var quickFixes = fixer.GetQuickFixes(uri, fixRange);
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
      private (string, TextEdit[])[] GetPossibleEdits() {
        var possibleFixes = new List<(string, TextEdit[])>() { };
        var uri = document.Uri.GetFileSystemPath();
        possibleFixes.AddRange(GetVerificationDiagnosticFixes(uri));
        possibleFixes.AddRange(GetPluginFixes(uri));
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
      return new CodeActionProcessor(this.quickFixers, document, request, cancellationToken).Process();
    }

    public override Task<CodeAction> Handle(CodeAction request, CancellationToken cancellationToken) {
      return Task.FromResult(request);
    }
  }
}
