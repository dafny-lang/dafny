using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.Plugins;
using Microsoft.Extensions.Logging;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language;

class VerificationQuickFixer : QuickFixer {
  private readonly IDocumentDatabase documents;
  private readonly ILogger<DafnyCodeActionHandler> logger;

  public VerificationQuickFixer(IDocumentDatabase documents, ILogger<DafnyCodeActionHandler> logger) {
    this.documents = documents;
    this.logger = logger;
  }

  public override QuickFix[] GetQuickFixes(IQuickFixInput input, IToken selection) {
    var cachedData = (VerificationQuickFixerInput)input;
    string uri = cachedData.DocumentUri;
    var document = cachedData.Document;
    var diagnostics = cachedData.Diagnostics;
    var range = selection.GetLspRange();
    var result = new List<QuickFix>() { };
    foreach (var diagnostic in diagnostics) {
      if (diagnostic.Range.Contains(range) && diagnostic.Source == MessageSource.Verifier.ToString()) {
        if (diagnostic.RelatedInformation?.FirstOrDefault() is { } relatedInformation) {
          if (relatedInformation.Location.Uri == uri) {
            var relatedRange = relatedInformation.Location.Range;
            var expression = Extract(relatedRange, cachedData.Code);
            var endToken = GetMatchingEndToken(document, uri, diagnostic.Range.Start.ToBoogieToken(cachedData.Code));
            if (endToken != null) {
              var (indentation, indentationBrace) = GetIndentationBefore(endToken, cachedData.Code);
              result.Add(new InstantQuickFix(
                "Explicit the failing assert",
                new[] {
                  new QuickFixEdit(
                    endToken.Start(), $"{indentation}assert {expression};\n{indentationBrace}")
                }
              ));
            }
          }
        }
      }
    }

    return result.ToArray();
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
        if (text[pos] == ' ' || text[pos] == '\t') {
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
  private IToken? GetMatchingEndToken(DafnyDocument document, string documentUri, IToken openingBrace) {
    // Look in methods for BlockStmt with the IToken as opening brace
    // Return the EndTok of them.
    foreach (var module in document.Program.Modules()) {
      foreach (var topLevelDecl in module.TopLevelDecls) {
        if (topLevelDecl is ClassDecl classDecl) {
          foreach (var member in classDecl.Members) {
            if (member is Method method && method.tok.filename == documentUri && method.Body != null &&
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
}