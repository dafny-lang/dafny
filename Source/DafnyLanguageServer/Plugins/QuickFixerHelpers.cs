using System;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Plugins;

/// <summary>
/// Helpers for plugins defining a QuickFixer
/// </summary>
public static class QuickFixerHelpers {
  /// <summary>
  /// Given a LSP range and some text, extract the corresponding substring
  /// </summary>
  /// <param name="range">The range to extract</param>
  /// <param name="text">The document</param>
  /// <returns>The substring of the document in the range</returns>
  public static string Extract(Range range, string text) {
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
  /// Given the position of a closing brace '}' and the position of the opening brace '{',
  /// returns spacing that can be used to insert a statement before it,
  /// as well as spacing for after the statement
  /// </summary>
  /// <param name="endToken">The position of the closing brace</param>
  /// <param name="text">The document text</param>
  /// <returns>(extra indentation for a statement, current indentation)</returns>
  public static (string, string) GetIndentationBefore(IToken endToken, IToken startToken, string text) {
    var pos = endToken.pos + endToken.val.Length - 1;
    var indentation = 0;
    var indentationBrace = endToken.col - 1;
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

    if (startToken.line == endToken.line - 1) {
      // Override case {\n} with some spacing, we return a default value of 2 spaces or 1 tab, if we find some
      indentation = indentationBrace + (useTabs ? 1 : 2);
    } else if (startToken.line == endToken.line) {
      // Override case { ... } on one line.
      indentationBrace = startToken.col - 1;
      indentation = indentationBrace + 1;
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
  /// <param name="program">The program</param>
  /// <param name="documentUri">The document URI</param>
  /// <param name="openingBrace">A token whose pos is the absolute position of the opening brace</param>
  /// <returns>The token of a matching closing brace, typically the `ÈndTok` of a BlockStmt</returns>
  public static IToken? GetMatchingEndToken(Dafny.Program program, string documentUri, IToken openingBrace) {
    // Look in methods for BlockStmt with the IToken as opening brace
    // Return the EndTok of them.
    foreach (var module in program.Modules()) {
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
  public static IToken? GetMatchingEndToken(IToken openingBrace, Statement stmt) {
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

  /// <summary>
  /// Given a range (start, end), return the range (start, start)
  /// </summary>
  public static Range GetStartRange(this Range range) {
    var start = range.Start;
    return new Range(start, start);
  }

  /// <summary>
  /// Given a range (start, end), return the range (end, end)
  /// </summary>
  public static Range GetEndRange(this Range range) {
    var end = range.End;
    return new Range(end, end);
  }
}