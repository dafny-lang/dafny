﻿using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Handlers.Custom;
using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Plugins;

/// <summary>
/// Helpers for plugins defining a DafnyCodeActionProvider
/// </summary>
public static class DafnyCodeActionHelpers {
  /// <summary>
  /// Given the position of a closing brace '}' and the position of the opening brace '{',
  /// returns spacing that can be used to insert a statement before the closing brace,
  /// as well as spacing for after the statement
  ///
  /// For example, given:
  /// ```
  ///     {
  ///       Some code here:
  ///     }
  /// ```
  /// the method will return ("  ", "    "), so that if someone inserted the first value,
  /// "assert X;\n" and the second value, the resulting code would be
  /// ```
  ///     {
  ///       Some code here:
  ///       assert X;
  ///     }
  /// ```
  /// 
  /// </summary>
  /// <param name="endToken">The position of the closing brace</param>
  /// <param name="text">The document text</param>
  /// <returns>(extra indentation for a statement, current indentation)</returns>
  public static (string, string) GetIndentationBefore(Token endToken, int startLine, int startCol) {
    var indentation = 0;
    var indentationBrace = endToken.col - 1;
    var firstNewline = true;
    var useTabs = false;

    var token = endToken;
    while (token != null) {
      var text = token.LeadingTrivia + token.val + token.TrailingTrivia;
      for (int index = text.Length - 1; index >= 0; index--) {
        var c = text[index];

        if (c == '\n') {
          if (!firstNewline) {
            goto Exit;
          }

          firstNewline = false;
        }

        if (c == '\t') {
          useTabs = true;
        }

        if (!firstNewline) {
          if (c == ' ' || c == '\t') {
            indentation++;
          } else {
            indentation = 0;
          }
        }
      }
      token = token.Prev;
    }
  Exit:

    if (startLine == endToken.line - 1) {
      // Override case {\n} with some spacing, we return a default value of 2 spaces or 1 tab, if we find some
      indentation = indentationBrace + (useTabs ? 1 : 2);
    } else if (startLine == endToken.line) {
      // Override case { ... } on one line.
      indentationBrace = startCol - 1;
      indentation = indentationBrace + 1;
    }

    indentation = Math.Max(indentationBrace, indentation);

    return (
      new string(useTabs ? '\t' : ' ', indentation - indentationBrace),
      new string(useTabs ? '\t' : ' ', indentationBrace));
  }

  public static DafnyCodeActionEdit? InsertAtEndOfBlock(
    IDafnyCodeActionInput input,
    Position openingBracePosition,
    string statementsToInsert) {
    var (beforeEndBrace, indentationExtra, indentationUntilBrace) =
      GetInformationToInsertAtEndOfBlock(input, openingBracePosition);
    if (beforeEndBrace == null) {
      return null;
    }

    return new DafnyCodeActionEdit(beforeEndBrace,
      $"{indentationExtra}{statementsToInsert}\n{indentationUntilBrace}");
  }

  /// <summary>
  /// Given the position of an opening brace of a Block, returns the range for the position just before the closing brace,
  /// and indentation helpers as defined by GetIndentationBefore()
  /// </summary>
  /// <param name="input"></param>
  /// <param name="openingBracePosition"></param>
  /// <returns></returns>
  private static (TokenRange? beforeEndBrace, string indentationExtra, string indentationUntilBrace)
      GetInformationToInsertAtEndOfBlock(IDafnyCodeActionInput input, Position openingBracePosition) {

    var (line, col) = openingBracePosition.ToTokenLineAndCol();
    var endToken = GetMatchingEndToken(input.Program!, input.Uri.ToUri(), line, col);
    if (endToken == null) {
      return (null, "", "");
    }

    var (extraIndentation, indentationUntilBrace) = GetIndentationBefore(endToken, line, col);
    var beforeClosingBrace = new TokenRange(endToken, null);
    return (beforeClosingBrace, extraIndentation, indentationUntilBrace);
  }

  /// <summary>
  /// Given an opening brace of a Block (typically where an error is detected),
  /// finds and returns the closing brace token.
  /// </summary>
  /// <param name="program">The program</param>
  /// <param name="documentUri">The document URI</param>
  /// <param name="line">The line of the opening brace</param>
  /// <param name="col">The column of the opening brace</param>
  /// <returns>The token of a matching closing brace, typically the `ÈndTok` of a BlockStmt</returns>
  private static Token? GetMatchingEndToken(Node program, Uri documentUri, int line, int col) {
    // Look in methods for BlockStmt with the IToken as opening brace
    // Return the EndTok of them.
    Token? tokenFound = null;
    program.Visit((INode n) => {
      if (tokenFound != null) {
        return false;
      }

      if (n.StartToken.line != 0 &&
          (n.StartToken.Uri != documentUri
           || n.StartToken.line > line || line > n.EndToken.line)) {
        return false; // Outside of the current scope
      }

      if (n is MethodOrConstructor method && method.Origin.Uri == documentUri && method.Body != null &&
          method.StartToken.line <= line && line <= method.EndToken.line &&
          GetMatchingEndToken(line, col, method.Body) is { } token) {
        tokenFound = token;
      } else if (n is Function { ByMethodBody: { } } function &&
                 function.StartToken.line <= line && line <= function.EndToken.line &&
                 GetMatchingEndToken(line, col, function.ByMethodBody) is { } token2) {
        tokenFound = token2;
      }
      return tokenFound == null;
    }, node => { });
    return tokenFound;
  }

  /// <summary>
  /// Given an opening brace and a statement, if the statement's token is openingBrace
  /// returns the closing brace token, else null.
  /// Visit substatements recursively
  /// </summary>
  private static Token? GetMatchingEndToken(int line, int col, Statement stmt) {
    // Look in methods for BlockStmt with the IToken as opening brace
    // Return the EndTok of them.
    if (stmt is BlockStmt blockStmt && blockStmt.Origin.line == line && blockStmt.Origin.col == col) {
      return blockStmt.EndToken;
    }

    foreach (var subStmt in stmt.SubStatements) {
      if (GetMatchingEndToken(line, col, subStmt) is { } token) {
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
