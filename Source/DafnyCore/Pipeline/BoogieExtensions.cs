﻿using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny {
  /// <summary>
  /// Extension methods for the use with boogie data.
  /// </summary>
  public static class BoogieExtensions {
    /// <summary>
    /// The offset to convert a boogie line-number to an LSP line-number.
    /// </summary>
    public const int LineOffset = -1;

    /// <summary>
    /// The offset to convert a boogie column-number to an LSP column-number.
    /// </summary>
    public const int ColumnOffset = -1;

    public static Range ToLspRange(this DafnyRange range) {
      return new Range(
        range.Start.GetLspPosition(),
        range.ExclusiveEnd.GetLspPosition());
    }

    public static Range ToLspRange(this TokenRange tokenRange) {
      return tokenRange.ToDafnyRange().ToLspRange();
    }

    /// <summary>
    /// Gets the LSP range of the specified token.
    /// </summary>
    /// <param name="startToken">The token to get the range of.</param>
    /// <param name="endToken">An optional other token to get the end of the range of.</param>
    /// <returns>The LSP range of the token.</returns>
    public static Range ToLspRange(this INode node) {
      return node.ToDafnyRange().ToLspRange();
    }

    /// <summary>
    /// Gets the LSP range of the specified token.
    /// </summary>
    /// <param name="startToken">The token to get the range of.</param>
    /// <param name="endToken">An optional other token to get the end of the range of.</param>
    /// <returns>The LSP range of the token.</returns>
    public static Range GetLspRange(this IOrigin startToken, IOrigin endToken) {
      return GetLspRangeGeneric(startToken, endToken);
    }

    private static Range GetLspRangeGeneric(this Boogie.IToken startToken, Boogie.IToken endToken) {
      return new Range(
        GetLspPosition(startToken),
        ToLspPosition(endToken.line, endToken.col + endToken.val.Length)
      );
    }

    /// <summary>
    /// Gets the LSP range of the specified token.
    /// </summary>
    /// <param name="token">The token to get the range of.</param>
    /// <param name="endToken">An optional other token to get the end of the range of.</param>
    /// <returns>The LSP range of the token.</returns>
    public static Range GetLspRange(this Boogie.IToken token, bool nameRange = false) {
      if (token is NestedOrigin nestedToken) {
        return GetLspRange(nestedToken.Outer, nameRange);
      }

      var dafnyToken = BoogieGenerator.ToDafnyToken(token);
      var tokenRange = nameRange ? dafnyToken.ReportingRange : dafnyToken.EntireRange ?? dafnyToken.ReportingRange;
      var lspRangeGeneric = GetLspRangeGeneric(tokenRange.StartToken, tokenRange.EndToken);
      return lspRangeGeneric;
    }

    public static Position GetLspPosition(this DafnyPosition position) {
      return new Position(position.Line, position.Column);
    }

    public static FilePosition GetFilePosition(this IOrigin token, bool end = false) {
      return new FilePosition(token.Uri, GetLspPosition(token, end));
    }

    /// <summary>
    /// Gets the LSP position of the specified token (i.e., the position of the first character of the token).
    /// </summary>
    /// <param name="token">The token to get the position of.</param>
    /// <param name="end">Whether to take the ending position of the token instead.</param>
    /// <returns>The LSP position of the token.</returns>
    public static Position GetLspPosition(this Boogie.IToken token, bool end = false) {
      return ToLspPosition(token.line, token.col + (end ? token.val.Length : 0));
    }

    /// <summary>
    /// Converts a given line and column of a boogie document to its LSP counterpart.
    /// </summary>
    /// <param name="boogieLine">The line in the boogie format.</param>
    /// <param name="boogieColumn">The column in the boogie format.</param>
    /// <returns>The given boogie line and column as a LSP position.</returns>
    public static Position ToLspPosition(int boogieLine, int boogieColumn) {
      return new Position(boogieLine + LineOffset, boogieColumn + ColumnOffset);
    }

    public static (int line, int col) ToTokenLineAndCol(this Position position) {
      return (line: position.Line - LineOffset, col: position.Character - ColumnOffset);
    }
  }
}
