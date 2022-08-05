using System;
using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language {
  /// <summary>
  /// Extension methods for the use with boogie data.
  /// </summary>
  public static class BoogieExtensions {
    /// <summary>
    /// The offset to convert a boogie line-number to an LSP line-number.
    /// </summary>
    private const int LineOffset = -1;

    /// <summary>
    /// The offset to convert a boogie column-number to an LSP column-number.
    /// </summary>
    private const int ColumnOffset = -1;

    /// <summary>
    /// Gets the LSP range of the specified token.
    /// </summary>
    /// <param name="startToken">The token to get the range of.</param>
    /// <param name="endToken">An optional other token to get the end of the range of.</param>
    /// <returns>The LSP range of the token.</returns>
    public static Range GetLspRange(this Boogie.IToken startToken, Boogie.IToken? endToken = null) {
      endToken ??= startToken;
      endToken = endToken is RangeToken rangeToken ? rangeToken.EndToken : endToken;
      return new Range(
        GetLspPosition(startToken),
        ToLspPosition(endToken.line, endToken.col + endToken.val.Length)
      );
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

    public static IToken ToToken(this Position position, string document) {
      try {
        return new Token() {
          line = position.Line - LineOffset,
          col = position.Character - ColumnOffset,
          val = "",
          pos = position.ToAbsolutePosition(document)
        };
      } catch (ArgumentException) {
        return Token.NoToken;
      }
    }

    public static RangeToken ToToken(this Range range, string document) {
      var start = range.Start.ToToken(document);
      var end = range.End.ToToken(document);
      if (end.line == 0) { // Sometimes the end is not a valid token because of over approximation
        end = start;
      }
      return new RangeToken(start, end);
    }
  }
}
