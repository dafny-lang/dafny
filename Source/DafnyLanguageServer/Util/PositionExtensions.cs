using Microsoft.Dafny.LanguageServer.Language;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Util; 

public static class PositionExtensions {
  public static DafnyPosition ToDafnyPosition(this IToken token) {
    return new DafnyPosition(token.line + BoogieExtensions.LineOffset, token.col + BoogieExtensions.ColumnOffset);
  }
  public static DafnyPosition ToDafnyPosition(this Position position) {
    return new DafnyPosition(position.Line, position.Character);
  }
}