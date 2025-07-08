using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public static class PositionExtensions {
  public static DafnyPosition ToDafnyPosition(this IOrigin token) {
    return new DafnyPosition(token.line + BoogieExtensions.LineOffset, token.col + BoogieExtensions.ColumnOffset);
  }
  public static DafnyPosition ToDafnyPosition(this Position position) {
    return new DafnyPosition(position.Line, position.Character);
  }
}