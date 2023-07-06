using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Util; 

public static class PositionExtensions {
  public static DafnyPosition ToDafnyPosition(this Position position) {
    return new DafnyPosition(position.Line, position.Character);
  }
}