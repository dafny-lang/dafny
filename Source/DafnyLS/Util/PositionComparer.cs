using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;

namespace Microsoft.Dafny.LanguageServer.Util {
  /// <summary>
  /// Comparer implementation to define the order of LSP positions.
  /// </summary>
  public class PositionComparer : Comparer<Position> {
    public override int Compare([AllowNull] Position x, [AllowNull] Position y) {
      if(x == null) {
        return y != null ? -1 : 0;
      } else if(y == null) {
        return 1;
      }
      int lineComparison = x.Line.CompareTo(y.Line);
      if(lineComparison != 0) {
        return lineComparison;
      }
      return x.Character.CompareTo(y.Character);
    }
  }
}
