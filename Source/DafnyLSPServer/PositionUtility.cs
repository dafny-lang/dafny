using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LSPServer
{
  static class PositionUtility
  {
    public static Range ToSingleLengthRange(this Position position)
    {
      return new Range(position, new Position(position.Line, position.Character));
    }

  }
}
