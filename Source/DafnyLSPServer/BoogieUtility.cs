using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LSPServer
{
  static class BoogieUtility
  {

    public static Position BoogieToLspPosition(this IToken token)
    {
      // TODO understand why there is an extra -1,-1
      return new Position(token.line - 1, token.col - 2);
    }
  }
}
