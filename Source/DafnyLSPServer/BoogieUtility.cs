using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LSPServer
{
  static class BoogieUtility
  {

    public static Position BoogieToLspPosition(this IToken token)
    {
      return new Position(token.line - 1, token.col - 1);
    }
  }
}
