using System.Linq;

namespace Microsoft.Dafny; 

public static class IncludeHandler {
  public static bool IsIncludeToken(this IToken token, Program program) {
    if (token == Token.NoToken) {
      return false;
    }
    
    if (program.Options.Files.Contains(token.Filename)) {
      return false;
    }

    return true;
  }
}