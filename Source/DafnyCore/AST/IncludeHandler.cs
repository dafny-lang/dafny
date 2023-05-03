using System;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public static class IncludeHandler {
  public static bool IsIncludeToken(this IToken token, DafnyOptions options) {
    if (token is RefinementToken) {
      return false;
    }

    if (token == Token.NoToken) {
      return false;
    }

    var files = options.RootUris;
    if (files.Contains(token.Uri)) {
      return false;
    }

    return true;
  }
}