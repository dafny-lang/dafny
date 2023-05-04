using System;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public static class IncludeHandler {
  public static bool IsIncludeToken(this IToken token, DefaultModuleDefinition outerModule) {
    if (token is RefinementToken) {
      return false;
    }

    if (token == Token.NoToken) {
      return false;
    }

    var files = outerModule.RootUris;
    if (files.Contains(token.Uri)) {
      return false;
    }

    return true;
  }

  public static bool IsIncludeToken(this IToken token, Program program) {
    return token.IsIncludeToken(program.DefaultModuleDef);
  }
}