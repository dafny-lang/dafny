using System;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public static class IncludeHandler {
  public static bool IsIncludeToken(this IToken token, Program program) {
    if (token is RefinementToken) {
      return false;
    }

    if (token == Token.NoToken) {
      return false;
    }

    var files = program.Options.Files.Select(Path.GetFullPath);
    if (files.Contains(token.ActualFilename)) { // TODO, use Uris?
      return false;
    }

    if (token.Uri.Scheme == "stdin" || token.Uri.Scheme == "transcript") {
      return false;
    }

    return true;
  }
}