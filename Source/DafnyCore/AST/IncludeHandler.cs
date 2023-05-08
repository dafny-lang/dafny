using System;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public static class IncludeHandler {

  public static bool ShouldCompile(this ModuleDefinition module, Program program) {
    // dafnyFile.IsPrecompiled, set to true for library files and for .dll with source attribute
    
    // Is it reachable from a library file, then return false
    
    // Originates from a .dll, return false
    
    // Return true
  }
  
  public static bool ShouldVerify(this ModuleDefinition module, Program program) {
    // There should be verifyAllIncludes and verifyEverythingIncludingLibrariesAndDooFiles
    if (program.Options.VerificationScope == VerificationScope.Libraries) {
      return true;
    }
    
    // Is it reachable from a library file, then return false
    
    // Originates from a .doo, return false

    if (program.Options.VerificationScope == VerificationScope.IncludeDirectives) {
      return true;
    }

    return !module.Tok.IsIncludeToken(program);
  }
  
  public static bool IsIncludeToken(this IToken token, Program program) {
    if (token is RefinementToken) {
      return false;
    }

    if (token == Token.NoToken) {
      return false;
    }

    var files = program.Options.RootUris;
    if (files.Contains(token.Uri)) {
      return false;
    }

    return true;
  }
}