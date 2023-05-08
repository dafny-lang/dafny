using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public static class ShouldCompileOrVerify {

  public static bool ShouldCompile(this ModuleDefinition module, Program program) {
    if (program.NotCompiledFiles == null) {
      program.NotCompiledFiles = NonCompiledUris(program);
    }
    if (module is DefaultModuleDefinition) {
      // TODO Can there be things from precompiled files that live in the default module?
      return true;
    }
    return program.NotCompiledFiles.Contains(module.Tok.Uri);
  }
  
  public static bool ShouldVerify(this INode declaration, Program program) {
    if (program.Options.VerificationScope == VerificationScope.Libraries) {
      return true;
    }

    if (declaration.Tok == Token.NoToken) {
      // TODO required for DefaultModuleDefinition. Do we need it for other things or can be make the code more specific?
      return true;
    }
    if (program.NotVerifiedFiles == null) {
      program.NotVerifiedFiles = NonVerifiedUris(program);
    }
    if (!program.NotVerifiedFiles.Contains(declaration.Tok.Uri)) {
      return false;
    }

    if (program.Options.VerificationScope == VerificationScope.IncludeDirectives) {
      return true;
    }

    return !declaration.Tok.FromIncludeDirective(program);
  }
  
  public static bool FromIncludeDirective(this IToken token, DefaultModuleDefinition outerModule) {
    if (token is RefinementToken) {
      return false;
    }

    if (token == Token.NoToken) {
      return false;
    }

    var files = outerModule.RootSourceUris;
    if (files.Contains(token.Uri)) {
      return false;
    }

    return true;
  }

  public static bool FromIncludeDirective(this IToken token, Program program) {
    return token.FromIncludeDirective(program.DefaultModuleDef);
  }

  private static ISet<Uri> NonCompiledUris(Program program) {
    var compiledRoots = program.Options.CompiledRoots;
    return GetReachableUris(program, compiledRoots);
  }
  
  private static ISet<Uri> NonVerifiedUris(Program program) {
    var verifiedRoots = program.Options.VerifiedRoots;
    return GetReachableUris(program, verifiedRoots);
  }

  private static ISet<Uri> GetReachableUris(Program program, ISet<Uri> verifiedRoots)
  {
    var toVisit = new Stack<Uri>(program.DefaultModuleDef.RootSourceUris);

    var visited = new HashSet<Uri>();
    var edges = program.Includes.GroupBy(i => i.IncluderFilename)
      .ToDictionary(g => g.Key, g => g.Select(i => new Uri(i.IncludedFilename)).ToList());
    while (toVisit.Any())
    {
      var uri = toVisit.Pop();
      if (verifiedRoots.Contains(uri))
      {
        continue;
      }

      if (!visited.Add(uri))
      {
        continue;
      }

      foreach (var included in edges.GetOrDefault(uri, Enumerable.Empty<Uri>))
      {
        toVisit.Push(included);
      }
    }

    return visited;
  }

}