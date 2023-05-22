using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public static class ShouldCompileOrVerify {

  public static bool ShouldCompile(this ModuleDefinition module, Program program) {
    if (program.UrisToCompile == null) {
      program.UrisToCompile = ComputeUrisToCompile(program);
    }

    if (module.FullName == "_System") {
      return true;
    }

    if (module is DefaultModuleDefinition) {
      // If things from precompiled files live in the default module, that can cause downstream compilation issues:
      // https://github.com/dafny-lang/dafny/issues/4009
      return true;
    }
    return program.UrisToCompile.Contains(module.Tok.Uri);
  }

  public static bool ShouldVerify(this INode declaration, Program program) {
    if (program.Options.VerificationScope == VerificationScope.Everything) {
      return true;
    }

    if (declaration.Tok == Token.NoToken) {
      // Required for DefaultModuleDefinition.
      return true;
    }
    if (program.UrisToVerify == null) {
      program.UrisToVerify = ComputeUrisToVerify(program);
    }
    if (!program.UrisToVerify.Contains(declaration.Tok.Uri)) {
      return false;
    }

    if (program.Options.VerificationScope == VerificationScope.RootSourcesAndIncludes) {
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

  private static ISet<Uri> ComputeUrisToCompile(Program program) {
    var compiledRoots = program.AlreadyCompiledRoots;
    return GetReachableUris(program, compiledRoots);
  }

  private static ISet<Uri> ComputeUrisToVerify(Program program) {
    var verifiedRoots = program.AlreadyVerifiedRoots;
    return GetReachableUris(program, verifiedRoots);
  }

  private static ISet<Uri> GetReachableUris(Program program, ISet<Uri> stopUris) {
    var toVisit = new Stack<Uri>(program.DefaultModuleDef.RootSourceUris);

    var visited = new HashSet<Uri>();
    var edges = program.Includes.GroupBy(i => i.IncluderFilename)
      .ToDictionary(g => g.Key, g => g.Select(i => new Uri(i.IncludedFilename)).ToList());
    while (toVisit.Any()) {
      var uri = toVisit.Pop();
      if (stopUris.Contains(uri)) {
        continue;
      }

      if (!visited.Add(uri)) {
        continue;
      }

      foreach (var included in edges.GetOrDefault(uri, Enumerable.Empty<Uri>)) {
        toVisit.Push(included);
      }
    }

    return visited;
  }

}