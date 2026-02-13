using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny;

public static class ShouldCompileOrVerify {

  public static bool ShouldCompile(this ModuleDefinition module, CompilationData program) {
    if (program.UrisToCompile == null) {
      program.UrisToCompile = ComputeUrisToCompile(program);
    }

    if (module.FullName == "_System") {
      return program.Options.SystemModuleTranslationMode != CommonOptionBag.SystemModuleMode.Omit;
    }
    if (program.Options.SystemModuleTranslationMode == CommonOptionBag.SystemModuleMode.OmitAllOtherModules) {
      return false;
    }

    if (module is DefaultModuleDefinition) {
      // If things from precompiled files live in the default module, that can cause downstream compilation issues:
      // https://github.com/dafny-lang/dafny/issues/4009
      return true;
    }

    if (program.Options.Backend?.TargetId != "lib") {
      if (!ProgramResolver.ShouldCompile(module)) {
        return false;
      }
    }

    return program.UrisToCompile.Contains(module.Origin.Uri);
  }

  public static bool ShouldVerify(this INode declaration, CompilationData compilation) {
    if (ReferenceEquals(declaration.Origin, Token.NoToken)) {
      // Required for DefaultModuleDefinition.
      return true;
    }
    if (compilation.UrisToVerify == null) {
      compilation.UrisToVerify = ComputeUrisToVerify(compilation);
    }
    if (!compilation.UrisToVerify.Contains(declaration.Origin.Uri)) {
      return false;
    }

    if (compilation.Options.VerifyAllModules) {
      return true;
    }

    return !declaration.Origin.FromIncludeDirective(compilation);
  }

  public static bool FromIncludeDirective(this IOrigin token, CompilationData outerModule) {
    if (token is RefinementOrigin) {
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

  public static bool FromIncludeDirective(this IOrigin token, Program program) {
    return token.FromIncludeDirective(program.Compilation);
  }

  private static ISet<Uri> ComputeUrisToCompile(CompilationData program) {
    var compiledRoots = program.AlreadyCompiledRoots;
    return GetReachableUris(program, compiledRoots);
  }

  private static ISet<Uri> ComputeUrisToVerify(CompilationData program) {
    var verifiedRoots = program.AlreadyVerifiedRoots;
    return GetReachableUris(program, verifiedRoots);
  }

  private static ISet<Uri> GetReachableUris(CompilationData compilation, ISet<Uri> stopUris) {
    var edges = compilation.Includes.GroupBy(i => i.IncluderFilename)
      .ToDictionary(g => g.Key, g => g.Select(x => x.IncludedFilename).ToList());

    ISet<Uri> Visit(Stack<Uri> roots, ISet<Uri> excluded) {
      var toVisit = roots;

      var visited = new HashSet<Uri>();

      while (toVisit.Any()) {
        var uri = toVisit.Pop();
        if (excluded.Contains(uri)) {
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

    var excluded = Visit(new Stack<Uri>(stopUris), new HashSet<Uri>());

    return Visit(new Stack<Uri>(compilation.RootSourceUris), excluded);
  }

}