using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ModuleQualifiedId : Node, IHasUsages {
  public readonly List<Name> Path; // Path != null && Path.Count > 0

  // The following are filled in during resolution
  // Note that the root (first path segment) is resolved initially,
  // as it is needed to determine dependency relationships.
  // Then later the rest of the path is resolved, at which point all of the
  // ids in the path have been fully resolved
  // Note also that the resolution of the root depends on the syntactice location
  // of the qualified id; the resolution of subsequent ids depends on the
  // default export set of the previous id.
  [FilledInDuringResolution] public ModuleDecl Root; // the module corresponding to Path[0].val
  [FilledInDuringResolution] public ModuleDecl Decl; // the module corresponding to the full path
  [FilledInDuringResolution] public ModuleDefinition Def; // the module definition corresponding to the full path
  [FilledInDuringResolution] public ModuleSignature Sig; // the module signature corresponding to the full path

  public ModuleQualifiedId(List<Name> path) {
    Contract.Assert(path != null && path.Count > 0);
    Path = path; // note that the list is aliased -- not to be modified after construction
  }

  public ModuleQualifiedId(Cloner cloner, ModuleQualifiedId original) {
    Path = original.Path.Select(n => n.Clone(cloner)).ToList();

    // TODO decide what to do with this. It's commented out because the conditioned used to be a custom bool parameter that was always false.
    // if (cloner.CloneResolvedFields) {
    //   Root = original.Root;
    //   Decl = original.Decl;
    //   Def = original.Def;
    //   Sig = original.Sig;
    // }
  }

  public string RootName() {
    return Path[0].Value;
  }

  public IToken RootToken() {
    return Path[0].StartToken;
  }

  public override string ToString() {
    string s = Path[0].Value;
    for (int i = 1; i < Path.Count; ++i) {
      s = s + "." + Path[i].Value;
    }

    return s;
  }

  public void SetRoot(ModuleDecl m) {
    Root = m;
  }

  public void SetTarget(ModuleDecl m) {
    if (m == null) {
      Decl = null;
      Def = null;
      Sig = null;
    } else {
      Decl = m;
      Def = m.Signature.ModuleDef;
      Sig = m.Signature;
    }
  }

  public override IToken Tok => Path.Last().Tok;
  public override IEnumerable<Node> Children => Enumerable.Empty<Node>();
  public override IEnumerable<Node> PreResolveChildren => Children;

  public override RangeToken RangeToken {
    get => new(Path.First().StartToken, Path.Last().EndToken);
    set => throw new NotSupportedException();
  }

  public IToken NameToken => Path.Last().StartToken;

  public IEnumerable<IDeclarationOrUsage> GetResolvedDeclarations() {
    return Enumerable.Repeat(Decl, 1);
  }

  /// <summary>
  /// Returns the resolved Module declaration corresponding to the qualified module id
  /// Requires the root to have been resolved
  /// Issues an error and returns null if the path is not valid
  /// </summary>
  public ModuleDecl ResolveTarget(ModuleDecl root, ErrorReporter reporter) {
    Contract.Requires(this != null);
    Contract.Requires(Path.Count > 0);

    ModuleDecl decl = root;
    ModuleSignature p;
    for (int k = 1; k < Path.Count; k++) {
      if (decl is LiteralModuleDecl) {
        p = ((LiteralModuleDecl)decl).DefaultExport;
        if (p == null) {
          reporter.Error(MessageSource.Resolver, Path[k],
            Resolver.ModuleNotFoundErrorMessage(k, Path, $" because {decl.Name} does not have a default export"));
          return null;
        }
      } else {
        p = decl.Signature;
      }

      var tld = p.TopLevels.GetValueOrDefault(Path[k].Value, null);
      if (!(tld is ModuleDecl dd)) {
        if (decl.Signature.ModuleDef == null) {
          reporter.Error(MessageSource.Resolver, Path[k],
            Resolver.ModuleNotFoundErrorMessage(k, Path, " because of previous error"));
        } else {
          reporter.Error(MessageSource.Resolver, Path[k], Resolver.ModuleNotFoundErrorMessage(k, Path));
        }
        return null;
      }

      // Any aliases along the qualified path ought to be already resolved,
      // else the modules are not being resolved in the right order
      if (dd is AliasModuleDecl amd) {
        Contract.Assert(amd.Signature != null);
      }
      decl = dd;
    }

    return decl;
  }
}