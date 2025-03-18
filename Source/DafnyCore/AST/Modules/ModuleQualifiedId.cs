using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class ModuleQualifiedId : NodeWithoutOrigin, IHasReferences {
  public List<Name> Path; // Path != null && Path.Count > 0

  // The following are filled in during resolution
  // Note that the root (first path segment) is resolved initially,
  // as it is needed to determine dependency relationships.
  // Then later the rest of the path is resolved, at which point all of the
  // ids in the path have been fully resolved
  // Note also that the resolution of the root depends on the syntactice location
  // of the qualified id; the resolution of subsequent ids depends on the
  // default export set of the previous id.
  [FilledInDuringResolution] public ModuleDecl Root { get; set; } // the module corresponding to Path[0].val
  [FilledInDuringResolution] public ModuleDecl Decl { get; private set; } // the module corresponding to the full path
  [FilledInDuringResolution] public ModuleDefinition Def { get; private set; } // the module definition corresponding to the full path
  [FilledInDuringResolution] public ModuleSignature Sig { get; set; } // the module signature corresponding to the full path

  [SyntaxConstructor]
  public ModuleQualifiedId(List<Name> path) {
    Origin = new SourceOrigin(path.First().StartToken, path.Last().EndToken, path.Last().Center);
    Contract.Assert(path != null && path.Count > 0);
    Path = path; // note that the list is aliased -- not to be modified after construction
  }

  public override TokenRange EntireRange => Origin.EntireRange!;
  public override IOrigin Origin { get; }

  public ModuleQualifiedId(Cloner cloner, ModuleQualifiedId original) {
    Path = original.Path.Select(n => n.Clone(cloner)).ToList();
    Origin = cloner.Origin(original.Origin);
    if (cloner.CloneResolvedFields) {
      Root = original.Root;
    }
  }

  public string RootName() {
    return Path[0].Value;
  }

  public IOrigin RootToken() {
    return Path[0].StartToken;
  }

  public override string ToString() {
    string s = Path[0].Value;
    for (int i = 1; i < Path.Count; ++i) {
      s = s + "." + Path[i].Value;
    }

    return s;
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

  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override IEnumerable<INode> PreResolveChildren => Children;


  public IEnumerable<Reference> GetReferences() {
    // Normally the target should already have been resolved, but in certain conditions like an unused alias module decl,
    // Decl might not be set yet so we need to resolve it here.

    var reference = new Reference(Path.Last().ReportingRange, ResolveTarget(new ErrorReporterSink(DafnyOptions.Default)));
    return Enumerable.Repeat(reference, 1);
  }

  /// <summary>
  /// Returns the resolved Module declaration corresponding to the qualified module id
  /// Requires the root to have been resolved
  /// Issues an error and returns null if the path is not valid
  /// </summary>
  public ModuleDecl ResolveTarget(ErrorReporter reporter) {

    Contract.Requires(this != null);
    Contract.Requires(Path.Count > 0);

    if (Decl == null) {
      Decl = ResolveTargetUncached(reporter);
    }

    return Decl;
  }

  private ModuleDecl ResolveTargetUncached(ErrorReporter reporter) {
    if (Root == null) {
      return null;
    }

    var decl = Root;
    for (int k = 1; k < Path.Count; k++) {
      ModuleSignature p;
      if (decl is LiteralModuleDecl literalModuleDecl) {
        p = literalModuleDecl.DefaultExport;
        if (p == null) {
          reporter.Error(MessageSource.Resolver, Path[k],
            ProgramResolver.ModuleNotFoundErrorMessage(k, Path, $" because {decl.Name} does not have a default export"));
          return null;
        }
      } else {
        p = decl.Signature;
      }

      var tld = p.TopLevels.GetValueOrDefault(Path[k].Value, null);
      if (tld is not ModuleDecl dd) {
        if (decl.Signature.ModuleDef == null) {
          reporter.Error(MessageSource.Resolver, Path[k],
            ProgramResolver.ModuleNotFoundErrorMessage(k, Path, " because of previous error"));
        } else {
          reporter.Error(MessageSource.Resolver, Path[k], ProgramResolver.ModuleNotFoundErrorMessage(k, Path));
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