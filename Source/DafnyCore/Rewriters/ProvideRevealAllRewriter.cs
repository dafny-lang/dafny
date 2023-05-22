using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ProvideRevealAllRewriter : IRewriter {
  public ProvideRevealAllRewriter(ErrorReporter reporter)
    : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PreResolve(ModuleDefinition m) {
    var declarations = m.TopLevelDecls;

    foreach (var d in declarations) {
      if (d is ModuleExportDecl me) {
        var revealAll = me.RevealAll || Reporter.Options.DisableScopes;

        HashSet<string> explicitlyRevealedTopLevelIDs = null;
        if (!revealAll) {
          explicitlyRevealedTopLevelIDs = new HashSet<string>();
          foreach (var esig in me.Exports) {
            if (esig.ClassId == null && !esig.Opaque) {
              explicitlyRevealedTopLevelIDs.Add(esig.Id);
            }
          }
        }

        if (revealAll || me.ProvideAll) {
          foreach (var newt in declarations) {
            if (!newt.CanBeExported()) {
              continue;
            }

            if (!(newt is DefaultClassDecl)) {
              me.Exports.Add(new ExportSignature(newt.tok, newt.Name, !revealAll || !newt.CanBeRevealed()));
            }

            if (newt is TopLevelDeclWithMembers) {
              var cl = (TopLevelDeclWithMembers)newt;
              var newtIsRevealed = revealAll || explicitlyRevealedTopLevelIDs.Contains(newt.Name);

              foreach (var mem in cl.Members) {
                var opaque = !revealAll || !mem.CanBeRevealed();
                if (newt is DefaultClassDecl) {
                  // add everything from the default class
                  me.Exports.Add(new ExportSignature(mem.tok, mem.Name, opaque));
                } else if (mem is Constructor && !newtIsRevealed) {
                  // "provides *" does not pick up class constructors, unless the class is to be revealed
                } else if (opaque && mem is Field field && !(mem is ConstantField) && !newtIsRevealed) {
                  // "provides *" does not pick up mutable fields, unless the class is to be revealed
                } else {
                  me.Exports.Add(new ExportSignature(cl.tok, cl.Name, mem.tok, mem.Name, opaque));
                }
              }
            }
          }
        }
      }
    }
  }
}