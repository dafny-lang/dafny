// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  // ------------------- PrintEffectEnforcement -------------------

  public class PrintEffectEnforcement : IRewriter {
    private DafnyOptions options;
    internal PrintEffectEnforcement(ErrorReporter reporter, DafnyOptions options) : base(reporter) {
      Contract.Requires(reporter != null);
      this.options = options;
    }

    internal override void PostDecreasesResolve(ModuleDefinition m) {
      foreach (var decl in m.TopLevelDecls) {
        if (decl is IteratorDecl iter) {
          var hasPrintAttribute = HasPrintAttribute(iter.Attributes);
          if (!hasPrintAttribute && iter.Body != null) {
            if (options.EnforcePrintEffects) {
              iter.Body.Body.Iter(stmt => CheckNoPrintEffects(stmt, iter));
            }
          }
        } else if (decl is TopLevelDeclWithMembers cl) {
          foreach (var member in cl.Members) {
            var hasPrintAttribute = HasPrintAttribute(member.Attributes);
            if (member is Function f) {
              if (hasPrintAttribute) {
                Reporter.Error(MessageSource.Rewriter, member.tok, ":print attribute is not allowed on functions");
              }
              if (f.ByMethodDecl != null && options.EnforcePrintEffects) {
                f.ByMethodDecl.Body.Body.Iter(stmt => CheckNoPrintEffects(stmt, f.ByMethodDecl));
              }
            } else if (member is Method method) {
              if (hasPrintAttribute) {
                if (member.IsGhost) {
                  Reporter.Error(MessageSource.Rewriter, member.tok, ":print attribute is not allowed on ghost methods");
                } else if (method.OverriddenMethod != null && !HasPrintAttribute(method.OverriddenMethod.Attributes, false)) {
                  Reporter.Error(MessageSource.Rewriter, member.tok,
                    "not allowed to override a non-printing method with a possibly printing method ('{0}')", method.Name);
                }
              } else if (!member.IsGhost && method.Body != null) {
                if (options.EnforcePrintEffects) {
                  method.Body.Body.Iter(stmt => CheckNoPrintEffects(stmt, method));
                }
              }
            }
          }
        }
      }
    }

    bool HasPrintAttribute(Attributes attrs, bool checkParameters = true) {
      var printAttribute = Attributes.Find(attrs, "print");
      if (checkParameters && printAttribute != null && printAttribute.Args.Count != 0) {
        Reporter.Error(MessageSource.Rewriter, printAttribute.Args[0].tok, ":print attribute does not take any arguments");
      }
      return printAttribute != null;
    }

    private void CheckNoPrintEffects(Statement stmt, IMethodCodeContext codeContext) {
      if (stmt is PrintStmt) {
        var method = codeContext as Method;
        if (method != null && method.IsByMethod) {
          Reporter.Error(MessageSource.Rewriter, stmt.Tok, "a function-by-method is not allowed to use print statements");
        } else {
          Reporter.Error(MessageSource.Rewriter, stmt.Tok,
            "to use a print statement, the enclosing {0} must be marked with {{:print}}", method?.WhatKind ?? ((IteratorDecl)codeContext).WhatKind);
        }
      } else if (stmt is CallStmt call) {
        if (HasPrintAttribute(call.Method.Attributes, false)) {
          var method = codeContext as Method;
          if (method != null && method.IsByMethod) {
            Reporter.Error(MessageSource.Rewriter, stmt.Tok, "a function-by-method is not allowed to call a method with print effects");
          } else {
            Reporter.Error(MessageSource.Rewriter, stmt.Tok,
              "to call a method with print effects, the enclosing {0} must be marked with {{:print}}",
              method?.WhatKind ?? ((IteratorDecl)codeContext).WhatKind);
          }
        }
      }
      stmt.SubStatements.Iter(s => CheckNoPrintEffects(s, codeContext));
    }
  }
}
