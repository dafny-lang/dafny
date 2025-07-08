// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using static Microsoft.Dafny.RewriterErrors;

namespace Microsoft.Dafny {
  // ------------------- PrintEffectEnforcement -------------------

  public class PrintEffectEnforcement : IRewriter {
    internal PrintEffectEnforcement(ErrorReporter reporter) : base(reporter) {
      Contract.Requires(reporter != null);
    }

    internal override void PostDecreasesResolve(ModuleDefinition m) {
      foreach (var decl in m.TopLevelDecls) {
        if (decl is IteratorDecl iter) {
          var hasPrintAttribute = HasPrintAttribute(iter.Attributes);
          if (!hasPrintAttribute && iter.Body != null) {
            if (Reporter.Options.EnforcePrintEffects) {
              iter.Body.Body.ForEach(stmt => CheckNoPrintEffects(stmt, iter));
            }
          }
        } else if (decl is TopLevelDeclWithMembers cl) {
          foreach (var member in cl.Members) {
            var hasPrintAttribute = HasPrintAttribute(member.Attributes);
            if (member is Function f) {
              if (hasPrintAttribute) {
                ReportError(ErrorId.rw_print_attribute_forbidden_on_functions, member.Origin, ":print attribute is not allowed on functions");
              }
              if (f.ByMethodDecl != null && Reporter.Options.EnforcePrintEffects) {
                f.ByMethodDecl.Body.Body.ForEach(stmt => CheckNoPrintEffects(stmt, f.ByMethodDecl));
              }
            } else if (member is MethodOrConstructor method) {
              if (hasPrintAttribute) {
                if (member.IsGhost) {
                  ReportError(ErrorId.rw_print_attribute_forbidden_on_ghost_methods, member.Origin, ":print attribute is not allowed on ghost methods");
                } else if (method.OverriddenMethod != null && !HasPrintAttribute(method.OverriddenMethod.Attributes, false)) {
                  ReportError(ErrorId.rw_override_must_preserve_printing, member.Origin,
                    "not allowed to override a non-printing method with a possibly printing method ('{0}')", method.Name);
                }
              } else if (!member.IsGhost && method.Body != null) {
                if (Reporter.Options.EnforcePrintEffects) {
                  method.Body.Body.ForEach(stmt => CheckNoPrintEffects(stmt, method));
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
        ReportError(ErrorId.rw_print_attribute_takes_no_arguments, printAttribute.Args[0].Origin, ":print attribute does not take any arguments");
      }
      return printAttribute != null;
    }

    private void CheckNoPrintEffects(Statement stmt, IMethodCodeContext codeContext) {
      if (stmt is PrintStmt) {
        var method = codeContext as MethodOrConstructor;
        if (method is Method method2 && method2.IsByMethod) {
          ReportError(ErrorId.rw_no_print_in_function_by_method, stmt.Origin, "a function-by-method is not allowed to use print statements");
        } else {
          ReportError(ErrorId.rw_print_attribute_required_to_print, stmt.Origin,
            "to use a print statement, the enclosing {0} must be marked with {{:print}}", method?.WhatKind ?? ((IteratorDecl)codeContext).WhatKind);
        }
      } else if (stmt is CallStmt call) {
        if (HasPrintAttribute(call.Method.Attributes, false)) {
          var method = codeContext as MethodOrConstructor;
          if (method is Method method2 && method2.IsByMethod) {
            ReportError(ErrorId.rw_function_by_method_may_not_call_printing_method, stmt.Origin, "a function-by-method is not allowed to call a method with print effects");
          } else {
            ReportError(ErrorId.rw_must_be_print_to_call_printing_method, stmt.Origin,
              "to call a method with print effects, the enclosing {0} must be marked with {{:print}}",
              method?.WhatKind ?? ((IteratorDecl)codeContext).WhatKind);
          }
        }
      }
      stmt.SubStatements.ForEach(s => CheckNoPrintEffects(s, codeContext));
    }
  }
}
