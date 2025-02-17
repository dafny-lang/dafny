//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// This class contains the logic to figure out if a subset types and newtypes have compilable constraints.
/// This analysis leads to the setting of the .ConstraintIsCompilable field of the declarations of those types.
/// </summary>
class AnalyzeTypeConstraints {
  public static void AssignConstraintIsCompilable(List<TopLevelDecl> declarations, DafnyOptions options) {
    // It's important to do the declarations in topological order from how they depend on each other.
    declarations = TopologicallySortedTopLevelDecls(declarations);

    foreach (var d in declarations.Where(decl => decl is SubsetTypeDecl or NewtypeDecl)) {
      var declWithConstraints = (RedirectingTypeDecl)d;

      var constraintIsCompilable = true;

      // Check base type
      var baseType = (declWithConstraints.Var?.Type ?? ((NewtypeDecl)declWithConstraints).BaseType).NormalizeExpandKeepConstraints();
      if (baseType.AsRedirectingType is (SubsetTypeDecl or NewtypeDecl) and var baseDecl) {
        constraintIsCompilable &= baseDecl.ConstraintIsCompilable;
      }

      // Check the type's constraint
      if (declWithConstraints.Constraint != null) {
        constraintIsCompilable &= ExpressionTester.CheckIsCompilable(options, null, declWithConstraints.Constraint,
          new CodeContextWrapper(declWithConstraints, true));
      }

      declWithConstraints.ConstraintIsCompilable = constraintIsCompilable;
    }
  }

  /// <summary>
  /// Return "declarations" in sorted order, so that each declaration is preceded by those on which it depends.
  /// It is assumed that "declarations" are all from the same module and that the call graph of that module has been constructed.
  /// If there's some given declaration that's not in the call graph, then that's fine; it just means that the call
  /// graph does not constrain the output order of that declaration.
  /// </summary>
  private static List<TopLevelDecl> TopologicallySortedTopLevelDecls(List<TopLevelDecl> declarations) {
    // Dependency information among the declarations is stored in the enclosing module's call graph. To get to that
    // call graph, we need to have the module declaration, which we obtain from one of the given declarations:
    if (declarations.Count == 0) {
      return declarations;
    }
    var enclosingModule = declarations[0].EnclosingModule;
    Contract.Assert(declarations.TrueForAll(decl => decl.EnclosingModule == enclosingModule));

    // From the module declaration, we get the components sorted according to how they depend on each other.
    var sortedComponents = enclosingModule.CallGraph.TopologicallySortedComponents();

    // But... this is a list of ICallable's (which also includes MemberDecl's and may not contain all TopLevelDecl's).
    // So, we filter the ICallable's to consider only the given TopLevelDecl's. We also remember which declarations we
    // have added to the output, so we later can add all the remaining ones.
    var remainingDecls = new HashSet<TopLevelDecl>(declarations);
    var output = new List<TopLevelDecl>();
    foreach (var callable in sortedComponents) {
      if (callable is TopLevelDecl topLevelDecl && remainingDecls.Contains(topLevelDecl)) {
        output.Add(topLevelDecl);
        remainingDecls.Remove(topLevelDecl);
      }
    }

    // Finally, add in those TopLevelDecl's that were not in the call graph.
    foreach (var decl in declarations) {
      if (remainingDecls.Contains(decl)) {
        output.Add(decl);
      }
    }
    Contract.Assert(declarations.Count == output.Count); // this assumes there were no duplicates in the given declarations

    return output;
  }

}
