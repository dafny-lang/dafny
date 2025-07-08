// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;
using Function = Microsoft.Dafny.Function;

namespace DafnyTestGeneration.Inlining;

/// <summary>
/// Separates the bodies of function-by-methods into separate methods so that translator will process them accordingly.
/// </summary>
public class SeparateByMethodRewriter : IRewriter {

  private readonly List<Method> methodsToAdd = [];

  protected internal SeparateByMethodRewriter(ErrorReporter reporter) :
    base(reporter) {
  }

  internal void PostResolve(Program program) {
    SeparateByMethod(program.DefaultModule);
  }

  private void SeparateByMethod(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.Children.OfType<TopLevelDecl>().ForEach(SeparateByMethod);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      methodsToAdd.Clear();
      withMembers.Members.OfType<Function>().ForEach(SeparateByMethod);
      withMembers.Members.AddRange(methodsToAdd);
    }
  }

  private void SeparateByMethod(Function func) {
    if (func.ByMethodBody == null || func.ByMethodDecl == null) {
      return;
    }
    methodsToAdd.Add(func.ByMethodDecl);
  }
}