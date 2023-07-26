// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System;
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

  private readonly List<Method> methodsToAdd = new();
  // determines whether the given function-by-method should be split into a function and a method
  private readonly Func<MemberDecl, bool> shouldProcessPredicate;

  protected internal SeparateByMethodRewriter(ErrorReporter reporter, Func<MemberDecl, bool> shouldProcessPredicate) :
    base(reporter) {
    this.shouldProcessPredicate = shouldProcessPredicate;
  }

  internal void PostResolve(Program program) {
    SeparateByMethod(program.DefaultModule);
  }

  private void SeparateByMethod(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.ForEach(SeparateByMethod);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      methodsToAdd.Clear();
      withMembers.Members.Where(shouldProcessPredicate).OfType<Function>().ForEach(SeparateByMethod);
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