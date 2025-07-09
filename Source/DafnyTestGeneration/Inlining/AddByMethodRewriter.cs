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

/// <summary> Turns each function into a function-by-method and removes all opaque attributes. </summary>
public class AddByMethodRewriter : IRewriter {

  // determines whether byMethod body should be added to a function
  private readonly Func<MemberDecl, bool> shouldProcessPredicate;

  protected internal AddByMethodRewriter(ErrorReporter reporter, Func<MemberDecl, bool> shouldProcessPredicate)
    : base(reporter) {
    this.shouldProcessPredicate = shouldProcessPredicate;
  }

  internal void PreResolve(Program program) {
    AddByMethod(program.DefaultModule);
  }

  private void AddByMethod(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.Children.OfType<TopLevelDecl>().ForEach(AddByMethod);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.OfType<Function>().ForEach(AddByMethod);
    }
  }

  private static Attributes RemoveOpaqueAttr(Attributes attributes, Cloner cloner) {
    if (attributes == null) {
      return null;
    }

    if (attributes.Name == "opaque") {
      RemoveOpaqueAttr(attributes.Prev, cloner);
    }

    if (attributes is UserSuppliedAttributes) {
      var usa = (UserSuppliedAttributes)attributes;
      return new UserSuppliedAttributes(
        cloner.Origin(usa.Origin),
        cloner.Origin(usa.OpenBrace),
        cloner.Origin(usa.CloseBrace),
        attributes.Args.ConvertAll(cloner.CloneExpr),
        RemoveOpaqueAttr(attributes.Prev, cloner));
    }

    return new Attributes(attributes.Name,
      attributes.Args.ConvertAll(cloner.CloneExpr),
      RemoveOpaqueAttr(attributes.Prev, cloner));
  }

  private void AddByMethod(Function func) {

    func.Attributes = RemoveOpaqueAttr(func.Attributes, new Cloner());
    if (func.IsGhost ||
        func.Body == null ||
        func.ByMethodBody != null || !shouldProcessPredicate(func)) {
      return;
    }

    var returnStatement = new ReturnStmt(func.Body.Origin,
      [new ExprRhs(new Cloner().CloneExpr(func.Body))]);
    func.ByMethodBody = new BlockStmt(
      func.Body.Origin,
      [returnStatement]);
    func.ByMethodTok = func.Body.Origin;
  }
}