// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

#nullable disable
using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Formal = Microsoft.Boogie.Formal;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using LocalVariable = Microsoft.Boogie.LocalVariable;
using Program = Microsoft.Boogie.Program;
using Token = Microsoft.Boogie.Token;

namespace DafnyTestGeneration.Inlining;

/// <summary>
/// Create implementations for all "CallPost$$" procedures by making them
/// call the respective "Impl$$ implementations. This allows to implement
/// inlining of Dafny methods further down the road.
/// </summary>
public class AddImplementationsForCallsRewriter : ReadOnlyVisitor {

  private readonly DafnyOptions options;
  private List<Implementation> implsToAdd = [];

  private Program /*?*/ program;

  public AddImplementationsForCallsRewriter(DafnyOptions options) {
    this.options = options;
  }

  public override Procedure /*?*/ VisitProcedure(Procedure /*?*/ node) {
    if (node == null || !node.Name.StartsWith(BoogieGenerator.CallPrefix + BoogieGenerator.NameSeparator) ||
        node.Name.EndsWith(ProgramModifier.CtorPostfix)) {
      return node;
    }

    var callerName = node.Name;
    var calleeName = $"{ProgramModifier.ImplPrefix}{node.Name.Split("$").Last()}";
    var calleeProc = program?.Procedures
      .Where(f => f.Name == calleeName)
      .FirstOrDefault((Procedure)null);
    if (calleeProc == null) {
      return node; // Can happen if included modules are not verified
    }

    // define local variables to hold unused return values:
    var vars = calleeProc.OutParams
      .Where(p1 => !node.OutParams
        .Exists(p2 => p2.Name == p1.Name)).ToList()
      .ConvertAll(p1 =>
        (Variable)new LocalVariable(new Token(), (TypedIdent)p1.TypedIdent.Clone())).ToList();
    // you cannot directly reuse node.InParams and node.OutParams
    // because they might contain where clauses which have to be removed
    var inParams = node.InParams.ConvertAll(v =>
      (Variable)new Formal(new Token(),
        new TypedIdent(new Token(), v.Name, v.TypedIdent.Type), true)).ToList();
    var outParams = node.OutParams.ConvertAll(v =>
      (Variable)new Formal(new Token(),
        new TypedIdent(new Token(), v.Name, v.TypedIdent.Type), false)).ToList();
    var returnVars = outParams.Concat(vars);
    // construct the call to the "Impl$$" implementation:
    var cmd = new CallCmd(new Token(), calleeName,
      inParams
        .ConvertAll(v => (Expr)new IdentifierExpr(new Token(), v))
        .ToList(),
      calleeProc.OutParams
        .ConvertAll(v => new IdentifierExpr(new Token(), returnVars.First(rv => rv.Name == v.Name)))
        .ToList());
    cmd.Proc = calleeProc;
    // create a block for this call:
    var block = new Block(new Token(), "anon_0", [cmd],
      new ReturnCmd(new Token()));
    // construct the new implementation:
    var callerImpl = new Implementation(new Token(), callerName,
      node.TypeParameters, inParams, outParams, vars,
      [block], node.Attributes);
    callerImpl.Proc = node;
    implsToAdd.Add(callerImpl);
    return node;
  }

  public override Implementation VisitImplementation(Implementation node) {
    this.VisitVariableSeq(node.LocVars);
    this.VisitBlockList(node.Blocks);
    if (node.Proc is not null) {
      // TODO: The overall test generation code should be refactored so that
      // this case can't occur. The default visitor for Implementation nodes
      // has an invariant that node.Proc is never null. That invariant did
      // not lead to an NPE until Boogie 3.0.1, however.
      node.Proc = (Procedure)node.Proc.StdDispatch((StandardVisitor)this);
    }
    return (Implementation)this.VisitDeclWithFormals((DeclWithFormals)node);
  }

  public override Program VisitProgram(Program node) {
    program = node;
    implsToAdd = [];
    node = base.VisitProgram(node);
    node.AddTopLevelDeclarations(implsToAdd);
    return Utils.DeepCloneResolvedProgram(node, options);
  }
}