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
/// Create implementations for all "Call$$" procedures by making them
/// call the respective "Impl$$ implementations. This allows to implement
/// inlining of Dafny methods further down the road.
/// </summary>
public class AddImplementationsForCallsRewriter : ReadOnlyVisitor {

  private const string CallPrefix = "Call$$";
  private readonly DafnyOptions options;
  private List<Implementation> implsToAdd = new();

  private Program /*?*/ program;

  public AddImplementationsForCallsRewriter(DafnyOptions options) {
    this.options = options;
  }

  public override Procedure /*?*/ VisitProcedure(Procedure /*?*/ node) {
    if (node == null || !node.Name.StartsWith(CallPrefix) ||
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
    var block = new Block(new Token(), "anon_0", new List<Cmd> { cmd },
      new ReturnCmd(new Token()));
    // construct the new implementation:
    var callerImpl = new Implementation(new Token(), callerName,
      node.TypeParameters, inParams, outParams, vars,
      new List<Block> { block }, node.Attributes);
    callerImpl.Proc = node;
    implsToAdd.Add(callerImpl);
    return node;
  }

  public override Program VisitProgram(Program node) {
    program = node;
    implsToAdd = new();
    node = base.VisitProgram(node);
    node.AddTopLevelDeclarations(implsToAdd);
    return Utils.DeepCloneResolvedProgram(node, options);
  }
}