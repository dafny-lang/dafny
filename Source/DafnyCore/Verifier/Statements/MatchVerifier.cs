using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public static class MatchStatementVerifier {
  public static void TrMatchStmt(BoogieGenerator generator, MatchStmt stmt, BoogieStmtListBuilder builder,
    Variables locals, BoogieGenerator.ExpressionTranslator etran) {
    Contract.Requires(stmt != null);
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);

    FillMissingCases(stmt);

    generator.TrStmt_CheckWellformed(stmt.Source, builder, locals, etran, true);
    Boogie.Expr source = etran.TrExpr(stmt.Source);
    var b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
    b.Add(BoogieGenerator.TrAssumeCmd(stmt.Tok, Boogie.Expr.False));
    Boogie.StmtList els = b.Collect(stmt.Tok);
    Boogie.IfCmd ifCmd = null;
    foreach (var missingCtor in stmt.MissingCases) {
      // havoc all bound variables
      b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
      var newLocals = new Variables();
      Boogie.Expr r = CtorInvocation(generator, stmt.Tok, missingCtor, etran, newLocals, b);
      locals.AddRange(newLocals.Values);

      if (newLocals.Count != 0) {
        List<Boogie.IdentifierExpr> havocIds = new List<Boogie.IdentifierExpr>();
        foreach (Variable local in newLocals.Values) {
          havocIds.Add(new Boogie.IdentifierExpr(local.tok, local));
        }
        builder.Add(new Boogie.HavocCmd(stmt.Tok, havocIds));
      }
      String missingStr = stmt.Context.FillHole(new IdCtx(missingCtor)).AbstractAllHoles()
        .ToString();
      var desc = new MatchIsComplete("statement", missingStr);
      b.Add(generator.Assert(stmt.Tok, Boogie.Expr.False, desc, builder.Context));

      Boogie.Expr guard = Boogie.Expr.Eq(source, r);
      ifCmd = new Boogie.IfCmd(stmt.Tok, guard, b.Collect(stmt.Tok), ifCmd, els);
      els = null;
    }
    for (int i = stmt.Cases.Count; 0 <= --i;) {
      var mc = (MatchCaseStmt)stmt.Cases[i];
      generator.CurrentIdGenerator.Push();
      // havoc all bound variables
      b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
      var newLocals = new Variables();
      Boogie.Expr r = CtorInvocation(generator, mc, stmt.Source.Type, etran, newLocals, b, stmt.IsGhost ? BoogieGenerator.NOALLOC : BoogieGenerator.ISALLOC);
      locals.AddRange(newLocals.Values);

      if (newLocals.Count != 0) {
        List<Boogie.IdentifierExpr> havocIds = new List<Boogie.IdentifierExpr>();
        foreach (Variable local in newLocals.Values) {
          havocIds.Add(new Boogie.IdentifierExpr(local.tok, local));
        }
        builder.Add(new Boogie.HavocCmd(mc.tok, havocIds));
      }

      // translate the body into b
      var prevDefiniteAssignmentTrackers = generator.DefiniteAssignmentTrackers;
      generator.TrStmtList(mc.Body, b, locals, etran);
      generator.DefiniteAssignmentTrackers = prevDefiniteAssignmentTrackers;

      Boogie.Expr guard = Boogie.Expr.Eq(source, r);
      ifCmd = new Boogie.IfCmd(mc.tok, guard, b.Collect(mc.tok), ifCmd, els);
      els = null;
      generator.CurrentIdGenerator.Pop();
    }
    if (ifCmd != null) {
      builder.Add(ifCmd);
    }
  }

  private static void FillMissingCases(IMatch match) {
    Contract.Requires(match != null);
    if (match.MissingCases.Any()) {
      return;
    }

    var dtd = match.Source.Type.AsDatatype;
    var constructors = dtd?.ConstructorsByName;

    ISet<string> memberNamesUsed = new HashSet<string>();

    foreach (var matchCase in match.Cases) {
      if (constructors != null) {
        Contract.Assert(dtd != null);
        var ctorId = matchCase.Ctor.Name;
        if (match.Source.Type.AsDatatype is TupleTypeDecl) {
          var tuple = (TupleTypeDecl)match.Source.Type.AsDatatype;
          ctorId = SystemModuleManager.TupleTypeCtorName(tuple.Dims);
        }

        if (constructors.ContainsKey(ctorId)) {
          memberNamesUsed.Add(ctorId); // add mc.Id to the set of names used
        }
      }
    }
    if (dtd != null && memberNamesUsed.Count != dtd.Ctors.Count) {
      // We could complain about the syntactic omission of constructors:
      //   Reporter.Error(MessageSource.Resolver, stmt, "match statement does not cover all constructors");
      // but instead we let the verifier do a semantic check.
      // So, for now, record the missing constructors:
      foreach (var ctr in dtd.Ctors) {
        if (!memberNamesUsed.Contains(ctr.Name)) {
          match.MissingCases.Add(ctr);
        }
      }
      Contract.Assert(memberNamesUsed.Count + match.MissingCases.Count == dtd.Ctors.Count);
    }
  }

  public static void TrMatchExpr(BoogieGenerator generator, MatchExpr me, WFOptions wfOptions, Variables locals,
    BoogieStmtListBuilder builder, BoogieGenerator.ExpressionTranslator etran, BoogieGenerator.AddResultCommands addResultCommands) {
    MatchStatementVerifier.FillMissingCases(me);

    generator.CheckWellformed(me.Source, wfOptions, locals, builder, etran);
    Boogie.Expr src = etran.TrExpr(me.Source);
    Boogie.IfCmd ifCmd = null;
    BoogieStmtListBuilder elsBldr = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
    elsBldr.Add(BoogieGenerator.TrAssumeCmd(me.tok, Boogie.Expr.False));
    StmtList els = elsBldr.Collect(me.tok);
    foreach (var missingCtor in me.MissingCases) {
      // havoc all bound variables
      var b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
      Variables newLocals = new();
      Boogie.Expr r = CtorInvocation(generator, me.tok, missingCtor, etran, newLocals, b);
      locals.AddRange(newLocals.Values);

      if (newLocals.Count != 0) {
        List<Boogie.IdentifierExpr> havocIds = new List<Boogie.IdentifierExpr>();
        foreach (Variable local in newLocals.Values) {
          havocIds.Add(new Boogie.IdentifierExpr(local.tok, local));
        }

        builder.Add(new Boogie.HavocCmd(me.tok, havocIds));
      }

      String missingStr = me.Context.FillHole(new IdCtx(missingCtor)).AbstractAllHoles().ToString();
      b.Add(generator.Assert(generator.GetToken(me), Boogie.Expr.False,
        new MatchIsComplete("expression", missingStr), builder.Context));

      Boogie.Expr guard = Boogie.Expr.Eq(src, r);
      ifCmd = new Boogie.IfCmd(me.tok, guard, b.Collect(me.tok), ifCmd, els);
      els = null;
    }

    for (int i = me.Cases.Count; 0 <= --i;) {
      MatchCaseExpr mc = me.Cases[i];
      var b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
      Boogie.Expr ct = CtorInvocation(generator, mc, me.Source.Type, etran, locals, b, BoogieGenerator.NOALLOC, false);
      // generate:  if (src == ctor(args)) { assume args-is-well-typed; mc.Body is well-formed; assume Result == TrExpr(case); } else ...

      generator.CheckWellformedWithResult(mc.Body, wfOptions, locals, b, etran, addResultCommands);
      ifCmd = new Boogie.IfCmd(mc.tok, Boogie.Expr.Eq(src, ct), b.Collect(mc.tok), ifCmd, els);
      els = null;
    }

    builder.Add(ifCmd);
  }

  /// <summary>
  /// If "declareLocals" is "false", then the locals are added only if they are new, that is, if
  /// they don't already exist in "locals".
  /// </summary>
  private static Boogie.Expr CtorInvocation(BoogieGenerator boogieGenerator, MatchCase mc, Type sourceType,
    BoogieGenerator.ExpressionTranslator etran, Variables locals, BoogieStmtListBuilder localTypeAssumptions,
    IsAllocType isAlloc, bool declareLocals = true) {
    Contract.Requires(mc != null);
    Contract.Requires(sourceType != null);
    Contract.Requires(etran != null);
    Contract.Requires(locals != null);
    Contract.Requires(localTypeAssumptions != null);
    Contract.Requires(boogieGenerator.Predef != null);
    Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

    sourceType = sourceType.NormalizeExpand();
    Contract.Assert(sourceType.TypeArgs.Count == mc.Ctor.EnclosingDatatype.TypeArgs.Count);
    var subst = new Dictionary<TypeParameter, Type>();
    for (var i = 0; i < mc.Ctor.EnclosingDatatype.TypeArgs.Count; i++) {
      subst.Add(mc.Ctor.EnclosingDatatype.TypeArgs[i], sourceType.TypeArgs[i]);
    }

    List<Boogie.Expr> args = new List<Boogie.Expr>();
    for (int i = 0; i < mc.Arguments.Count; i++) {
      BoundVar p = mc.Arguments[i];
      var nm = p.AssignUniqueName(boogieGenerator.CurrentDeclaration.IdGenerator);
      var local = declareLocals ? null : locals.GetValueOrDefault(nm);  // find previous local
      if (local == null) {
        local = locals.GetOrAdd(new Boogie.LocalVariable(p.tok, new Boogie.TypedIdent(p.tok, nm, boogieGenerator.TrType(p.Type))));
      } else {
        Contract.Assert(Boogie.Type.Equals(local.TypedIdent.Type, boogieGenerator.TrType(p.Type)));
      }
      var pFormalType = mc.Ctor.Formals[i].Type.Subst(subst);
      var pIsAlloc = (isAlloc == BoogieGenerator.ISALLOC) ? boogieGenerator.isAllocContext.Var(p) : BoogieGenerator.NOALLOC;
      Boogie.Expr wh = boogieGenerator.GetWhereClause(p.tok, new Boogie.IdentifierExpr(p.tok, local), pFormalType, etran, pIsAlloc);
      if (wh != null) {
        localTypeAssumptions.Add(BoogieGenerator.TrAssumeCmd(p.tok, wh));
      }

      boogieGenerator.CheckSubrange(p.tok, new Boogie.IdentifierExpr(p.tok, local), pFormalType, p.Type, new IdentifierExpr(p.Tok, p), localTypeAssumptions);
      args.Add(boogieGenerator.CondApplyBox(mc.tok, new Boogie.IdentifierExpr(p.tok, local), cce.NonNull(p.Type), mc.Ctor.Formals[i].Type));
    }
    Boogie.IdentifierExpr id = new Boogie.IdentifierExpr(mc.tok, mc.Ctor.FullName, boogieGenerator.Predef.DatatypeType);
    return new Boogie.NAryExpr(mc.tok, new Boogie.FunctionCall(id), args);
  }

  private static Boogie.Expr CtorInvocation(BoogieGenerator generator, IToken tok, DatatypeCtor ctor,
    BoogieGenerator.ExpressionTranslator etran, Variables locals,
    BoogieStmtListBuilder localTypeAssumptions) {
    Contract.Requires(tok != null);
    Contract.Requires(ctor != null);
    Contract.Requires(etran != null);
    Contract.Requires(locals != null);
    Contract.Requires(localTypeAssumptions != null);
    Contract.Requires(generator.Predef != null);
    Contract.Ensures(Contract.Result<Boogie.Expr>() != null);

    // create local variables for the formals
    var varNameGen = generator.CurrentIdGenerator.NestedFreshIdGenerator("a#");
    var args = new List<Boogie.Expr>();
    foreach (Formal arg in ctor.Formals) {
      Contract.Assert(arg != null);
      var nm = varNameGen.FreshId(string.Format("#{0}#", args.Count));
      var bv = locals.GetOrAdd(new Boogie.LocalVariable(arg.tok, new Boogie.TypedIdent(arg.tok, nm, generator.TrType(arg.Type))));
      args.Add(new Boogie.IdentifierExpr(arg.tok, bv));
    }

    Boogie.IdentifierExpr id = new Boogie.IdentifierExpr(tok, ctor.FullName, generator.Predef.DatatypeType);
    return new Boogie.NAryExpr(tok, new Boogie.FunctionCall(id), args);
  }
}