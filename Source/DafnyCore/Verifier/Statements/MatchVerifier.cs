using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using VCGeneration.Splits;
using IdentifierExpr = Microsoft.Boogie.IdentifierExpr;
using Type = Microsoft.Dafny.Type;

namespace DafnyCore.Verifier.Statements;

public class MatchStmtVerifier {
  public static void TrMatchStmt(BoogieGenerator generator, MatchStmt stmt, BoogieStmtListBuilder builder, Variables locals, BoogieGenerator.ExpressionTranslator etran) {
    Contract.Requires(stmt != null);
    Contract.Requires(builder != null);
    Contract.Requires(locals != null);
    Contract.Requires(etran != null);

    FillMissingCases(stmt);

    generator.TrStmt_CheckWellformed(stmt.Source, builder, locals, etran, true);
    Expr source = etran.TrExpr(stmt.Source);
    var b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
    b.Add(BoogieGenerator.TrAssumeCmd(stmt.Origin, Expr.False));
    StmtList els = b.Collect(stmt.Origin);
    IfCmd ifCmd = null;
    foreach (var missingCtor in stmt.MissingCases) {
      // havoc all bound variables
      b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
      var newLocals = new Variables();
      Expr r = generator.CtorInvocation(stmt.Origin, missingCtor, etran, newLocals, b);
      locals.AddRange(newLocals.Values);

      if (newLocals.Count != 0) {
        List<IdentifierExpr> havocIds = [];
        foreach (Variable local in newLocals.Values) {
          havocIds.Add(new IdentifierExpr(local.tok, local));
        }
        builder.Add(new HavocCmd(stmt.Origin, havocIds));
      }
      String missingStr = stmt.Context.FillHole(new IdCtx(missingCtor)).AbstractAllHoles()
        .ToString();
      var desc = new MatchIsComplete("statement", missingStr);
      b.Add(generator.Assert(stmt.Origin, Expr.False, desc, builder.Context));

      Expr guard = Expr.Eq(source, r);
      ifCmd = new IfCmd(stmt.Origin, guard, b.Collect(stmt.Origin), ifCmd, els);
      els = null;
    }
    for (int i = stmt.Cases.Count; 0 <= --i;) {
      var mc = stmt.Cases[i];
      generator.CurrentIdGenerator.Push();
      // havoc all bound variables
      b = new BoogieStmtListBuilder(generator, generator.Options, builder.Context);
      var newLocals = new Variables();
      Expr r = CtorInvocation(generator, mc, stmt.Source.Type, etran, newLocals, b,
        stmt.IsGhost ? BoogieGenerator.NOALLOC : BoogieGenerator.ISALLOC);
      locals.AddRange(newLocals.Values);

      if (newLocals.Count != 0) {
        List<IdentifierExpr> havocIds = [];
        foreach (Variable local in newLocals.Values) {
          havocIds.Add(new IdentifierExpr(local.tok, local));
        }
        builder.Add(new HavocCmd(mc.Origin, havocIds));
      }

      // translate the body into b
      var prevDefiniteAssignmentTrackers = generator.DefiniteAssignmentTrackers;
      generator.TrStmtList(mc.Body, b, locals, etran);
      generator.DefiniteAssignmentTrackers = prevDefiniteAssignmentTrackers;

      Expr guard = Expr.Eq(source, r);
      ifCmd = new IfCmd(mc.Origin, guard, b.Collect(mc.Origin), ifCmd, els, BlockRewriter.AllowSplitQ);
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

  /// <summary>
  /// If "declareLocals" is "false", then the locals are added only if they are new, that is, if
  /// they don't already exist in "locals".
  /// </summary>
  private static Expr CtorInvocation(BoogieGenerator generator, MatchCase mc, Type sourceType,
    BoogieGenerator.ExpressionTranslator etran, Variables locals, BoogieStmtListBuilder localTypeAssumptions,
    IsAllocType isAlloc, bool declareLocals = true) {
    Contract.Requires(mc != null);
    Contract.Requires(sourceType != null);
    Contract.Requires(etran != null);
    Contract.Requires(locals != null);
    Contract.Requires(localTypeAssumptions != null);
    Contract.Ensures(Contract.Result<Expr>() != null);

    sourceType = sourceType.NormalizeExpand();
    Contract.Assert(sourceType.TypeArgs.Count == mc.Ctor.EnclosingDatatype.TypeArgs.Count);
    var subst = new Dictionary<TypeParameter, Type>();
    for (var i = 0; i < mc.Ctor.EnclosingDatatype.TypeArgs.Count; i++) {
      subst.Add(mc.Ctor.EnclosingDatatype.TypeArgs[i], sourceType.TypeArgs[i]);
    }

    List<Expr> args = [];
    for (int i = 0; i < mc.Arguments.Count; i++) {
      BoundVar p = mc.Arguments[i];
      var nm = p.AssignUniqueName(generator.CurrentDeclaration.IdGenerator);
      Variable local = declareLocals ? null : locals.GetValueOrDefault(nm);  // find previous local
      if (local == null) {
        local = new Microsoft.Boogie.LocalVariable(p.Origin, new TypedIdent(p.Origin, nm, generator.TrType(p.Type)));
        locals.Add(local);
      } else {
        Contract.Assert(Equals(local.TypedIdent.Type, generator.TrType(p.Type)));
      }
      var pFormalType = mc.Ctor.Formals[i].Type.Subst(subst);
      var pIsAlloc = (isAlloc == BoogieGenerator.ISALLOC) ? generator.IsAllocContext.Var(p) : BoogieGenerator.NOALLOC;
      Expr wh = generator.GetWhereClause(p.Origin, new IdentifierExpr(p.Origin, local), pFormalType, etran, pIsAlloc);
      if (wh != null) {
        localTypeAssumptions.Add(BoogieGenerator.TrAssumeCmd(p.Origin, wh));
      }
      generator.CheckSubrange(p.Origin, new IdentifierExpr(p.Origin, local), pFormalType, p.Type,
        new Microsoft.Dafny.IdentifierExpr(p.Origin, p), localTypeAssumptions);
      args.Add(generator.CondApplyBox(mc.Origin, new IdentifierExpr(p.Origin, local), Cce.NonNull(p.Type), mc.Ctor.Formals[i].Type));
    }
    IdentifierExpr id = new IdentifierExpr(mc.Origin, mc.Ctor.FullName, generator.Predef.DatatypeType);
    return new NAryExpr(mc.Origin, new FunctionCall(id), args);
  }

  public static void TrMatchExpr(BoogieGenerator boogieGenerator, MatchExpr me, WFOptions wfOptions, Variables locals,
    BoogieStmtListBuilder builder, BoogieGenerator.ExpressionTranslator etran, BoogieGenerator.AddResultCommands addResultCommands) {
    FillMissingCases(me);

    boogieGenerator.CheckWellformed(me.Source, wfOptions, locals, builder, etran);
    Expr src = etran.TrExpr(me.Source);
    IfCmd ifCmd = null;
    BoogieStmtListBuilder elsBldr = new BoogieStmtListBuilder(boogieGenerator, boogieGenerator.Options, builder.Context);
    elsBldr.Add(BoogieGenerator.TrAssumeCmd(me.Origin, Expr.False));
    StmtList els = elsBldr.Collect(me.Origin);
    foreach (var missingCtor in me.MissingCases) {
      // havoc all bound variables
      var b = new BoogieStmtListBuilder(boogieGenerator, boogieGenerator.Options, builder.Context);
      var newLocals = new Variables();
      Expr r = boogieGenerator.CtorInvocation(me.Origin, missingCtor, etran, newLocals, b);
      locals.AddRange(newLocals.Values);

      if (newLocals.Count != 0) {
        List<IdentifierExpr> havocIds = [];
        foreach (Variable local in newLocals.Values) {
          havocIds.Add(new IdentifierExpr(local.tok, local));
        }

        builder.Add(new HavocCmd(me.Origin, havocIds));
      }

      String missingStr = me.Context.FillHole(new IdCtx(missingCtor)).AbstractAllHoles().ToString();
      b.Add(boogieGenerator.Assert(boogieGenerator.GetToken(me), Expr.False,
        new MatchIsComplete("expression", missingStr), builder.Context));

      Expr guard = Expr.Eq(src, r);
      ifCmd = new IfCmd(me.Origin, guard, b.Collect(me.Origin), ifCmd, els, BlockRewriter.AllowSplitQ);
      els = null;
    }

    for (int i = me.Cases.Count; 0 <= --i;) {
      MatchCaseExpr mc = me.Cases[i];
      var b = new BoogieStmtListBuilder(boogieGenerator, boogieGenerator.Options, builder.Context);
      Expr ct = CtorInvocation(boogieGenerator, mc, me.Source.Type, etran, locals, b, BoogieGenerator.NOALLOC, false);
      // generate:  if (src == ctor(args)) { assume args-is-well-typed; mc.Body is well-formed; assume Result == TrExpr(case); } else ...

      boogieGenerator.CheckWellformedWithResult(mc.Body, wfOptions, locals, b, etran, addResultCommands);
      ifCmd = new IfCmd(mc.Origin, Expr.Eq(src, ct), b.Collect(mc.Origin), ifCmd, els);
      els = null;
    }

    builder.Add(ifCmd);
  }
}