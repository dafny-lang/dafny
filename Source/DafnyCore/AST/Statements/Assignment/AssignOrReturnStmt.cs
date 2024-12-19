using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Parsed from ":-"
/// </summary>
public class AssignOrReturnStmt : ConcreteAssignStatement, ICloneable<AssignOrReturnStmt>, ICanResolve {
  public readonly ExprRhs Rhs; // this is the unresolved RHS, and thus can also be a method call
  public readonly List<AssignmentRhs> Rhss;
  public readonly AttributedToken KeywordToken;
  [FilledInDuringResolution] public readonly List<Statement> ResolvedStatements = new();
  public override IEnumerable<Statement> SubStatements => ResolvedStatements;
  public override IOrigin Tok {
    get {
      var result = Rhs.StartToken.Prev;
      if (char.IsLetter(result.val[0])) {
        // Jump to operator if we're on an assume/expect/assert keyword.
        result = result.Prev;
      }
      return result;
    }
  }

  public override IEnumerable<INode> Children => ResolvedStatements;

  public override IEnumerable<Statement> PreResolveSubStatements => Enumerable.Empty<Statement>();

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Lhss != null);
    Contract.Invariant(
      Lhss.Count == 0 ||                   // ":- MethodOrExpression;" which returns void success or an error
      (Lhss.Count == 1 && Lhss[0] != null)   // "y :- MethodOrExpression;"
    );
    Contract.Invariant(Rhs != null);
  }

  public AssignOrReturnStmt Clone(Cloner cloner) {
    return new AssignOrReturnStmt(cloner, this);
  }

  public AssignOrReturnStmt(Cloner cloner, AssignOrReturnStmt original) : base(cloner, original) {
    Rhs = (ExprRhs)cloner.CloneRHS(original.Rhs);
    Rhss = original.Rhss.ConvertAll(cloner.CloneRHS);
    KeywordToken = cloner.AttributedTok(original.KeywordToken);

    if (cloner.CloneResolvedFields) {
      ResolvedStatements = original.ResolvedStatements.Select(stmt => cloner.CloneStmt(stmt, false)).ToList();
    }
  }

  public AssignOrReturnStmt(IOrigin rangeOrigin, List<Expression> lhss, ExprRhs rhs, AttributedToken keywordToken, List<AssignmentRhs> rhss)
    : base(rangeOrigin, lhss) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(lhss != null);
    Contract.Requires(lhss.Count <= 1);
    Contract.Requires(rhs != null);
    Contract.Requires(rhss != null);
    Rhs = rhs;
    Rhss = rhss;
    KeywordToken = keywordToken;
  }

  public override IEnumerable<Expression> PreResolveSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) {
        yield return e;
      }
      foreach (var e in Lhss) {
        yield return e;
      }
      if (Rhs != null) {
        yield return Rhs.Expr;
      }
      foreach (var rhs in Rhss) {
        foreach (var e in rhs.SubExpressions) {
          yield return e;
        }
      }
    }
  }

  /// <summary>
  /// Desugars "y, ... :- MethodOrExpression" into
  /// var temp;
  /// temp, ... := MethodOrExpression;
  /// if temp.IsFailure() { return temp.PropagateFailure(); }
  /// y := temp.Extract();
  ///
  /// If the type of MethodExpression does not have an Extract, then the desugaring is
  /// var temp;
  /// temp, y, ... := MethodOrExpression;
  /// if temp.IsFailure() { return temp.PropagateFailure(); }
  ///
  /// If there are multiple RHSs then "y, ... :- Expression, ..." becomes
  /// var temp;
  /// temp, ... := Expression, ...;
  /// if temp.IsFailure() { return temp.PropagateFailure(); }
  /// y := temp.Extract();
  /// OR
  /// var temp;
  /// temp, y, ... := Expression, ...;
  /// if temp.IsFailure() { return temp.PropagateFailure(); }
  ///
  /// and "y, ... :- expect MethodOrExpression, ..." into
  /// var temp, [y, ] ... := MethodOrExpression, ...;
  /// expect !temp.IsFailure(), temp.PropagateFailure();
  /// [y := temp.Extract();]
  ///
  /// and saves the result into s.ResolvedStatements.
  /// This is also known as the "elephant operator"
  /// </summary>
  public override void Resolve(ModuleResolver resolver, ResolutionContext resolutionContext) {
    base.Resolve(resolver, resolutionContext);

    ResolveKeywordToken(resolver, resolutionContext);

    // We need to figure out whether we are using a status type that has Extract or not,
    // as that determines how the AssignOrReturnStmt is desugared. Thus if the Rhs is a
    // method call we need to know which one (to inspect its first output); if RHs is a
    // list of expressions, we need to know the type of the first one. For all of this we have
    // to do some partial type resolution.

    bool expectExtract = Lhss.Count != 0; // default value if we cannot determine and inspect the type
    Type firstType = null;
    Method call = null;
    if ((Rhss == null || Rhss.Count == 0) && Rhs.Expr is ApplySuffix asx) {
      resolver.ResolveApplySuffix(asx, resolutionContext, true);
      call = (asx.Lhs.Resolved as MemberSelectExpr)?.Member as Method;
      if (call != null) {
        // We're looking at a method call
        var typeMap = (asx.Lhs.Resolved as MemberSelectExpr)?.TypeArgumentSubstitutionsWithParents();
        if (call.Outs.Count != 0) {
          firstType = call.Outs[0].Type.Subst(typeMap);
        } else {
          resolver.Reporter.Error(MessageSource.Resolver, Rhs.Tok, "Expected {0} to have a Success/Failure output value, but the method returns nothing.", call.Name);
        }
      } else {
        // We're looking at a call to a function. Treat it like any other expression.
        firstType = asx.Type;
      }
    } else {
      resolver.ResolveExpression(Rhs.Expr, resolutionContext);
      firstType = Rhs.Expr.Type;
    }

    var method = (Method)resolutionContext.CodeContext;
    if (method.Outs.Count == 0 && KeywordToken == null) {
      resolver.Reporter.Error(MessageSource.Resolver, Tok, "A method containing a :- statement must have an out-parameter ({0})", method.Name);
      return;
    }
    if (firstType != null) {
      firstType = resolver.PartiallyResolveTypeForMemberSelection(Rhs.Tok, firstType);
      if (firstType.AsTopLevelTypeWithMembers != null) {
        if (firstType.AsTopLevelTypeWithMembers.Members.Find(x => x.Name == "IsFailure") == null) {
          resolver.Reporter.Error(MessageSource.Resolver, Tok,
            "member IsFailure does not exist in {0}, in :- statement", firstType);
          return;
        }
        expectExtract = firstType.AsTopLevelTypeWithMembers.Members.Find(x => x.Name == "Extract") != null;
        if (expectExtract && call == null && Lhss.Count != 1 + Rhss.Count) {
          resolver.Reporter.Error(MessageSource.Resolver, Tok,
            "number of lhs ({0}) must match number of rhs ({1}) for a rhs type ({2}) with member Extract",
            Lhss.Count, 1 + Rhss.Count, firstType);
          return;
        } else if (expectExtract && call != null && Lhss.Count != call.Outs.Count) {
          resolver.Reporter.Error(MessageSource.Resolver, Tok,
            "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) with member Extract",
            Lhss.Count, call.Outs.Count, firstType);
          return;

        } else if (!expectExtract && call == null && Lhss.Count != Rhss.Count) {
          resolver.Reporter.Error(MessageSource.Resolver, Tok,
            "number of lhs ({0}) must be one less than number of rhs ({1}) for a rhs type ({2}) without member Extract", Lhss.Count, 1 + Rhss.Count, firstType);
          return;

        } else if (!expectExtract && call != null && Lhss.Count != call.Outs.Count - 1) {
          resolver.Reporter.Error(MessageSource.Resolver, Tok,
            "wrong number of method result arguments (got {0}, expected {1}) for a rhs type ({2}) without member Extract", Lhss.Count, call.Outs.Count - 1, firstType);
          return;
        }
      } else {
        resolver.Reporter.Error(MessageSource.Resolver, Tok,
          $"The type of the first expression to the right of ':-' could not be determined to be a failure type (got '{firstType}')");
        return;
      }
    } else {
      resolver.Reporter.Error(MessageSource.Resolver, Tok,
        "Internal Error: Unknown failure type in :- statement");
      return;
    }

    Expression lhsExtract = null;
    if (expectExtract) {
      if (resolutionContext.CodeContext is Method caller && caller.Outs.Count == 0 && KeywordToken == null) {
        resolver.Reporter.Error(MessageSource.Resolver, Rhs.Tok, "Expected {0} to have a Success/Failure output value", caller.Name);
        return;
      }

      lhsExtract = Lhss[0];
      var lhsResolved = Lhss[0].Resolved;
      // Make a new unresolved expression
      if (lhsResolved is MemberSelectExpr lexr) {
        Expression id = Expression.AsThis(lexr.Obj) != null ? lexr.Obj : resolver.makeTemp("recv", this, resolutionContext, lexr.Obj);
        var lex = lhsExtract as ExprDotName; // might be just a NameSegment
        lhsExtract = new ExprDotName(lexr.Tok, id, lexr.MemberNameNode, lex == null ? null : lex.OptTypeArguments);
      } else if (lhsResolved is SeqSelectExpr lseq) {
        if (!lseq.SelectOne || lseq.E0 == null) {
          resolver.Reporter.Error(MessageSource.Resolver, Tok,
            "Element ranges not allowed as l-values");
          return;
        }
        Expression id = resolver.makeTemp("recv", this, resolutionContext, lseq.Seq);
        Expression id0 = id0 = resolver.makeTemp("idx", this, resolutionContext, lseq.E0);
        lhsExtract = new SeqSelectExpr(lseq.Tok, lseq.SelectOne, id, id0, null, lseq.CloseParen);
        lhsExtract.Type = lseq.Type;
      } else if (lhsResolved is MultiSelectExpr lmulti) {
        Expression id = resolver.makeTemp("recv", this, resolutionContext, lmulti.Array);
        var idxs = new List<Expression>();
        foreach (var i in lmulti.Indices) {
          Expression idx = resolver.makeTemp("idx", this, resolutionContext, i);
          idxs.Add(idx);
        }
        lhsExtract = new MultiSelectExpr(lmulti.Tok, id, idxs);
        lhsExtract.Type = lmulti.Type;
      } else if (lhsResolved is IdentifierExpr) {
        // do nothing
      } else if (lhsResolved == null) {
        // LHS failed to resolve. Abort trying to resolve assign or return stmt
        return;
      } else {
        throw new InvalidOperationException("Internal error: unexpected option in ResolveAssignOrReturnStmt");
      }
    }

    DesugarElephantStatement(expectExtract, lhsExtract, firstType, resolver, (Method)resolutionContext.CodeContext);
    ResolvedStatements.ForEach(a => resolver.ResolveStatement(a, resolutionContext));
    resolver.EnsureSupportsErrorHandling(Tok, firstType, expectExtract, KeywordToken?.Token.val);
  }

  public void ResolveKeywordToken(INewOrOldResolver resolver, ResolutionContext resolutionContext) {
    if (KeywordToken == null) {
      return;
    }

    if (!resolver.Options.Get(CommonOptionBag.AllowAxioms) && KeywordToken.Token.val == "assume" && !KeywordToken.IsExplicitAxiom()) {
      resolver.Reporter.Warning(MessageSource.Verifier, ResolutionErrors.ErrorId.none, KeywordToken.Token, "assume keyword in update-with-failure statement has no {:axiom} annotation");
    }

    resolver.ResolveAttributes(KeywordToken, resolutionContext);
  }

  /// <summary>
  /// Add to .Resolved
  /// </summary>
  /// <param name="expectExtract"></param>
  /// <param name="lhsExtract"></param>
  /// <param name="firstType"></param>
  /// <param name="resolver"></param>
  /// <param name="enclosingMethod"></param>
  private void DesugarElephantStatement(bool expectExtract, Expression lhsExtract, Type firstType,
    ModuleResolver resolver, Method enclosingMethod) {

    var temp = resolver.FreshTempVarName("valueOrError", enclosingMethod);
    var lhss = new List<LocalVariable>() { new LocalVariable(Origin, temp, new InferredTypeProxy(), false) };
    // "var temp ;"
    ResolvedStatements.Add(new VarDeclStmt(Origin, lhss, null));
    var lhss2 = new List<Expression>() { new IdentifierExpr(Tok, temp) };
    for (int k = (expectExtract ? 1 : 0); k < Lhss.Count; ++k) {
      lhss2.Add(Lhss[k]);
    }
    List<AssignmentRhs> rhss2 = new List<AssignmentRhs>() { Rhs };
    if (Rhss != null) {
      Rhss.ForEach(e => rhss2.Add(e));
    }
    if (Rhss != null && Rhss.Count > 0) {
      if (lhss2.Count != rhss2.Count) {
        resolver.reporter.Error(MessageSource.Resolver, Tok,
          "Mismatch in expected number of LHSs and RHSs");
        if (lhss2.Count < rhss2.Count) {
          rhss2.RemoveRange(lhss2.Count, rhss2.Count - lhss2.Count);
        } else {
          lhss2.RemoveRange(rhss2.Count, lhss2.Count - rhss2.Count);
        }
      }
    }
    // " temp, ... := MethodOrExpression, ...;"
    var up = new AssignStatement(Origin, lhss2, rhss2);
    if (expectExtract) {
      up.OriginalInitialLhs = Lhss.Count == 0 ? null : Lhss[0];
    }
    ResolvedStatements.Add(up);

    if (KeywordToken != null) {
      var keyword = KeywordToken.Token;
      var notFailureExpr = new UnaryOpExpr(keyword, UnaryOpExpr.Opcode.Not, resolver.VarDotMethod(Tok, temp, "IsFailure"));
      Statement ss = null;
      if (keyword.val == "expect") {
        // "expect !temp.IsFailure(), temp"
        ss = new ExpectStmt(new SourceOrigin(keyword.StartToken, EndToken), notFailureExpr, new IdentifierExpr(Tok, temp), KeywordToken.Attrs);
      } else if (keyword.val == "assume") {
        ss = new AssumeStmt(new SourceOrigin(keyword.StartToken, EndToken), notFailureExpr, SystemModuleManager.AxiomAttribute(KeywordToken.Attrs));
      } else if (keyword.val == "assert") {
        ss = new AssertStmt(new SourceOrigin(keyword.StartToken, EndToken), notFailureExpr, null, KeywordToken.Attrs);
      } else {
        Contract.Assert(false, $"Invalid token in :- statement: {keyword.val}");
      }
      ResolvedStatements.Add(ss);
    } else {
      var enclosingOutParameter = enclosingMethod.Outs[0];
      var ident = new IdentifierExpr(Tok, enclosingOutParameter.Name);
      // resolve it here to avoid capture into more closely declared local variables
      Contract.Assert(enclosingOutParameter.Type != null); // this confirms our belief that the out-parameter has already been resolved
      ident.Var = enclosingOutParameter;
      ident.Type = ident.Var.Type;

      ResolvedStatements.Add(
        // "if temp.IsFailure()"
        new IfStmt(Origin, false, resolver.VarDotMethod(Tok, temp, "IsFailure"),
          // THEN: { out := temp.PropagateFailure(); return; }
          new BlockStmt(Origin, new List<Statement>() {
            new AssignStatement(Origin,
              new List<Expression>() { ident },
              new List<AssignmentRhs>() { new ExprRhs(resolver.VarDotMethod(Tok, temp, "PropagateFailure")) }
            ),
            new ReturnStmt(Origin, null),
          }),
          // ELSE: no else block
          null
        ));
    }

    if (expectExtract) {
      // "y := temp.Extract();"
      var lhs = Lhss[0];
      ResolvedStatements.Add(
        new AssignStatement(Origin,
          new List<Expression>() { lhsExtract },
          new List<AssignmentRhs>() { new ExprRhs(resolver.VarDotMethod(Tok, temp, "Extract")) }
        ));
      // The following check is not necessary, because the ghost mismatch is caught later.
      // However the error message here is much clearer.
      var m = resolver.ResolveMember(Tok, firstType, "Extract", out _);
      if (m != null && m.IsGhost && !SingleAssignStmt.LhsIsToGhostOrAutoGhost(lhs)) {
        resolver.reporter.Error(MessageSource.Resolver, lhs.Tok,
          "The Extract member may not be ghost unless the initial LHS is ghost");
      }
    }
  }

  public override void ResolveGhostness(ModuleResolver resolver, ErrorReporter reporter, bool mustBeErasable,
    ICodeContext codeContext,
    string proofContext, bool allowAssumptionVariables, bool inConstructorInitializationPhase) {
    ResolvedStatements.ForEach(ss => ss.ResolveGhostness(resolver, reporter, mustBeErasable, codeContext,
      proofContext, allowAssumptionVariables, inConstructorInitializationPhase));
    IsGhost = ResolvedStatements.All(ss => ss.IsGhost);
  }
}
