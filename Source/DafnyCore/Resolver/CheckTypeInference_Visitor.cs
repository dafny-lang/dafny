using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

partial class Resolver {
  // ------------------------------------------------------------------------------------------------------
  // ----- CheckTypeInference -----------------------------------------------------------------------------
  // ------------------------------------------------------------------------------------------------------
  // The CheckTypeInference machinery visits every type in a given part of the AST (for example,
  // CheckTypeInference(Expression) does so for an Expression and CheckTypeInference_Member(MemberDecl)
  // does so for a MemberDecl) to make sure that all parts of types were fully inferred.
  #region CheckTypeInference
  private void CheckTypeInference_Member(MemberDecl member) {
    if (member is ConstantField) {
      var field = (ConstantField)member;
      if (field.Rhs != null) {
        CheckTypeInference(field.Rhs, new NoContext(member.EnclosingClass.EnclosingModuleDefinition));
      }
      CheckTypeInference(field.Type, new NoContext(member.EnclosingClass.EnclosingModuleDefinition), field.tok, "const");
    } else if (member is Method) {
      var m = (Method)member;
      foreach (var formal in m.Ins) {
        if (formal.DefaultValue != null) {
          CheckTypeInference(formal.DefaultValue, m);
        }
      }
      m.Req.Iter(mfe => CheckTypeInference_MaybeFreeExpression(mfe, m));
      m.Ens.Iter(mfe => CheckTypeInference_MaybeFreeExpression(mfe, m));
      CheckTypeInference_Specification_FrameExpr(m.Mod, m);
      CheckTypeInference_Specification_Expr(m.Decreases, m);
      if (m.Body != null) {
        CheckTypeInference(m.Body, m);
      }
    } else if (member is Function) {
      var f = (Function)member;
      foreach (var formal in f.Formals) {
        if (formal.DefaultValue != null) {
          CheckTypeInference(formal.DefaultValue, f);
        }
      }
      var errorCount = reporter.Count(ErrorLevel.Error);
      f.Req.Iter(e => CheckTypeInference(e.E, f));
      f.Ens.Iter(e => CheckTypeInference(e.E, f));
      f.Reads.Iter(fe => CheckTypeInference(fe.E, f));
      CheckTypeInference_Specification_Expr(f.Decreases, f);
      if (f.Body != null) {
        CheckTypeInference(f.Body, f);
      }
      if (errorCount == reporter.Count(ErrorLevel.Error)) {
        if (f is ExtremePredicate cop) {
          CheckTypeInference_Member(cop.PrefixPredicate);
        } else if (f.ByMethodDecl != null) {
          CheckTypeInference_Member(f.ByMethodDecl);
        }
      }
    }
  }

  private void CheckTypeInference_MaybeFreeExpression(AttributedExpression mfe, ICodeContext codeContext) {
    Contract.Requires(mfe != null);
    Contract.Requires(codeContext != null);
    foreach (var e in Attributes.SubExpressions(mfe.Attributes)) {
      CheckTypeInference(e, codeContext);
    }
    CheckTypeInference(mfe.E, codeContext);
  }
  private void CheckTypeInference_Specification_Expr(Specification<Expression> spec, ICodeContext codeContext) {
    Contract.Requires(spec != null);
    Contract.Requires(codeContext != null);
    foreach (var e in Attributes.SubExpressions(spec.Attributes)) {
      CheckTypeInference(e, codeContext);
    }
    spec.Expressions.Iter(e => CheckTypeInference(e, codeContext));
  }
  private void CheckTypeInference_Specification_FrameExpr(Specification<FrameExpression> spec, ICodeContext codeContext) {
    Contract.Requires(spec != null);
    Contract.Requires(codeContext != null);
    foreach (var e in Attributes.SubExpressions(spec.Attributes)) {
      CheckTypeInference(e, codeContext);
    }
    spec.Expressions.Iter(fe => CheckTypeInference(fe.E, codeContext));
  }
  void CheckTypeInference(Expression expr, ICodeContext codeContext) {
    Contract.Requires(expr != null);
    Contract.Requires(codeContext != null);
    PartiallySolveTypeConstraints(true);
    var c = new CheckTypeInference_Visitor(this, codeContext);
    c.Visit(expr);
  }
  void CheckTypeInference(Type type, ICodeContext codeContext, IToken tok, string what) {
    Contract.Requires(type != null);
    Contract.Requires(codeContext != null);
    Contract.Requires(tok != null);
    Contract.Requires(what != null);
    PartiallySolveTypeConstraints(true);
    var c = new CheckTypeInference_Visitor(this, codeContext);
    c.CheckTypeIsDetermined(tok, type, what);
  }
  void CheckTypeInference(Statement stmt, ICodeContext codeContext) {
    Contract.Requires(stmt != null);
    Contract.Requires(codeContext != null);
    PartiallySolveTypeConstraints(true);
    var c = new CheckTypeInference_Visitor(this, codeContext);
    c.Visit(stmt);
  }
  class CheckTypeInference_Visitor : ResolverBottomUpVisitor {
    readonly ICodeContext codeContext;
    public CheckTypeInference_Visitor(Resolver resolver, ICodeContext codeContext)
      : base(resolver) {
      Contract.Requires(resolver != null);
      Contract.Requires(codeContext != null);
      this.codeContext = codeContext;
    }

    protected override void VisitOneStmt(Statement stmt) {
      if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        foreach (var local in s.Locals) {
          CheckTypeIsDetermined(local.Tok, local.Type, "local variable");
          CheckTypeArgsContainNoOrdinal(local.Tok, local.type);
        }
      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        s.LocalVars.Iter(local => CheckTypeIsDetermined(local.Tok, local.Type, "local variable"));
        s.LocalVars.Iter(local => CheckTypeArgsContainNoOrdinal(local.Tok, local.Type));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        s.BoundVars.Iter(bv => CheckTypeIsDetermined(bv.tok, bv.Type, "bound variable"));
        s.BoundVars.Iter(bv => CheckTypeArgsContainNoOrdinal(bv.tok, bv.Type));

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          var what = lhs is IdentifierExpr ? string.Format("variable '{0}'", ((IdentifierExpr)lhs).Name) : "LHS";
          CheckTypeArgsContainNoOrdinal(lhs.tok, lhs.Type);
        }
      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        // The resolution of the calc statement builds up .Steps and .Result, which are of the form E0 OP E1, where
        // E0 and E1 are expressions from .Lines.  These additional expressions still need to have their .ResolvedOp
        // fields filled in, so we visit them (but not their subexpressions) here.
        foreach (var e in s.Steps) {
          Visit(e);
        }
        Visit(s.Result);
      }
    }

    protected override void VisitOneExpr(Expression expr) {
      if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e.Type.IsBitVectorType || e.Type.IsBigOrdinalType) {
          var n = (BigInteger)e.Value;
          var absN = n < 0 ? -n : n;
          // For bitvectors, check that the magnitude fits the width
          if (e.Type.IsBitVectorType && resolver.MaxBV(e.Type.AsBitVectorType.Width) < absN) {
            resolver.reporter.Error(MessageSource.Resolver, e.tok, "literal ({0}) is too large for the bitvector type {1}", absN, e.Type);
          }
          // For bitvectors and ORDINALs, check for a unary minus that, earlier, was mistaken for a negative literal
          // This can happen only in `match` patterns (see comment by LitPattern.OptimisticallyDesugaredLit).
          if (n < 0 || e.tok.val == "-0") {
            Contract.Assert(e.tok.val == "-0");  // this and the "if" above tests that "n < 0" happens only when the token is "-0"
            resolver.reporter.Error(MessageSource.Resolver, e.tok, "unary minus (-{0}, type {1}) not allowed in case pattern", absN, e.Type);
          }
        }

        if (expr is StaticReceiverExpr stexpr) {
          if (stexpr.ObjectToDiscard != null) {
            Visit(stexpr.ObjectToDiscard);
          } else {
            foreach (Type t in stexpr.Type.TypeArgs) {
              if (t is InferredTypeProxy && ((InferredTypeProxy)t).T == null) {
                resolver.reporter.Error(MessageSource.Resolver, stexpr.tok, "type of type parameter could not be determined; please specify the type explicitly");
              }
            }
          }
        }

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        foreach (var bv in e.BoundVars) {
          if (!IsDetermined(bv.Type.Normalize())) {
            resolver.reporter.Error(MessageSource.Resolver, bv.tok, "type of bound variable '{0}' could not be determined; please specify the type explicitly", bv.Name);
          } else if (codeContext is ExtremePredicate) {
            CheckContainsNoOrdinal(bv.tok, bv.Type, string.Format("type of bound variable '{0}' ('{1}') is not allowed to use type ORDINAL", bv.Name, bv.Type));
          }
        }

        if (e is ExistsExpr && e.Range == null) {
          var binBody = ((ExistsExpr)e).Term as BinaryExpr;
          if (binBody != null && binBody.Op == BinaryExpr.Opcode.Imp) {  // check Op, not ResolvedOp, in order to distinguish ==> and <==
                                                                         // apply the wisdom of Claude Marche: issue a warning here
            resolver.reporter.Warning(MessageSource.Resolver, e.tok,
              "the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; " +
              "if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning");
          }
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member is Function || e.Member is Method) {
          var i = 0;
          foreach (var p in Util.Concat(e.TypeApplication_AtEnclosingClass, e.TypeApplication_JustMember)) {
            var tp = i < e.TypeApplication_AtEnclosingClass.Count ? e.Member.EnclosingClass.TypeArgs[i] : ((ICallable)e.Member).TypeArgs[i - e.TypeApplication_AtEnclosingClass.Count];
            if (!IsDetermined(p.Normalize())) {
              resolver.reporter.Error(MessageSource.Resolver, e.tok, "type parameter '{0}' (inferred to be '{1}') to the {2} '{3}' could not be determined", tp.Name, p, e.Member.WhatKind, e.Member.Name);
            } else {
              CheckContainsNoOrdinal(e.tok, p, string.Format("type parameter '{0}' (passed in as '{1}') to the {2} '{3}' is not allowed to use ORDINAL", tp.Name, p, e.Member.WhatKind, e.Member.Name));
            }
            i++;
          }
        }
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var i = 0;
        foreach (var p in Util.Concat(e.TypeApplication_AtEnclosingClass, e.TypeApplication_JustFunction)) {
          var tp = i < e.TypeApplication_AtEnclosingClass.Count ? e.Function.EnclosingClass.TypeArgs[i] : e.Function.TypeArgs[i - e.TypeApplication_AtEnclosingClass.Count];
          if (!IsDetermined(p.Normalize())) {
            resolver.reporter.Error(MessageSource.Resolver, e.tok, "type parameter '{0}' (inferred to be '{1}') in the function call to '{2}' could not be determined{3}", tp.Name, p, e.Name,
              (e.Name.StartsWith("reveal_"))
              ? ". If you are making an opaque function, make sure that the function can be called."
              : ""
            );
          } else {
            CheckContainsNoOrdinal(e.tok, p, string.Format("type parameter '{0}' (passed in as '{1}') to function call '{2}' is not allowed to use ORDINAL", tp.Name, p, e.Name));
          }
          i++;
        }
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var p in e.LHSs) {
          foreach (var x in p.Vars) {
            if (!IsDetermined(x.Type.Normalize())) {
              resolver.reporter.Error(MessageSource.Resolver, x.tok, "the type of the bound variable '{0}' could not be determined", x.Name);
            } else {
              CheckTypeArgsContainNoOrdinal(x.tok, x.Type);
            }
          }
        }
      } else if (expr is IdentifierExpr) {
        // by specializing for IdentifierExpr, error messages will be clearer
        CheckTypeIsDetermined(expr.tok, expr.Type, "variable");
      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        if (e.ToType.IsRefType) {
          var fromType = e.E.Type;
          Contract.Assert(fromType.IsRefType);
          if (fromType.IsSubtypeOf(e.ToType, false, true) || e.ToType.IsSubtypeOf(fromType, false, true)) {
            // looks good
          } else {
            resolver.reporter.Error(MessageSource.Resolver, e.tok,
              "a type cast to a reference type ({0}) must be from a compatible type (got {1}); this cast could never succeed", e.ToType, fromType);
          }
        }
      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        var fromType = e.E.Type;
        if (fromType.IsSubtypeOf(e.ToType, false, true)) {
          // This test is allowed and it always returns true
        } else if (!e.ToType.IsSubtypeOf(fromType, false, true)) {
          resolver.reporter.Error(MessageSource.Resolver, e.tok,
            "a type test to '{0}' must be from a compatible type (got '{1}')", e.ToType, fromType);
        } else if (!e.ToType.IsRefType) {
          resolver.reporter.Error(MessageSource.Resolver, e.tok,
            "a non-trivial type test is allowed only for reference types (tried to test if '{1}' is a '{0}')", e.ToType, fromType);
        }
      } else if (CheckTypeIsDetermined(expr.tok, expr.Type, "expression")) {
        if (expr is UnaryOpExpr uop) {
          // The CheckTypeInference_Visitor has already visited uop.E, but uop.E's may be undetermined. If that happened,
          // then an error has already been reported.
          if (CheckTypeIsDetermined(uop.E.tok, uop.E.Type, "expression")) {
            uop.ResolveOp(); // Force resolution eagerly at this point to catch potential bugs
          }
        } else if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          e.ResolvedOp = ResolveOp(e.Op, e.E0.Type, e.E1.Type);
          // Check for useless comparisons with "null"
          Expression other = null;  // if "null" if one of the operands, then "other" is the other
          if (e.E0 is LiteralExpr && ((LiteralExpr)e.E0).Value == null) {
            other = e.E1;
          } else if (e.E1 is LiteralExpr && ((LiteralExpr)e.E1).Value == null) {
            other = e.E0;
          }
          if (other != null) {
            bool sense = true;
            switch (e.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                sense = false;
                goto case BinaryExpr.ResolvedOpcode.EqCommon;
              case BinaryExpr.ResolvedOpcode.EqCommon: {
                  var nntUdf = other.Type.AsNonNullRefType;
                  if (nntUdf != null) {
                    string name = null;
                    string hint = "";
                    other = other.Resolved;
                    if (other is IdentifierExpr) {
                      name = string.Format("variable '{0}'", ((IdentifierExpr)other).Name);
                    } else if (other is MemberSelectExpr) {
                      var field = ((MemberSelectExpr)other).Member as Field;
                      // The type of the field may be a formal type parameter, in which case the hint is omitted
                      if (field.Type.IsNonNullRefType) {
                        name = string.Format("field '{0}'", field.Name);
                      }
                    }
                    if (name != null) {
                      // The following relies on that a NonNullTypeDecl has a .Rhs that is a
                      // UserDefinedType denoting the possibly null type declaration and that
                      // these two types have the same number of type arguments.
                      var nonNullTypeDecl = (NonNullTypeDecl)nntUdf.ResolvedClass;
                      var possiblyNullUdf = (UserDefinedType)nonNullTypeDecl.Rhs;
                      var possiblyNullTypeDecl = (ClassDecl)possiblyNullUdf.ResolvedClass;
                      Contract.Assert(nonNullTypeDecl.TypeArgs.Count == possiblyNullTypeDecl.TypeArgs.Count);
                      Contract.Assert(nonNullTypeDecl.TypeArgs.Count == nntUdf.TypeArgs.Count);
                      var ty = new UserDefinedType(nntUdf.tok, possiblyNullUdf.Name, possiblyNullTypeDecl, nntUdf.TypeArgs);

                      hint = string.Format(" (to make it possible for {0} to have the value 'null', declare its type to be '{1}')", name, ty);
                    }
                    resolver.reporter.Warning(MessageSource.Resolver, e.tok,
                      string.Format("the type of the other operand is a non-null type, so this comparison with 'null' will always return '{0}'{1}",
                      sense ? "false" : "true", hint));
                  }
                  break;
                }
              case BinaryExpr.ResolvedOpcode.NotInSet:
              case BinaryExpr.ResolvedOpcode.NotInSeq:
              case BinaryExpr.ResolvedOpcode.NotInMultiSet:
                sense = false;
                goto case BinaryExpr.ResolvedOpcode.InSet;
              case BinaryExpr.ResolvedOpcode.InSet:
              case BinaryExpr.ResolvedOpcode.InSeq:
              case BinaryExpr.ResolvedOpcode.InMultiSet: {
                  var ty = other.Type.NormalizeExpand();
                  var what = ty is SetType ? "set" : ty is SeqType ? "seq" : "multiset";
                  if (((CollectionType)ty).Arg.IsNonNullRefType) {
                    resolver.reporter.Warning(MessageSource.Resolver, e.tok,
                      string.Format("the type of the other operand is a {0} of non-null elements, so the {1}inclusion test of 'null' will always return '{2}'",
                      what, sense ? "" : "non-", sense ? "false" : "true"));
                  }
                  break;
                }
              case BinaryExpr.ResolvedOpcode.NotInMap:
                goto case BinaryExpr.ResolvedOpcode.InMap;
              case BinaryExpr.ResolvedOpcode.InMap: {
                  var ty = other.Type.NormalizeExpand();
                  if (((MapType)ty).Domain.IsNonNullRefType) {
                    resolver.reporter.Warning(MessageSource.Resolver, e.tok,
                      string.Format("the type of the other operand is a map to a non-null type, so the inclusion test of 'null' will always return '{0}'",
                      sense ? "false" : "true"));
                  }
                  break;
                }
              default:
                break;
            }
          }
        } else if (expr is NegationExpression) {
          var e = (NegationExpression)expr;
          Expression resolved = null;
          if (e.E is LiteralExpr lit) { // note, not e.E.Resolved, since we don't want to do this for double negations
                                        // For real-based types, integer-based types, and bi (but not bitvectors), "-" followed by a literal is just a literal expression with a negative value
            if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
              var d = (BaseTypes.BigDec)lit.Value;
              Contract.Assert(!d.IsNegative);
              resolved = new LiteralExpr(e.tok, -d);
            } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
              var n = (BigInteger)lit.Value;
              Contract.Assert(0 <= n);
              resolved = new LiteralExpr(e.tok, -n);
            }
          }
          if (resolved == null) {
            // Treat all other expressions "-e" as "0 - e"
            Expression zero;
            if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
              zero = new LiteralExpr(e.tok, BaseTypes.BigDec.ZERO);
            } else {
              Contract.Assert(e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType);
              zero = new LiteralExpr(e.tok, 0);
            }
            zero.Type = expr.Type;
            resolved = new BinaryExpr(e.tok, BinaryExpr.Opcode.Sub, zero, e.E) { ResolvedOp = BinaryExpr.ResolvedOpcode.Sub };
          }
          resolved.Type = expr.Type;
          e.ResolvedExpression = resolved;
        }
      }
    }
    public static bool IsDetermined(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);
      // all other proxies indicate the type has not yet been determined, provided their type parameters have been
      return !(t is TypeProxy) && t.TypeArgs.All(tt => IsDetermined(tt.Normalize()));
    }
    ISet<TypeProxy> UnderspecifiedTypeProxies = new HashSet<TypeProxy>();
    public bool CheckTypeIsDetermined(IToken tok, Type t, string what) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      Contract.Requires(what != null);
      t = t.NormalizeExpand();

      if (t is TypeProxy) {
        var proxy = (TypeProxy)t;
        if (!UnderspecifiedTypeProxies.Contains(proxy)) {
          // report an error for this TypeProxy only once
          resolver.reporter.Error(MessageSource.Resolver, tok, "the type of this {0} is underspecified", what);
          UnderspecifiedTypeProxies.Add(proxy);
        }
        return false;
      }
      // Recurse on type arguments:
      return t.TypeArgs.All(rg => CheckTypeIsDetermined(tok, rg, what));
    }
    public void CheckTypeArgsContainNoOrdinal(IToken tok, Type t) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      t = t.NormalizeExpand();
      t.TypeArgs.Iter(rg => CheckContainsNoOrdinal(tok, rg, "an ORDINAL type is not allowed to be used as a type argument"));
    }
    public void CheckContainsNoOrdinal(IToken tok, Type t, string errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      Contract.Requires(errMsg != null);
      t = t.NormalizeExpand();
      if (t.IsBigOrdinalType) {
        resolver.reporter.Error(MessageSource.Resolver, tok, errMsg);
      }
      t.TypeArgs.Iter(rg => CheckContainsNoOrdinal(tok, rg, errMsg));
    }
  }
  #endregion CheckTypeInference
}