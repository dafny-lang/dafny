using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.Boogie;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny;

partial class Resolver {
  class TypeInferenceCheckingContext : IASTVisitorContext {
    private readonly IASTVisitorContext astVisitorContext;

    public bool IsPrefixPredicate => astVisitorContext is PrefixPredicate;
    public bool IsExtremePredicate => astVisitorContext is ExtremePredicate;
    public bool IsPrefixDeclaration => astVisitorContext is PrefixPredicate or PrefixLemma;

    public TypeInferenceCheckingContext(IASTVisitorContext astVisitorContext) {
      this.astVisitorContext = astVisitorContext;
    }

    ModuleDefinition IASTVisitorContext.EnclosingModule => astVisitorContext.EnclosingModule;
  }

  class CheckTypeInferenceVisitor : ASTVisitor<TypeInferenceCheckingContext> {
    private readonly Resolver resolver;
    private ErrorReporter reporter => resolver.reporter;

    public CheckTypeInferenceVisitor(Resolver resolver) {
      this.resolver = resolver;
    }

    public override TypeInferenceCheckingContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
      return new TypeInferenceCheckingContext(astVisitorContext);
    }

    protected override void VisitOneDeclaration(TopLevelDecl decl) {
      if (decl is NewtypeDecl newtypeDecl) {
        if (newtypeDecl.Var != null) {
          if (!IsDetermined(newtypeDecl.BaseType.NormalizeExpand())) {
            reporter.Error(MessageSource.Resolver, newtypeDecl.tok, "newtype's base type is not fully determined; add an explicit type for '{0}'",
              newtypeDecl.Var.Name);
          }
        }

      } else if (decl is SubsetTypeDecl subsetTypeDecl) {
        if (!IsDetermined(subsetTypeDecl.Rhs.NormalizeExpand())) {
          reporter.Error(MessageSource.Resolver, subsetTypeDecl.tok,
            "subset type's base type is not fully determined; add an explicit type for '{0}'", subsetTypeDecl.Var.Name);
        }

      } else if (decl is DatatypeDecl datatypeDecl) {
        foreach (var member in resolver.classMembers[datatypeDecl].Values) {
          if (member is DatatypeDestructor dtor) {
            var rolemodel = dtor.CorrespondingFormals[0];
            for (var i = 1; i < dtor.CorrespondingFormals.Count; i++) {
              var other = dtor.CorrespondingFormals[i];
              if (!Type.Equal_Improved(rolemodel.Type, other.Type)) {
                reporter.Error(MessageSource.Resolver, other,
                  "shared destructors must have the same type, but '{0}' has type '{1}' in constructor '{2}' and type '{3}' in constructor '{4}'",
                  rolemodel.Name, rolemodel.Type, dtor.EnclosingCtors[0].Name, other.Type, dtor.EnclosingCtors[i].Name);
              }
            }
          }
        }
      }

      base.VisitOneDeclaration(decl);
    }

    public override void VisitField(Field field) {
      if (field is ConstantField constantField) {
        resolver.PartiallySolveTypeConstraints(true);
        CheckTypeIsDetermined(field.tok, field.Type, "const");
      }

      base.VisitField(field);
    }

    protected override bool VisitOneStatement(Statement stmt, TypeInferenceCheckingContext context) {
      if (stmt is CalcStmt calcStmt) {
        // The resolution of the calc statement builds up .Steps and .Result, which are of the form E0 OP E1, where
        // E0 and E1 are expressions from .Lines.  These additional expressions still need to have their .ResolvedOp
        // fields filled in, so we visit them, rather than just the parsed .Lines.
        Attributes.SubExpressions(calcStmt.Attributes).Iter(e => VisitExpression(e, context));
        calcStmt.Steps.Iter(e => VisitExpression(e, context));
        VisitExpression(calcStmt.Result, context);
        calcStmt.Hints.Iter(hint => VisitStatement(hint, context));
        return false; // we're done with all subcomponents of the CalcStmt
      }

      return base.VisitOneStatement(stmt, context);
    }

    protected override void PostVisitOneStatement(Statement stmt, TypeInferenceCheckingContext context) {
      if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        foreach (var local in s.Locals) {
          CheckTypeIsDetermined(local.Tok, local.Type, "local variable");
          CheckTypeArgsContainNoOrdinal(local.Tok, local.type, context);
        }
      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        s.LocalVars.Iter(local => CheckTypeIsDetermined(local.Tok, local.Type, "local variable"));
        s.LocalVars.Iter(local => CheckTypeArgsContainNoOrdinal(local.Tok, local.Type, context));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        s.BoundVars.Iter(bv => CheckTypeIsDetermined(bv.tok, bv.Type, "bound variable"));
        s.BoundVars.Iter(bv => CheckTypeArgsContainNoOrdinal(bv.tok, bv.Type, context));

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        foreach (var lhs in s.Lhss) {
          var what = lhs is IdentifierExpr ? $"variable '{((IdentifierExpr)lhs).Name}'" : "LHS";
          CheckTypeArgsContainNoOrdinal(lhs.tok, lhs.Type, context);
        }
      }

      base.PostVisitOneStatement(stmt, context);
    }

    protected override void PostVisitOneExpression(Expression expr, TypeInferenceCheckingContext context) {
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
            VisitExpression(stexpr.ObjectToDiscard, context);
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
            resolver.reporter.Error(MessageSource.Resolver, bv.tok,
              $"type of bound variable '{bv.Name}' could not be determined; please specify the type explicitly");
          } else if (context.IsExtremePredicate) {
            CheckContainsNoOrdinal(bv.tok, bv.Type, $"type of bound variable '{bv.Name}' ('{bv.Type}') is not allowed to use type ORDINAL");
          }
        }

        if (e is ExistsExpr && e.Range == null) {
          var binBody = ((ExistsExpr)e).Term as BinaryExpr;
          if (binBody != null && binBody.Op == BinaryExpr.Opcode.Imp) {  // check Op, not ResolvedOp, in order to distinguish ==> and <==
                                                                         // apply the wisdom of Claude Marche: issue a warning here
            resolver.reporter.Warning(MessageSource.Resolver, ErrorID.None, e.tok,
              "the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; " +
              "if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning");
          }
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member is Function || e.Member is Method) {
          var i = 0;
          foreach (var p in Util.Concat(e.TypeApplication_AtEnclosingClass, e.TypeApplication_JustMember)) {
            var tp = i < e.TypeApplication_AtEnclosingClass.Count
              ? e.Member.EnclosingClass.TypeArgs[i]
              : ((ICallable)e.Member).TypeArgs[i - e.TypeApplication_AtEnclosingClass.Count];
            if (!IsDetermined(p.Normalize())) {
              resolver.reporter.Error(MessageSource.Resolver, e.tok,
                $"type parameter '{tp.Name}' (inferred to be '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' could not be determined");
            } else if (!context.IsPrefixPredicate) { // this check is done in extreme predicates, so no need to repeat it here for prefix predicates
              CheckContainsNoOrdinal(e.tok, p,
                $"type parameter '{tp.Name}' (passed in as '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' is not allowed to use ORDINAL");
            }
            i++;
          }
        }
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var i = 0;
        foreach (var p in Util.Concat(e.TypeApplication_AtEnclosingClass, e.TypeApplication_JustFunction)) {
          var tp = i < e.TypeApplication_AtEnclosingClass.Count
            ? e.Function.EnclosingClass.TypeArgs[i]
            : e.Function.TypeArgs[i - e.TypeApplication_AtEnclosingClass.Count];
          if (!IsDetermined(p.Normalize())) {
            var hint = e.Name.StartsWith("reveal_")
              ? ". If you are making an opaque function, make sure that the function can be called."
              : "";
            resolver.reporter.Error(MessageSource.Resolver, e.tok,
              $"type parameter '{tp.Name}' (inferred to be '{p}') in the function call to '{e.Name}' could not be determined{hint}");
          } else if (!context.IsPrefixPredicate) { // this check is done in extreme predicates, so no need to repeat it here for prefix predicates
            CheckContainsNoOrdinal(e.tok, p,
              $"type parameter '{tp.Name}' (passed in as '{p}') to function call '{e.Name}' is not allowed to use ORDINAL");
          }
          i++;
        }
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var p in e.LHSs) {
          foreach (var x in p.Vars) {
            if (!IsDetermined(x.Type.Normalize())) {
              resolver.reporter.Error(MessageSource.Resolver, x.tok, $"the type of the bound variable '{x.Name}' could not be determined");
            } else {
              CheckTypeArgsContainNoOrdinal(x.tok, x.Type, context);
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
              "a type cast to a reference type ({0}) must be from a compatible type (got {1}); this cast could never succeed",
              e.ToType, fromType);
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
                      name = $"variable '{((IdentifierExpr)other).Name}'";
                    } else if (other is MemberSelectExpr) {
                      var field = ((MemberSelectExpr)other).Member as Field;
                      // The type of the field may be a formal type parameter, in which case the hint is omitted
                      if (field.Type.IsNonNullRefType) {
                        name = $"field '{field.Name}'";
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

                      hint = $" (to make it possible for {name} to have the value 'null', declare its type to be '{ty}')";
                    }
                    var b = sense ? "false" : "true";
                    resolver.reporter.Warning(MessageSource.Resolver, ErrorID.None, e.tok,
                      $"the type of the other operand is a non-null type, so this comparison with 'null' will always return '{b}'{hint}");
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
                    var non = sense ? "" : "non-";
                    var b = sense ? "false" : "true";
                    resolver.reporter.Warning(MessageSource.Resolver, ErrorID.None, e.tok,
                      $"the type of the other operand is a {what} of non-null elements, so the {non}inclusion test of 'null' will always return '{b}'");
                  }
                  break;
                }
              case BinaryExpr.ResolvedOpcode.NotInMap:
                goto case BinaryExpr.ResolvedOpcode.InMap;
              case BinaryExpr.ResolvedOpcode.InMap: {
                  var ty = other.Type.NormalizeExpand();
                  if (((MapType)ty).Domain.IsNonNullRefType) {
                    var b = sense ? "false" : "true";
                    resolver.reporter.Warning(MessageSource.Resolver, ErrorID.None, e.tok,
                      $"the type of the other operand is a map to a non-null type, so the inclusion test of 'null' will always return '{b}'");
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
                                        // For real-based types, integer-based types, and bi (but not bitvectors), "-" followed by a literal is
                                        // just a literal expression with a negative value
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

      base.PostVisitOneExpression(expr, context);
    }

    public static bool IsDetermined(Type t) {
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);
      // all other proxies indicate the type has not yet been determined, provided their type parameters have been
      return !(t is TypeProxy) && t.TypeArgs.All(tt => IsDetermined(tt.Normalize()));
    }

    readonly ISet<TypeProxy> UnderspecifiedTypeProxies = new HashSet<TypeProxy>();

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

    public void CheckTypeArgsContainNoOrdinal(IToken tok, Type t, TypeInferenceCheckingContext context) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      if (context.IsPrefixDeclaration) {
        // User-provided expressions in extreme predicates/lemmas are checked in the extreme declarations, so need
        // need to do them here again for the prefix predicates/lemmas.
      } else {
        t = t.NormalizeExpand();
        t.TypeArgs.Iter(rg => CheckContainsNoOrdinal(tok, rg, "an ORDINAL type is not allowed to be used as a type argument"));
      }
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
}
