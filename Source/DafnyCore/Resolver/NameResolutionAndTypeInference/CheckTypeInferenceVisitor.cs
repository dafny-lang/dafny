//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.BaseTypes;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

class CheckTypeInferenceVisitor : ASTVisitor<TypeInferenceCheckingContext> {
  private readonly ModuleResolver resolver;

  public CheckTypeInferenceVisitor(ModuleResolver resolver) {
    this.resolver = resolver;
  }

  public override TypeInferenceCheckingContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return new TypeInferenceCheckingContext(astVisitorContext);
  }

  protected override void VisitOneDeclaration(TopLevelDecl decl) {
    if (decl is NewtypeDecl newtypeDecl) {
      if (newtypeDecl.Var != null) {
        if (!IsDetermined(newtypeDecl.BaseType.NormalizeExpand())) {
          resolver.ReportError(ResolutionErrors.ErrorId.r_newtype_base_undetermined, newtypeDecl.Origin,
            $"base type of {newtypeDecl.WhatKindAndName} is not fully determined; add an explicit type for bound variable '{newtypeDecl.Var.Name}'");
        }
      }

    } else if (decl is SubsetTypeDecl subsetTypeDecl) {
      if (!IsDetermined(subsetTypeDecl.Rhs.NormalizeExpand())) {
        resolver.ReportError(ResolutionErrors.ErrorId.r_subset_type_base_undetermined, subsetTypeDecl.Origin,
          $"base type of {subsetTypeDecl.WhatKindAndName} is not fully determined; add an explicit type for bound variable '{subsetTypeDecl.Var.Name}'");
      }

    } else if (decl is DatatypeDecl datatypeDecl) {
      foreach (var member in resolver.GetClassMembers(datatypeDecl).Values) {
        if (member is DatatypeDestructor dtor) {
          var rolemodel = dtor.CorrespondingFormals[0];
          for (var i = 1; i < dtor.CorrespondingFormals.Count; i++) {
            var other = dtor.CorrespondingFormals[i];
            if (!Type.Equal_Improved(rolemodel.Type, other.Type)) {
              resolver.ReportError(ResolutionErrors.ErrorId.r_shared_destructors_have_different_types, other,
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
      CheckTypeIsDetermined(field.Origin, field.Type, "const");
    }

    base.VisitField(field);
  }

  protected override bool VisitOneStatement(Statement stmt, TypeInferenceCheckingContext context) {
    if (stmt is CalcStmt calcStmt) {
      // The resolution of the calc statement builds up .Steps and .Result, which are of the form E0 OP E1, where
      // E0 and E1 are expressions from .Lines.  These additional expressions still need to have their .ResolvedOp
      // fields filled in, so we visit them, rather than just the parsed .Lines.
      Attributes.SubExpressions(calcStmt.Attributes).ForEach(e => VisitExpression(e, context));
      calcStmt.Steps.ForEach(e => VisitExpression(e, context));
      VisitExpression(calcStmt.Result, context);
      calcStmt.Hints.ForEach(hint => VisitStatement(hint, context));
      return false; // we're done with all subcomponents of the CalcStmt
    }

    return base.VisitOneStatement(stmt, context);
  }

  protected override void PostVisitOneStatement(Statement stmt, TypeInferenceCheckingContext context) {
    if (stmt is VarDeclStmt) {
      var s = (VarDeclStmt)stmt;
      foreach (var local in s.Locals) {
        CheckTypeIsDetermined(local.Origin, local.Type, "local variable");
        CheckTypeArgsContainNoOrdinal(local.Origin, local.type, context);
      }
    } else if (stmt is VarDeclPattern) {
      var s = (VarDeclPattern)stmt;
      s.LocalVars.ForEach(local => CheckTypeIsDetermined(local.Origin, local.Type, "local variable"));
      s.LocalVars.ForEach(local => CheckTypeArgsContainNoOrdinal(local.Origin, local.Type, context));

    } else if (stmt is ForallStmt) {
      var s = (ForallStmt)stmt;
      s.BoundVars.ForEach(bv => CheckTypeIsDetermined(bv.Origin, bv.Type, "bound variable"));
      s.BoundVars.ForEach(bv => CheckTypeArgsContainNoOrdinal(bv.Origin, bv.Type, context));

    } else if (stmt is AssignSuchThatStmt) {
      var s = (AssignSuchThatStmt)stmt;
      foreach (var lhs in s.Lhss) {
        CheckTypeArgsContainNoOrdinal(lhs.Origin, lhs.Type, context);
      }
    }

    base.PostVisitOneStatement(stmt, context);
  }

  protected override void PostVisitOneExpression(Expression expr, TypeInferenceCheckingContext context) {
    // Handle NegationExpression first, as ApproximateExpr may depend on it
    if (expr is NegationExpression) {
      var e = (NegationExpression)expr;
      Expression resolved = null;
      if (e.E is LiteralExpr lit) { // note, not e.E.Resolved, since we don't want to do this for double negations
        // For real-based types, float types, integer-based types, and bi (but not bitvectors), "-" followed by a literal is
        // just a literal expression with a negative value
        if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          var d = (BigDec)lit.Value;
          Contract.Assert(!d.IsNegative);
          resolved = new LiteralExpr(e.Origin, -d);
        } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Float)) {
          var d = (BigDec)lit.Value;
          Contract.Assert(!d.IsNegative);
          var (significandBits, exponentBits) = e.E.Type.FloatPrecision;

          if (d.IsZero) {
            resolved = new DecimalLiteralExpr(e.Origin, BigDec.ZERO) {
              Type = e.E.Type,
              ResolvedFloatValue = BigFloat.CreateZero(true, significandBits, exponentBits)
            };
          } else {
            BigFloat negatedFloat;
            if (lit is DecimalLiteralExpr decLit && decLit.ResolvedFloatValue != null) {
              negatedFloat = -decLit.ResolvedFloatValue.Value;
            } else {
              negatedFloat = FloatLiteralValidator.ComputeNegatedFloat(d, significandBits, exponentBits);
            }
            var negatedLit = new DecimalLiteralExpr(e.Origin, -d) {
              Type = e.Type,
              ResolvedFloatValue = negatedFloat
            };
            // Preserve IsApproximate flag from original literal
            if (lit is DecimalLiteralExpr origDecLit) {
              negatedLit.IsApproximate = origDecLit.IsApproximate;
            }
            resolved = negatedLit;
          }
        } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          var n = (BigInteger)lit.Value;
          Contract.Assert(0 <= n);
          resolved = new LiteralExpr(e.Origin, -n);
        }
      }
      if (resolved == null) {
        // For floating-point types, use UnaryOpExpr with Negate opcode for IEEE 754 compliance
        if (e.E.Type.IsFloatingPointType) {
          resolved = new UnaryOpExpr(e.Origin, UnaryOpExpr.Opcode.Negate, e.E);
        } else {
          // Treat all other expressions "-e" as "0 - e"
          Expression zero;
          if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
            zero = new LiteralExpr(e.Origin, BaseTypes.BigDec.ZERO);
          } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Float)) {
            zero = new DecimalLiteralExpr(e.Origin, BaseTypes.BigDec.ZERO);
          } else {
            Contract.Assert(e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.NormalizeToAncestorType().IsBitVectorType);
            zero = new LiteralExpr(e.Origin, 0);
          }
          zero.Type = expr.Type;
          resolved = new BinaryExpr(e.Origin, BinaryExpr.Opcode.Sub, zero, e.E) {
            ResolvedOp = BinaryExpr.ResolvedOpcode.Sub
          };
        }
      }
      resolved.Type = expr.Type;
      e.ResolvedExpression = resolved;
    } else if (expr is ApproximateExpr) {
      var e = (ApproximateExpr)expr;
      if (e.Expr is NegationExpression { ResolvedExpression: not null } neg) {
        e.ResolvedExpression = neg.ResolvedExpression;
      } else {
        e.ResolvedExpression ??= e.Expr;
      }

      // Validate and set ResolvedFloatValue for float literals
      Expression toCheck = e.ResolvedExpression ?? e.Expr;
      if (toCheck is DecimalLiteralExpr decLit) {
        var resolvedType = e.Type.Normalize();

        if (resolvedType.IsFloatingPointType) {
          var decValue = (BigDec)decLit.Value;
          var (significandBits, exponentBits) = resolvedType.FloatPrecision;
          var (isExact, floatValue) = FloatLiteralValidator.ValidateAndCompute(decValue, significandBits, exponentBits);

          decLit.ResolvedFloatValue = floatValue;
        }
      }
    } else if (expr is LiteralExpr) {
      var e = (LiteralExpr)expr;
      if (e.Type.IsBitVectorType || e.Type.IsBigOrdinalType) {
        var n = (BigInteger)e.Value;
        var absN = n < 0 ? -n : n;
        // For bitvectors, check that the magnitude fits the width
        if (e.Type.IsBitVectorType && ConstantFolder.MaxBv(e.Type.AsBitVectorType.Width) < absN) {
          resolver.ReportError(ResolutionErrors.ErrorId.r_literal_too_large_for_bitvector, e.Origin, "literal ({0}) is too large for the bitvector type {1}", absN, e.Type);
        }
        // For bitvectors and ORDINALs, check for a unary minus that, earlier, was mistaken for a negative literal
        // This can happen only in `match` patterns (see comment by LitPattern.OptimisticallyDesugaredLit).
        if (n < 0 || e.Origin.val == "-0") {
          Contract.Assert(e.Origin.val == "-0");  // this and the "if" above tests that "n < 0" happens only when the token is "-0"
          resolver.ReportError(ResolutionErrors.ErrorId.r_no_unary_minus_in_case_patterns, e.Origin, "unary minus (-{0}, type {1}) not allowed in case pattern", absN, e.Type);
        }
      }

      if (e is DecimalLiteralExpr decimalLiteral && e.Value is BigDec decValue) {
        var normalizedType = e.Type.Normalize();

        if (!normalizedType.IsFloatingPointType) {
          return;
        }

        if (decimalLiteral.IsApproximate) {
          var (significandBits, exponentBits) = normalizedType.FloatPrecision;
          var (isExact, _) = FloatLiteralValidator.ValidateAndCompute(decValue, significandBits, exponentBits);
          if (isExact) {
            var typeName = normalizedType.FloatTypeName;
            resolver.ReportError(ResolutionErrors.ErrorId.r_inexact_fp64_literal_without_prefix, e.Origin,
              $"The approximate literal prefix ~ is not allowed on value {decValue} which is exactly representable as {typeName}. Remove the ~ prefix.");
          }
          return;
        }

        // Compute float value if not yet computed, or if type precision changed during inference
        bool wasNull = decimalLiteral.ResolvedFloatValue == null;
        bool needsRecompute = wasNull;
        if (!needsRecompute) {
          var (currentMantissa, currentExponent) = normalizedType.FloatPrecision;
          var storedValue = decimalLiteral.ResolvedFloatValue.Value;
          needsRecompute = currentMantissa != storedValue.SignificandSize || currentExponent != storedValue.ExponentSize;
        }

        if (needsRecompute) {
          var (significandBits, exponentBits) = normalizedType.FloatPrecision;
          var (isExact, floatValue) = FloatLiteralValidator.ValidateAndCompute(decValue, significandBits, exponentBits);
          decimalLiteral.ResolvedFloatValue = floatValue;
          // Report inexact error only on first computation (not on type precision changes)
          if (!isExact && wasNull) {
            var typeName = normalizedType.FloatTypeName;
            resolver.ReportError(ResolutionErrors.ErrorId.r_inexact_fp64_literal_without_prefix, e.Origin,
              $"The literal {decValue} is not exactly representable as an {typeName} value. " +
              $"Use the approximate literal syntax ~{decValue} to explicitly acknowledge rounding.");
          }
        }
      }

      if (expr is StaticReceiverExpr stexpr) {
        foreach (Type t in stexpr.Type.TypeArgs) {
          if (t is InferredTypeProxy && ((InferredTypeProxy)t).T == null) {
            resolver.ReportError(ResolutionErrors.ErrorId.r_type_parameter_undetermined, stexpr.Origin, "type of type parameter could not be determined; please specify the type explicitly");
          }
        }
      }

    } else if (expr is ComprehensionExpr) {
      var e = (ComprehensionExpr)expr;
      foreach (var bv in e.BoundVars) {
        if (!IsDetermined(bv.Type.Normalize())) {
          resolver.ReportError(ResolutionErrors.ErrorId.r_bound_variable_undetermined, bv.Origin,
            $"type of bound variable '{bv.Name}' could not be determined; please specify the type explicitly");
        } else if (context.IsExtremePredicate) {
          CheckContainsNoOrdinal(ResolutionErrors.ErrorId.r_bound_variable_may_not_be_ORDINAL, bv.Origin, bv.Type, $"type of bound variable '{bv.Name}' ('{bv.Type}') is not allowed to use type ORDINAL");
        }
      }

      if (e is ExistsExpr && e.Range == null) {
        var binBody = ((ExistsExpr)e).Term as BinaryExpr;
        if (binBody != null && binBody.Op == BinaryExpr.Opcode.Imp) {  // check Op, not ResolvedOp, in order to distinguish ==> and <==
          // apply the wisdom of Claude Marche: issue a warning here
          resolver.ReportWarning(ResolutionErrors.ErrorId.r_exists_quantifier_warning, e.Origin,
            "the quantifier has the form 'exists x :: A ==> B', which most often is a typo for 'exists x :: A && B'; " +
            "if you think otherwise, rewrite as 'exists x :: (A ==> B)' or 'exists x :: !A || B' to suppress this warning");
        }
      }

    } else if (expr is MemberSelectExpr) {
      var e = (MemberSelectExpr)expr;
      if (e.Member is Function or MethodOrConstructor) {
        var i = 0;
        foreach (var p in Util.Concat(e.TypeApplicationAtEnclosingClass, e.TypeApplicationJustMember)) {
          var tp = i < e.TypeApplicationAtEnclosingClass.Count ?
              (e.Member.EnclosingClass is DefaultClassDecl ?
                // In a "revealedFunction" attribute, the EnclosingClass is DefaultClassDecl
                // and does not have type arguments
                null :
                e.Member.EnclosingClass.TypeArgs[i])
            : ((ICallable)e.Member).TypeArgs[i - e.TypeApplicationAtEnclosingClass.Count];
          if (tp == null) {
            continue;
          }
          if (!IsDetermined(p.Normalize())) {
            resolver.ReportError(ResolutionErrors.ErrorId.r_type_parameter_not_determined, e.Origin,
              $"type parameter '{tp.Name}' (inferred to be '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' could not be determined");
          } else if (!context.IsPrefixPredicate) { // this check is done in extreme predicates, so no need to repeat it here for prefix predicates
            CheckContainsNoOrdinal(ResolutionErrors.ErrorId.r_type_parameter_may_not_be_ORDINAL, e.Origin, p,
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
          var hint = e.Name.StartsWith(HideRevealStmt.RevealLemmaPrefix)
            ? ". If you are making an opaque function, make sure that the function can be called."
            : "";
          resolver.ReportError(ResolutionErrors.ErrorId.r_function_type_parameter_undetermined, e.Origin,
            $"type parameter '{tp.Name}' (inferred to be '{p}') in the function call to '{e.Name}' could not be determined{hint}");
        } else if (!context.IsPrefixPredicate) { // this check is done in extreme predicates, so no need to repeat it here for prefix predicates
          CheckContainsNoOrdinal(ResolutionErrors.ErrorId.r_function_type_parameter_may_not_be_ORDINAL, e.Origin, p,
            $"type parameter '{tp.Name}' (passed in as '{p}') to function call '{e.Name}' is not allowed to use ORDINAL");
        }
        i++;
      }
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      foreach (var p in e.LHSs) {
        foreach (var x in p.Vars) {
          if (!IsDetermined(x.Type.Normalize())) {
            resolver.ReportError(ResolutionErrors.ErrorId.r_bound_variable_type_undetermined, x.Origin, $"the type of the bound variable '{x.Name}' could not be determined");
          } else {
            CheckTypeArgsContainNoOrdinal(x.Origin, x.Type, context);
          }
        }
      }
    } else if (expr is IdentifierExpr) {
      // by specializing for IdentifierExpr, error messages will be clearer
      CheckTypeIsDetermined(expr.Origin, expr.Type, "variable");
    } else if (expr is ConversionExpr) {
      var e = (ConversionExpr)expr;
      CheckTypeIsDetermined(e.Origin, e.ToType, "as-expression");

      // In the resolver refresh, the restrictions on "as" are checked as a post-inference confirmation. But in the
      // legacy resolver, the restrictions on "as" are checked here.
      if (!resolver.Options.Get(CommonOptionBag.TypeSystemRefresh)) {
        if (e.ToType.IsRefType) {
          var fromType = e.E.Type;
          Contract.Assert(resolver.Options.Get(CommonOptionBag.GeneralTraits) != CommonOptionBag.GeneralTraitsOptions.Legacy || fromType.IsRefType);
          if (fromType.IsSubtypeOf(e.ToType, false, true) || e.ToType.IsSubtypeOf(fromType, false, true)) {
            // looks good
          } else {
            resolver.ReportError(ResolutionErrors.ErrorId.r_never_succeeding_type_cast, e.Origin,
              "a type cast to a reference type ({0}) must be from a compatible type (got {1}); this cast could never succeed",
              e.ToType, fromType);
          }
        }
      }
    } else if (expr is TypeTestExpr) {
      var e = (TypeTestExpr)expr;
      CheckTypeIsDetermined(e.Origin, e.ToType, "is-expression");

      // In the resolver refresh, the restrictions on "is" are checked as a post-inference confirmation. But in the
      // legacy resolver, the restrictions on "is" are checked here.
      if (!resolver.Options.Get(CommonOptionBag.TypeSystemRefresh)) {
        var fromType = e.E.Type;
        if (fromType.IsSubtypeOf(e.ToType, false, true)) {
          // This test is allowed and it always returns true
        } else if (!e.ToType.IsSubtypeOf(fromType, false, true)) {
          resolver.ReportError(ResolutionErrors.ErrorId.r_never_succeeding_type_test, e.Origin,
            "a type test to '{0}' must be from a compatible type (got '{1}')", e.ToType, fromType);
        } else if (resolver.Options.Get(CommonOptionBag.GeneralTraits) != CommonOptionBag.GeneralTraitsOptions.Legacy && (fromType.IsTraitType || fromType.Equals(e.ToType))) {
          // it's fine
        } else if (!e.ToType.IsRefType && !e.ToType.IsTraitType) {
          resolver.ReportError(ResolutionErrors.ErrorId.r_unsupported_type_test, e.Origin,
            "a non-trivial type test is allowed only for reference types (tried to test if '{1}' is a '{0}')", e.ToType, fromType);
        }
      }
    } else if (CheckTypeIsDetermined(expr.Origin, expr.Type, "expression")) {
      if (expr is UnaryOpExpr uop) {
        // The CheckTypeInference_Visitor has already visited uop.E, but uop.E's may be undetermined. If that happened,
        // then an error has already been reported.
        if (CheckTypeIsDetermined(uop.E.Origin, uop.E.Type, "expression")) {
          uop.ResolveOp(); // Force resolution eagerly at this point to catch potential bugs
        }
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        e.ResolvedOp = ModuleResolver.ResolveOp(e.Op, e.E0.Type, e.E1.Type);
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
                    var possiblyNullTypeDecl = (ClassLikeDecl)possiblyNullUdf.ResolvedClass;
                    Contract.Assert(nonNullTypeDecl.TypeArgs.Count == possiblyNullTypeDecl.TypeArgs.Count);
                    Contract.Assert(nonNullTypeDecl.TypeArgs.Count == nntUdf.TypeArgs.Count);
                    var ty = new UserDefinedType(nntUdf.Origin, possiblyNullUdf.Name, possiblyNullTypeDecl, nntUdf.TypeArgs);

                    hint = $" (to make it possible for {name} to have the value 'null', declare its type to be '{ty}')";
                  }
                  var b = sense ? "false" : "true";
                  resolver.ReportWarning(ResolutionErrors.ErrorId.r_trivial_null_test, e.Origin,
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
                  resolver.ReportWarning(ResolutionErrors.ErrorId.r_trivial_null_inclusion_test, e.Origin,
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
                  resolver.ReportWarning(ResolutionErrors.ErrorId.r_trivial_map_null_inclusion_test, e.Origin,
                    $"the type of the other operand is a map to a non-null type, so the inclusion test of 'null' will always return '{b}'");
                }
                break;
              }
            default:
              break;
          }
        }
      }
    }

    base.PostVisitOneExpression(expr, context);
  }

  protected override void VisitExtendedPattern(ExtendedPattern pattern, TypeInferenceCheckingContext context) {
    base.VisitExtendedPattern(pattern, context);

    if (pattern is IdPattern { BoundVar: { } bv }) {
      CheckTypeIsDetermined(bv.Origin, bv.Type, "bound variable");
    }
  }

  public static bool IsDetermined(Type t) {
    Contract.Requires(t != null);
    Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);
    // all other proxies indicate the type has not yet been determined, provided their type parameters have been
    return !(t is TypeProxy) && t.TypeArgs.All(tt => IsDetermined(tt.Normalize()));
  }

  readonly ISet<TypeProxy> UnderspecifiedTypeProxies = new HashSet<TypeProxy>();

  public bool CheckTypeIsDetermined(IOrigin tok, Type t, string what) {
    Contract.Requires(tok != null);
    Contract.Requires(t != null);
    Contract.Requires(what != null);
    t = t.Normalize(); // note, this keeps type synonyms, by design

    if (t is TypeProxy) {
      var proxy = (TypeProxy)t;
      if (!UnderspecifiedTypeProxies.Contains(proxy)) {
        resolver.ReportError(ResolutionErrors.ErrorId.r_var_type_undetermined, tok, "the type of this {0} is underspecified", what);
        UnderspecifiedTypeProxies.Add(proxy);
      }
      return false;
    }
    // Recurse on type arguments:
    return t.TypeArgs.All(rg => CheckTypeIsDetermined(tok, rg, what));
  }

  public void CheckTypeArgsContainNoOrdinal(IOrigin tok, Type t, TypeInferenceCheckingContext context) {
    Contract.Requires(tok != null);
    Contract.Requires(t != null);
    if (context.IsPrefixDeclaration) {
      // User-provided expressions in extreme predicates/lemmas are checked in the extreme declarations, so need
      // need to do them here again for the prefix predicates/lemmas.
    } else {
      t = t.NormalizeExpand();
      t.TypeArgs.ForEach(rg => CheckContainsNoOrdinal(ResolutionErrors.ErrorId.r_no_ORDINAL_as_type_parameter, tok, rg, "an ORDINAL type is not allowed to be used as a type argument"));
    }
  }

  public void CheckContainsNoOrdinal(ResolutionErrors.ErrorId errorId, IOrigin tok, Type t, string errMsg) {
    Contract.Requires(tok != null);
    Contract.Requires(t != null);
    Contract.Requires(errMsg != null);
    t = t.NormalizeExpand();
    if (t.IsBigOrdinalType) {
      resolver.ReportError(errorId, tok, errMsg);
    }
    t.TypeArgs.ForEach(rg => CheckContainsNoOrdinal(errorId, tok, rg, errMsg));
  }
}