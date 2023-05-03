//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class UnderspecificationDetector : ResolverPass {
    public UnderspecificationDetector(Resolver resolver)
      : base(resolver) {
    }

    /// <summary>
    /// This method
    ///     * checks that type inference was able to determine all types
    ///     * checks that shared destructors in datatypes are in agreement
    ///     * fills in the .ResolvedOp field of binary expressions
    ///     * performs substitution for DefaultValueExpression's
    /// </summary>
    public void Check(List<TopLevelDecl> declarations) {
      Contract.Requires(declarations != null);

      foreach (TopLevelDecl d in declarations) {
        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          var prevErrCnt = ErrorCount;
          foreach (var formal in iter.Ins) {
            if (formal.DefaultValue != null) {
              CheckExpression(formal.DefaultValue, iter);
            }
          }
          iter.Members.Iter(CheckMember);
          if (prevErrCnt == ErrorCount) {
            iter.SubExpressions.Iter(e => CheckExpression(e, iter));
          }
          CheckParameterDefaultValues(iter.Ins, iter);
          if (iter.Body != null) {
            CheckExpressions(iter.Body, iter);
            if (prevErrCnt == ErrorCount) {
              CheckExpressions(iter.Body, iter);
            }
          }

        } else if (d is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)d;
          CheckExpression(dd.Constraint, new CodeContextWrapper(dd, true));
          if (dd.Witness != null) {
            CheckExpression(dd.Witness, new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost));
          }

        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          if (dd.Var != null) {
            if (!DetectUnderspecificationVisitor.IsDetermined(dd.BasePreType)) {
              ReportError(dd, "newtype's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
            }
            CheckExpression(dd.Constraint, new CodeContextWrapper(dd, true));
            if (dd.Witness != null) {
              CheckExpression(dd.Witness, new CodeContextWrapper(dd, dd.WitnessKind == SubsetTypeDecl.WKind.Ghost));
            }
          }
          CheckMembers(dd);

        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          foreach (var ctor in dd.Ctors) {
            foreach (var formal in ctor.Formals) {
              if (formal.DefaultValue != null) {
                CheckExpression(formal.DefaultValue, dd);
              }
            }
          }
          foreach (var member in resolver.classMembers[dd].Values) {
            var dtor = member as DatatypeDestructor;
            if (dtor != null) {
              var rolemodel = dtor.CorrespondingFormals[0];
              for (int i = 1; i < dtor.CorrespondingFormals.Count; i++) {
                var other = dtor.CorrespondingFormals[i];
                if (!Type.Equal_Improved(rolemodel.Type, other.Type)) {
                  ReportError(other.tok,
                    "shared destructors must have the same type, but '{0}' has type '{1}' in constructor '{2}' and type '{3}' in constructor '{4}'",
                    rolemodel.Name, rolemodel.Type, dtor.EnclosingCtors[0].Name, other.Type, dtor.EnclosingCtors[i].Name);
                } else if (rolemodel.IsGhost != other.IsGhost) {
                  ReportError(other.tok,
                    "shared destructors must agree on whether or not they are ghost, but '{0}' is {1} in constructor '{2}' and {3} in constructor '{4}'",
                    rolemodel.Name,
                    rolemodel.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[0].Name,
                    other.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[i].Name);
                }
              }
            }
          }
          foreach (var ctor in dd.Ctors) {
            CheckParameterDefaultValues(ctor.Formals, dd);
          }
          CheckMembers(dd);

        } else if (d is TopLevelDeclWithMembers md) {
          CheckMembers(md);
        }
      }
    }

    private void CheckMembers(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      foreach (var member in cl.Members) {
        var prevErrCnt = ErrorCount;
        CheckMember(member);
        if (prevErrCnt == ErrorCount) {
          if (member is Method method) {
            CheckParameterDefaultValues(method.Ins, method);
            if (method.Body != null) {
              CheckExpressions(method.Body, method);
            }
          } else if (member is Function function) {
            CheckParameterDefaultValues(function.Formals, function);
            if (function.ByMethodBody != null) {
              var m = function.ByMethodDecl;
              CheckExpressions(m.Body, m);
            }
          }
          if (prevErrCnt == ErrorCount && member is ICodeContext) {
            member.SubExpressions.Iter(e => CheckExpression(e, (ICodeContext)member));
          }
        }
      }
    }

    private void CheckMember(MemberDecl member) {
      if (member is ConstantField field) {
        if (field.Rhs != null) {
          CheckExpression(field.Rhs, new NoContext(member.EnclosingClass.EnclosingModuleDefinition));
        }
        CheckPreType(field.PreType, new NoContext(member.EnclosingClass.EnclosingModuleDefinition), field.tok, "const");

      } else if (member is Method method) {
        foreach (var formal in method.Ins) {
          if (formal.DefaultValue != null) {
            CheckExpression(formal.DefaultValue, method);
          }
        }
        method.Req.Iter(mfe => CheckAttributedExpression(mfe, method));
        CheckSpecFrameExpression(method.Mod, method);
        method.Ens.Iter(mfe => CheckAttributedExpression(mfe, method));
        CheckSpecExpression(method.Decreases, method);
        if (method.Body != null) {
          CheckExpressions(method.Body, method);
        }

      } else if (member is Function) {
        var f = (Function)member;
        foreach (var formal in f.Formals) {
          if (formal.DefaultValue != null) {
            CheckExpression(formal.DefaultValue, f);
          }
        }
        var errorCount = ErrorCount;
        f.Req.Iter(e => CheckExpression(e.E, f));
        f.Ens.Iter(e => CheckExpression(e.E, f));
        f.Reads.Iter(fe => CheckExpression(fe.E, f));
        CheckSpecExpression(f.Decreases, f);
        if (f.Body != null) {
          CheckExpression(f.Body, f);
        }
        if (errorCount == ErrorCount) {
          if (f is ExtremePredicate cop) {
            CheckMember(cop.PrefixPredicate);
          } else if (f.ByMethodDecl != null) {
            CheckMember(f.ByMethodDecl);
          }
        }
      }
    }

    private void CheckPreType(PreType preType, ICodeContext codeContext, IToken tok, string what) {
      var visitor = new DetectUnderspecificationVisitor(this, codeContext);
      visitor.CheckPreTypeIsDetermined(tok, preType, what);
    }

    private void CheckExpressions(Statement stmt, ICodeContext codeContext) {
      var visitor = new DetectUnderspecificationVisitor(this, codeContext);
      visitor.Visit(stmt);
    }

    private void CheckExpression(Expression expr, ICodeContext codeContext) {
      var visitor = new DetectUnderspecificationVisitor(this, codeContext);
      visitor.Visit(expr);
    }

    private void CheckSpecExpression(Specification<Expression> spec, ICodeContext codeContext) {
      Attributes.SubExpressions(spec.Attributes).Iter(e => CheckExpression(e, codeContext));
      spec.Expressions.Iter(e => CheckExpression(e, codeContext));
    }

    private void CheckSpecFrameExpression(Specification<FrameExpression> spec, ICodeContext codeContext) {
      Attributes.SubExpressions(spec.Attributes).Iter(e => CheckExpression(e, codeContext));
      spec.Expressions.Iter(fe => CheckExpression(fe.E, codeContext));
    }

    private void CheckAttributedExpression(AttributedExpression ae, ICodeContext codeContext) {
      Attributes.SubExpressions(ae.Attributes).Iter(e => CheckExpression(e, codeContext));
      CheckExpression(ae.E, codeContext);
    }

    private void CheckParameterDefaultValues(List<Formal> formals, ICodeContext codeContext) {
      // TODO
    }
  }

  // ------------------------------------------------------------------------------------------------------
  // ----- CheckTypeInference -----------------------------------------------------------------------------
  // ------------------------------------------------------------------------------------------------------
  // The CheckTypeInference machinery visits every type in a given part of the AST (for example,
  // CheckTypeInference(Expression) does so for an Expression and CheckTypeInference_Member(MemberDecl)
  // does so for a MemberDecl) to make sure that all parts of types were fully inferred.
  public class DetectUnderspecificationVisitor : BottomUpVisitor {
    private readonly UnderspecificationDetector cus;
    private readonly ICodeContext codeContext;

    public DetectUnderspecificationVisitor(UnderspecificationDetector cus, ICodeContext codeContext) {
      Contract.Requires(cus != null);
      Contract.Requires(codeContext != null);
      this.cus = cus;
      this.codeContext = codeContext;
    }

    protected override void VisitOneStmt(Statement stmt) {
      if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        foreach (var local in s.Locals) {
          CheckPreTypeIsDetermined(local.Tok, local.PreType, "local variable");
          CheckTypeArgsContainNoOrdinal(local.Tok, local.PreType);
        }
      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        s.LocalVars.Iter(local => CheckPreTypeIsDetermined(local.Tok, local.PreType, "local variable"));
        s.LocalVars.Iter(local => CheckTypeArgsContainNoOrdinal(local.Tok, local.PreType));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        s.BoundVars.Iter(bv => CheckPreTypeIsDetermined(bv.tok, bv.PreType, "bound variable"));
        s.BoundVars.Iter(bv => CheckTypeArgsContainNoOrdinal(bv.tok, bv.PreType));

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        if (s.AssumeToken == null) {
          var varLhss = new List<IVariable>();
          foreach (var lhs in s.Lhss) {
            var ide = (IdentifierExpr)lhs.Resolved;  // successful resolution implies all LHS's are IdentifierExpr's
            varLhss.Add(ide.Var);
          }
        }
        foreach (var lhs in s.Lhss) {
          var what = lhs is IdentifierExpr ? string.Format("variable '{0}'", ((IdentifierExpr)lhs).Name) : "LHS";
          CheckTypeArgsContainNoOrdinal(lhs.tok, lhs.PreType);
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
      var familyDeclName = PreTypeResolver.AncestorName(expr.PreType);

      if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (PreTypeResolver.IsBitvectorName(familyDeclName) || familyDeclName == "ORDINAL") {
          var n = (BigInteger)e.Value;
          var absN = n < 0 ? -n : n;
          // For bitvectors, check that the magnitude fits the width
          if (PreTypeResolver.IsBitvectorName(familyDeclName, out var width) && Resolver.MaxBV(width) < absN) {
            cus.ReportError(e.tok, "literal ({0}) is too large for the bitvector type {1}", absN, e.PreType);
          }
          // For bitvectors and ORDINALs, check for a unary minus that, earlier, was mistaken for a negative literal
          // This can happen only in `match` patterns (see comment by LitPattern.OptimisticallyDesugaredLit).
          if (n < 0 || e.tok.val == "-0") {
            Contract.Assert(e.tok.val == "-0");  // this and the "if" above tests that "n < 0" happens only when the token is "-0"
            cus.ReportError(e.tok, "unary minus (-{0}, type {1}) not allowed in case pattern", absN, e.PreType);
          }
        }

        if (expr is StaticReceiverExpr stexpr) {
          CheckPreTypeIsDetermined(stexpr.tok, stexpr.PreType, "static receiver");
        }

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        foreach (var bv in e.BoundVars) {
          CheckVariable(bv, "bound variable");
          if (codeContext is ExtremePredicate || codeContext is ExtremeLemma) {
            CheckContainsNoOrdinal(bv.tok, bv.PreType, string.Format("type of bound variable '{0}' ('{1}') is not allowed to use type ORDINAL", bv.Name, bv.PreType));
          }
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member is Function || e.Member is Method) {
          var i = 0;
          foreach (var p in Util.Concat(e.PreTypeApplication_AtEnclosingClass, e.PreTypeApplication_JustMember)) {
            var tp =
              i < e.PreTypeApplication_AtEnclosingClass.Count
                ? e.Member.EnclosingClass.TypeArgs[i]
                : ((ICallable)e.Member).TypeArgs[i - e.PreTypeApplication_AtEnclosingClass.Count];
            if (!IsDetermined(p)) {
              cus.ReportError(e.tok, $"type parameter '{tp.Name}' (inferred to be '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' could not be determined");
            } else {
              CheckContainsNoOrdinal(e.tok, p, $"type parameter '{tp.Name}' (passed in as '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' is not allowed to use ORDINAL");
            }
            i++;
          }
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var i = 0;
        foreach (var p in Util.Concat(e.PreTypeApplication_AtEnclosingClass, e.PreTypeApplication_JustFunction)) {
          var tp =
            i < e.PreTypeApplication_AtEnclosingClass.Count
              ? e.Function.EnclosingClass.TypeArgs[i]
              : e.Function.TypeArgs[i - e.PreTypeApplication_AtEnclosingClass.Count];
          if (!IsDetermined(p)) {
            var hint = e.Name.StartsWith("reveal_") ? ". If you are making an opaque function, make sure that the function can be called." : "";
            cus.ReportError(e.tok, $"type parameter '{tp.Name}' (inferred to be '{p}') in the function call to '{e.Name}' could not be determined{hint}");
          } else {
            CheckContainsNoOrdinal(e.tok, p, $"type parameter '{tp.Name}' (passed in as '{p}') to function call '{e.Name}' is not allowed to use ORDINAL");
          }
          i++;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var lhsPattern in e.LHSs) {
          foreach (var bv in lhsPattern.Vars) {
            CheckVariable(bv, "bound variable");
            CheckTypeArgsContainNoOrdinal(bv.tok, bv.PreType);
          }
        }

      } else if (expr is IdentifierExpr) {
        // by specializing for IdentifierExpr, error messages will be clearer
        CheckPreTypeIsDetermined(expr.tok, expr.PreType, "variable");

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        CheckPreTypeIsDetermined(e.tok, e.PreType, "cast target");

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        CheckPreTypeIsDetermined(e.tok, e.PreType, "type test target");

      } else if (CheckPreTypeIsDetermined(expr.tok, expr.PreType, "expression")) {
        if (expr is UnaryOpExpr uop) {
          var resolvedOp = (uop.Op, PreTypeResolver.AncestorName(uop.E.PreType)) switch {
            (UnaryOpExpr.Opcode.Not, "bool") => UnaryOpExpr.ResolvedOpcode.BoolNot,
            (UnaryOpExpr.Opcode.Cardinality, "set") => UnaryOpExpr.ResolvedOpcode.SetCard,
            (UnaryOpExpr.Opcode.Cardinality, "seq") => UnaryOpExpr.ResolvedOpcode.SeqLength,
            (UnaryOpExpr.Opcode.Cardinality, "multiset") => UnaryOpExpr.ResolvedOpcode.MultiSetCard,
            (UnaryOpExpr.Opcode.Cardinality, "map") => UnaryOpExpr.ResolvedOpcode.MapCard,
            (UnaryOpExpr.Opcode.Fresh, _) => UnaryOpExpr.ResolvedOpcode.Fresh,
            (UnaryOpExpr.Opcode.Allocated, _) => UnaryOpExpr.ResolvedOpcode.Allocated,
            (UnaryOpExpr.Opcode.Lit, _) => UnaryOpExpr.ResolvedOpcode.Lit,
            _ => UnaryOpExpr.ResolvedOpcode.YetUndetermined // Unreachable
          };
          if (uop.Op == UnaryOpExpr.Opcode.Not && PreTypeResolver.IsBitvectorName(familyDeclName)) {
            resolvedOp = UnaryOpExpr.ResolvedOpcode.BVNot;
          }
          uop.SetResolveOp(resolvedOp);

        } else if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          e.ResolvedOp = ResolveOp(e.Op, e.E0.PreType, e.E1.PreType);

        }
      }
    }

    /// Note: this method is allowed to be called even if "type" does not make sense for "op", as might be the case if
    /// resolution of the binary expression failed.  If so, an arbitrary resolved opcode is returned.
    /// Usually, the type of the right-hand operand is used to determine the resolved operator (hence, the shorter
    /// name "operandPreType" instead of, say, "rightOperandType").
    /// </summary>
    static BinaryExpr.ResolvedOpcode ResolveOp(BinaryExpr.Opcode op, PreType leftOperandPreType, PreType operandPreType) {
      Contract.Requires(leftOperandPreType != null);
      Contract.Requires(operandPreType != null);
      operandPreType = operandPreType.Normalize();
      var operandFamilyName = PreTypeResolver.AncestorName(operandPreType);
      switch (op) {
        case BinaryExpr.Opcode.Iff:
          return BinaryExpr.ResolvedOpcode.Iff;
        case BinaryExpr.Opcode.Imp:
          return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.Exp:
          return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.And:
          return BinaryExpr.ResolvedOpcode.And;
        case BinaryExpr.Opcode.Or:
          return BinaryExpr.ResolvedOpcode.Or;
        case BinaryExpr.Opcode.Eq:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.SetEq,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetEq,
            "seq" => BinaryExpr.ResolvedOpcode.SeqEq,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.MapEq,
            _ => BinaryExpr.ResolvedOpcode.EqCommon
          };
        case BinaryExpr.Opcode.Neq:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.SetNeq,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetNeq,
            "seq" => BinaryExpr.ResolvedOpcode.SeqNeq,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.MapNeq,
            _ => BinaryExpr.ResolvedOpcode.NeqCommon
          };
        case BinaryExpr.Opcode.Disjoint:
          return operandFamilyName == "multiset" ? BinaryExpr.ResolvedOpcode.MultiSetDisjoint : BinaryExpr.ResolvedOpcode.Disjoint;
        case BinaryExpr.Opcode.Lt: {
            if (operandPreType is DPreType dp && PreTypeResolver.AncestorDecl(dp.Decl) is IndDatatypeDecl) {
              return BinaryExpr.ResolvedOpcode.RankLt;
            }
            return operandFamilyName switch {
              "set" or "iset" => BinaryExpr.ResolvedOpcode.ProperSubset,
              "multiset" => BinaryExpr.ResolvedOpcode.ProperMultiSubset,
              "seq" => BinaryExpr.ResolvedOpcode.ProperPrefix,
              "char" => BinaryExpr.ResolvedOpcode.LtChar,
              _ => BinaryExpr.ResolvedOpcode.Lt
            };
          }
        case BinaryExpr.Opcode.Le:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Subset,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSubset,
            "seq" => BinaryExpr.ResolvedOpcode.Prefix,
            "char" => BinaryExpr.ResolvedOpcode.LeChar,
            _ => BinaryExpr.ResolvedOpcode.Le
          };
        case BinaryExpr.Opcode.LeftShift:
          return BinaryExpr.ResolvedOpcode.LeftShift;
        case BinaryExpr.Opcode.RightShift:
          return BinaryExpr.ResolvedOpcode.RightShift;
        case BinaryExpr.Opcode.Add:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Union,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetUnion,
            "seq" => BinaryExpr.ResolvedOpcode.Concat,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.MapMerge,
            _ => BinaryExpr.ResolvedOpcode.Add
          };
        case BinaryExpr.Opcode.Sub: {
            var leftFamilyName = PreTypeResolver.AncestorName(leftOperandPreType);
            if (leftFamilyName == "map" || leftFamilyName == "imap") {
              return BinaryExpr.ResolvedOpcode.MapSubtraction;
            }
            return operandFamilyName switch {
              "set" or "iset" => BinaryExpr.ResolvedOpcode.SetDifference,
              "multiset" => BinaryExpr.ResolvedOpcode.MultiSetDifference,
              _ => BinaryExpr.ResolvedOpcode.Sub
            };
          }
        case BinaryExpr.Opcode.Mul:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Intersection,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetIntersection,
            _ => BinaryExpr.ResolvedOpcode.Mul
          };
        case BinaryExpr.Opcode.Gt: {
            if (operandPreType is DPreType dp && PreTypeResolver.AncestorDecl(dp.Decl) is IndDatatypeDecl) {
              return BinaryExpr.ResolvedOpcode.RankGt;
            }
            return operandFamilyName switch {
              "set" or "iset" => BinaryExpr.ResolvedOpcode.ProperSuperset,
              "multiset" => BinaryExpr.ResolvedOpcode.ProperMultiSuperset,
              "char" => BinaryExpr.ResolvedOpcode.GtChar,
              _ => BinaryExpr.ResolvedOpcode.Gt
            };
          }
        case BinaryExpr.Opcode.Ge:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Superset,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSuperset,
            "char" => BinaryExpr.ResolvedOpcode.GeChar,
            _ => BinaryExpr.ResolvedOpcode.Ge
          };
        case BinaryExpr.Opcode.In:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.InSet,
            "multiset" => BinaryExpr.ResolvedOpcode.InMultiSet,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.InMap,
            _ => BinaryExpr.ResolvedOpcode.InSeq
          };
        case BinaryExpr.Opcode.NotIn:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.NotInSet,
            "multiset" => BinaryExpr.ResolvedOpcode.NotInMultiSet,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.NotInMap,
            _ => BinaryExpr.ResolvedOpcode.NotInSeq
          };
        case BinaryExpr.Opcode.Div:
          return BinaryExpr.ResolvedOpcode.Div;
        case BinaryExpr.Opcode.Mod:
          return BinaryExpr.ResolvedOpcode.Mod;
        case BinaryExpr.Opcode.BitwiseAnd:
          return BinaryExpr.ResolvedOpcode.BitwiseAnd;
        case BinaryExpr.Opcode.BitwiseOr:
          return BinaryExpr.ResolvedOpcode.BitwiseOr;
        case BinaryExpr.Opcode.BitwiseXor:
          return BinaryExpr.ResolvedOpcode.BitwiseXor;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();  // unexpected operator
      }
    }

    void CheckVariable(IVariable v, string what) {
      if (!IsDetermined(v.PreType)) {
        cus.ReportError(v.Tok, $"type of {what} '{v.Name}' could not be determined{UndeterminedPreTypeToString(v.PreType)}; please specify the type explicitly");
      }
    }

    private string UndeterminedPreTypeToString(PreType preType) {
      if (preType.Normalize() is PreTypeProxy) {
        return "";
      } else {
        return $" ('{preType}')";
      }
    }

    public static bool IsDetermined(PreType pt) {
      Contract.Requires(pt != null);
      if (pt.Normalize() is DPreType dp) {
        if (dp.PrintablePreType != null) {
          // If the type is a synonym, focus on it, which will check that all its type arguments have been filled in
          dp = dp.PrintablePreType;
        }
        Contract.Assert(dp.Decl != null); // every DPreType has a non-null .Decl
        return dp.Arguments.TrueForAll(IsDetermined);
      }
      return false;
    }

    private readonly ISet<PreTypeProxy> underspecifiedTypeProxies = new HashSet<PreTypeProxy>();

    /// <summary>
    /// Check if "pt" is fully determined. If it is, return "true". If it is not, then
    /// report an error and return "false".
    /// </summary>
    public bool CheckPreTypeIsDetermined(IToken tok, PreType pt, string what, PreType origPreType = null) {
      Contract.Requires(tok != null);
      Contract.Requires(pt != null);
      Contract.Requires(what != null);
      origPreType ??= pt;
      pt = pt.Normalize();

      if (pt is PreTypeProxy proxy) {
        if (!underspecifiedTypeProxies.Contains(proxy)) {
          // report an error for this TypeProxy only once
          cus.ReportError(tok, $"the type{UndeterminedPreTypeToString(origPreType)} of this {what} is underspecified");
          underspecifiedTypeProxies.Add(proxy);
        }
        return false;
      }
      var dp = (DPreType)pt;
      if (dp.PrintablePreType != null) {
        // If the type is a synonym, focus on it, which will check that all its type arguments have been filled in
        dp = dp.PrintablePreType;
      }
      // Recurse on type arguments:
      return dp.Arguments.TrueForAll(tt => CheckPreTypeIsDetermined(tok, tt, what, origPreType));
    }

    public void CheckTypeArgsContainNoOrdinal(IToken tok, PreType preType) {
      Contract.Requires(tok != null);
      Contract.Requires(preType != null);
      if (preType.Normalize() is DPreType dp) {
        dp.Arguments.Iter(tt => CheckContainsNoOrdinal(tok, tt, "an ORDINAL type is not allowed to be used as a type argument"));
      }
    }

    public void CheckContainsNoOrdinal(IToken tok, PreType preType, string errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(preType != null);
      Contract.Requires(errMsg != null);
      if (preType.Normalize() is DPreType dp) {
        if (PreTypeResolver.AncestorName(dp) == "ORDINAL") {
          cus.ReportError(tok, errMsg);
        }
        dp.Arguments.Iter(tt => CheckContainsNoOrdinal(tok, tt, errMsg));
      }
    }
  }
}
