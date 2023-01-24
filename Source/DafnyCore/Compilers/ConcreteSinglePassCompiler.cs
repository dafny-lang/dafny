using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public abstract class ConcreteSinglePassCompiler : SinglePassCompiler<ICanRender> {
  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    Coverage = new CoverageInstrumenter(this);
  }

  // TODO Move TrExpr to SinglePassCompiler once all the methods it calls have been made to use TExpression instead of ConcreteSyntaxTree
  /// <summary>
  /// Before calling TrExpr(expr), the caller must have spilled the let variables declared in "expr".
  /// In order to give the compiler a way to put supporting statements above the current one, wStmts must be passed.
  /// </summary>
  protected internal override ICanRender TrExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
    Contract.Requires(expr != null);

    var wr = new ConcreteSyntaxTree();
    if (expr is LiteralExpr) {
      LiteralExpr e = (LiteralExpr)expr;
      return EmitLiteralExpr(e);
    } else if (expr is ThisExpr) {
      var result = EmitThis();
      if (thisContext != null) {
        var instantiatedType = expr.Type.Subst(thisContext.ParentFormalTypeParametersToActuals);
        result = EmitCoercionIfNecessary(UserDefinedType.FromTopLevelDecl(expr.tok, thisContext), instantiatedType, expr.tok, result);
      }

      return result;
    } else if (expr is IdentifierExpr) {
      var e = (IdentifierExpr)expr;
      if (inLetExprBody && !(e.Var is BoundVar)) {
        // copy variable to a temp since
        //   - C# doesn't allow out param in letExpr body, and
        //   - Java doesn't allow any non-final variable in letExpr body.
        var name = ProtectedFreshId("_pat_let_tv");
        wr.Write(name);
        DeclareLocalVar(name, null, null, false, IdName(e.Var), copyInstrWriters.Peek(), e.Type);
      } else {
        wr.Write(IdName(e.Var));
      }
    } else if (expr is SetDisplayExpr) {
      var e = (SetDisplayExpr)expr;
      EmitCollectionDisplay(e.Type.AsSetType, e.tok, e.Elements, inLetExprBody, wr, wStmts);

    } else if (expr is MultiSetDisplayExpr) {
      var e = (MultiSetDisplayExpr)expr;
      EmitCollectionDisplay(e.Type.AsMultiSetType, e.tok, e.Elements, inLetExprBody, wr, wStmts);

    } else if (expr is SeqDisplayExpr) {
      var e = (SeqDisplayExpr)expr;
      EmitCollectionDisplay(e.Type.AsSeqType, e.tok, e.Elements, inLetExprBody, wr, wStmts);

    } else if (expr is MapDisplayExpr) {
      var e = (MapDisplayExpr)expr;
      EmitMapDisplay(e.Type.AsMapType, e.tok, e.Elements, inLetExprBody, wr, wStmts);

    } else if (expr is MemberSelectExpr) {
      MemberSelectExpr e = (MemberSelectExpr)expr;
      SpecialField sf = e.Member as SpecialField;
      if (sf != null) {
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, e.Obj.Type, out compiledName, out preStr, out postStr);
        wr.Write(preStr);

        if (sf.IsStatic && !SupportsStaticsInGenericClasses && sf.EnclosingClass.TypeArgs.Count != 0) {
          var typeArgs = e.TypeApplication_AtEnclosingClass;
          Contract.Assert(typeArgs.Count == sf.EnclosingClass.TypeArgs.Count);
          wr.Write("{0}.", TypeName_Companion(e.Obj.Type, wr, e.tok, sf));
          EmitNameAndActualTypeArgs(IdName(e.Member), typeArgs, e.tok, wr);
          var tas = TypeArgumentInstantiation.ListFromClass(sf.EnclosingClass, typeArgs);
          EmitTypeDescriptorsActuals(tas, e.tok, wr.ForkInParens());
        } else {
          void writeObj(ConcreteSyntaxTree w) {
            //Contract.Assert(!sf.IsStatic);
            w = EmitCoercionIfNecessary(e.Obj.Type, UserDefinedType.UpcastToMemberEnclosingType(e.Obj.Type, e.Member), e.tok, w);
            TrParenExpr(e.Obj, w, inLetExprBody, wStmts);
          }

          var typeArgs = CombineAllTypeArguments(e.Member, e.TypeApplication_AtEnclosingClass, e.TypeApplication_JustMember);
          EmitMemberSelect(writeObj, e.Obj.Type, e.Member, typeArgs, e.TypeArgumentSubstitutionsWithParents(), expr.Type).EmitRead(wr);
        }

        wr.Write(postStr);
      } else {
        var typeArgs = CombineAllTypeArguments(e.Member, e.TypeApplication_AtEnclosingClass, e.TypeApplication_JustMember);
        var typeMap = e.TypeArgumentSubstitutionsWithParents();
        var customReceiver = NeedsCustomReceiver(e.Member) && !(e.Member.EnclosingClass is TraitDecl);
        if (!customReceiver && !e.Member.IsStatic) {
          Action<ConcreteSyntaxTree> obj;
          // The eta conversion here is to avoid capture of the receiver, because the call to EmitMemberSelect below may generate
          // a lambda expression in the target language.
          if (e.Member is Function && typeArgs.Count != 0) {
            // need to eta-expand wrap the receiver
            var etaReceiver = ProtectedFreshId("_eta_this");
            wr = CreateIIFE_ExprBody(etaReceiver, e.Obj.Type, e.Obj.tok, e.Obj, inLetExprBody, e.Type.Subst(typeMap), e.tok, wr, ref wStmts);
            obj = w => w.Write(etaReceiver);
          } else {
            obj = w => w.Append(TrExpr(e.Obj, inLetExprBody, wStmts));
          }
          EmitMemberSelect(obj, e.Obj.Type, e.Member, typeArgs, typeMap, expr.Type).EmitRead(wr);
        } else {
          string customReceiverName = null;
          if (customReceiver && e.Member is Function) {
            // need to eta-expand wrap the receiver
            customReceiverName = ProtectedFreshId("_eta_this");
            wr = CreateIIFE_ExprBody(customReceiverName, e.Obj.Type, e.Obj.tok, e.Obj, inLetExprBody, e.Type.Subst(typeMap), e.tok, wr, ref wStmts);
          }
          Action<ConcreteSyntaxTree> obj = w => w.Write(TypeName_Companion(e.Obj.Type, wr, e.tok, e.Member));
          EmitMemberSelect(obj, e.Obj.Type, e.Member, typeArgs, typeMap, expr.Type, customReceiverName).EmitRead(wr);
        }
      }
    } else if (expr is SeqSelectExpr) {
      SeqSelectExpr e = (SeqSelectExpr)expr;
      Contract.Assert(e.Seq.Type != null);
      if (e.Seq.Type.IsArrayType) {
        if (e.SelectOne) {
          Contract.Assert(e.E0 != null && e.E1 == null);
          var w = EmitArraySelect(new List<Expression>() { e.E0 }, e.Type, inLetExprBody, wr, wStmts);
          TrParenExpr(e.Seq, w, inLetExprBody, wStmts);
        } else {
          EmitSeqSelectRange(e.Seq, e.E0, e.E1, true, inLetExprBody, wr, wStmts);
        }
      } else if (e.SelectOne) {
        Contract.Assert(e.E0 != null && e.E1 == null);
        EmitIndexCollectionSelect(e.Seq, e.E0, inLetExprBody, wr, wStmts);
      } else {
        EmitSeqSelectRange(e.Seq, e.E0, e.E1, false, inLetExprBody, wr, wStmts);
      }
    } else if (expr is SeqConstructionExpr) {
      var e = (SeqConstructionExpr)expr;
      EmitSeqConstructionExpr(e, inLetExprBody, wr, wStmts);
    } else if (expr is MultiSetFormingExpr) {
      var e = (MultiSetFormingExpr)expr;
      EmitMultiSetFormingExpr(e, inLetExprBody, wr, wStmts);
    } else if (expr is MultiSelectExpr) {
      MultiSelectExpr e = (MultiSelectExpr)expr;
      WriteCast(TypeName(e.Type.NormalizeExpand(), wr, e.tok), wr);
      var w = EmitArraySelect(e.Indices, e.Type, inLetExprBody, wr, wStmts);
      TrParenExpr(e.Array, w, inLetExprBody, wStmts);

    } else if (expr is SeqUpdateExpr) {
      SeqUpdateExpr e = (SeqUpdateExpr)expr;
      var collectionType = e.Type.AsCollectionType;
      Contract.Assert(collectionType != null);
      EmitIndexCollectionUpdate(e.Seq, e.Index, e.Value, collectionType, inLetExprBody, wr, wStmts);
    } else if (expr is DatatypeUpdateExpr) {
      var e = (DatatypeUpdateExpr)expr;
      if (e.Members.All(member => member.IsGhost)) {
        // all fields to be updated are ghost, which doesn't change the value
        wr.Append(TrExpr(e.Root, inLetExprBody, wStmts));
        return wr;
      }
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(e.Root.Type.AsDatatype, out var dtor)) {
        var i = e.Members.IndexOf(dtor);
        if (0 <= i) {
          // the datatype is an erasable wrapper and its core destructor is part of the update (which implies everything else must be a ghost),
          // so proceed as with the rhs
          Contract.Assert(Enumerable.Range(0, e.Members.Count).All(j => j == i || e.Members[j].IsGhost));
          Contract.Assert(e.Members.Count == e.Updates.Count);
          var rhs = e.Updates[i].Item3;
          wr.Append(TrExpr(rhs, inLetExprBody, wStmts));
          return wr;
        }
      }
      // the optimized cases don't apply, so proceed according to the desugaring
      wr.Append(TrExpr(e.ResolvedExpression, inLetExprBody, wStmts));
    } else if (expr is FunctionCallExpr) {
      FunctionCallExpr e = (FunctionCallExpr)expr;
      if (e.Function is SpecialFunction) {
        CompileSpecialFunctionCallExpr(e, wr, inLetExprBody, wStmts, TrExpr);
      } else {
        CompileFunctionCallExpr(e, wr, inLetExprBody, wStmts, TrExpr);
      }

    } else if (expr is ApplyExpr) {
      var e = expr as ApplyExpr;
      EmitApplyExpr(e.Function.Type, e.tok, e.Function, e.Args, inLetExprBody, wr, wStmts);

    } else if (expr is DatatypeValue) {
      var dtv = (DatatypeValue)expr;
      Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved

      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(dtv.Ctor.EnclosingDatatype, out var dtor)) {
        var i = dtv.Ctor.Destructors.IndexOf(dtor);
        Contract.Assert(0 <= i);
        wr.Append(TrExpr(dtv.Arguments[i], inLetExprBody, wStmts));
        return wr;
      }

      var wrArgumentList = new ConcreteSyntaxTree();
      string sep = "";
      for (int i = 0; i < dtv.Arguments.Count; i++) {
        var formal = dtv.Ctor.Formals[i];
        if (!formal.IsGhost) {
          wrArgumentList.Write(sep);
          var w = EmitCoercionIfNecessary(from: dtv.Arguments[i].Type, to: dtv.Ctor.Formals[i].Type, tok: dtv.tok, wr: wrArgumentList);
          w.Append(TrExpr(dtv.Arguments[i], inLetExprBody, wStmts));
          sep = ", ";
        }
      }
      EmitDatatypeValue(dtv, wrArgumentList.ToString(), wr);

    } else if (expr is OldExpr) {
      Contract.Assert(false); throw new cce.UnreachableException();  // 'old' is always a ghost

    } else if (expr is UnaryOpExpr) {
      var e = (UnaryOpExpr)expr;
      if (e.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BVNot) {
        wr = EmitBitvectorTruncation(e.Type.AsBitVectorType, false, wr);
      }
      EmitUnaryExpr(UnaryOpCodeMap[e.ResolvedOp], e.E, inLetExprBody, wr, wStmts);
    } else if (expr is ConversionExpr) {
      var e = (ConversionExpr)expr;
      Contract.Assert(e.ToType.IsRefType == e.E.Type.IsRefType);
      if (e.ToType.IsRefType) {
        var w = EmitCoercionIfNecessary(e.E.Type, e.ToType, e.tok, wr);
        w = EmitDowncastIfNecessary(e.E.Type, e.ToType, e.tok, w);
        w.Append(TrExpr(e.E, inLetExprBody, wStmts));
      } else {
        EmitConversionExpr(e, inLetExprBody, wr, wStmts);
      }

    } else if (expr is TypeTestExpr) {
      var e = (TypeTestExpr)expr;
      var fromType = e.E.Type;
      if (fromType.IsSubtypeOf(e.ToType, false, false)) {
        wr.Append(TrExpr(Expression.CreateBoolLiteral(e.tok, true), inLetExprBody, wStmts));
      } else {
        var name = $"_is_{GetUniqueAstNumber(e)}";
        wr = CreateIIFE_ExprBody(name, fromType, e.tok, e.E, inLetExprBody, Type.Bool, e.tok, wr, ref wStmts);
        EmitTypeTest(name, e.E.Type, e.ToType, e.tok, wr);
      }

    } else if (expr is BinaryExpr) {
      var e = (BinaryExpr)expr;

      if (IsComparisonToZero(e, out var arg, out var sign, out var negated) &&
          CompareZeroUsingSign(arg.Type)) {
        // Transform e.g. x < BigInteger.Zero into x.Sign == -1
        var w = EmitSign(arg.Type, wr);
        TrParenExpr(arg, w, inLetExprBody, wStmts);
        wr.Write(negated ? " != " : " == ");
        wr.Write(sign.ToString());
      } else {
        string opString, preOpString, postOpString, callString, staticCallString;
        bool reverseArguments, truncateResult, convertE1_to_int;
        CompileBinOp(e.ResolvedOp, e.E0, e.E1, e.tok, expr.Type,
          out opString,
          out preOpString,
          out postOpString,
          out callString,
          out staticCallString,
          out reverseArguments,
          out truncateResult,
          out convertE1_to_int,
          wr);

        if (truncateResult && e.Type.IsBitVectorType) {
          wr = EmitBitvectorTruncation(e.Type.AsBitVectorType, true, wr);
        }
        var e0 = reverseArguments ? e.E1 : e.E0;
        var e1 = reverseArguments ? e.E0 : e.E1;
        if (opString != null) {
          var nativeType = AsNativeType(e.Type);
          string nativeName = null, literalSuffix = null;
          bool needsCast = false;
          if (nativeType != null) {
            GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
          }

          var inner = wr;
          if (needsCast) {
            inner = wr.Write("(" + nativeName + ")").ForkInParens();
          }
          inner.Write(preOpString);
          TrParenExpr(e0, inner, inLetExprBody, wStmts);
          inner.Write(" {0} ", opString);
          if (convertE1_to_int) {
            EmitExprAsInt(e1, inLetExprBody, inner, wStmts);
          } else {
            TrParenExpr(e1, inner, inLetExprBody, wStmts);
          }
          wr.Write(postOpString);
        } else if (callString != null) {
          wr.Write(preOpString);
          TrParenExpr(e0, wr, inLetExprBody, wStmts);
          wr.Write(".{0}(", callString);
          if (convertE1_to_int) {
            EmitExprAsInt(e1, inLetExprBody, wr, wStmts);
          } else {
            TrParenExpr(e1, wr, inLetExprBody, wStmts);
          }
          wr.Write(")");
          wr.Write(postOpString);
        } else if (staticCallString != null) {
          wr.Write(preOpString);
          wr.Write("{0}(", staticCallString);
          wr.Append(TrExpr(e0, inLetExprBody, wStmts));
          wr.Write(", ");
          wr.Append(TrExpr(e1, inLetExprBody, wStmts));
          wr.Write(")");
          wr.Write(postOpString);
        }
      }
    } else if (expr is TernaryExpr) {
      Contract.Assume(false);  // currently, none of the ternary expressions is compilable

    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      if (e.Exact) {
        // The Dafny "let" expression
        //    var Pattern(x,y) := G; E
        // is translated into C# as:
        //    LamLet(G, tmp =>
        //      LamLet(dtorX(tmp), x =>
        //      LamLet(dtorY(tmp), y => E)))
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        var w = wr;
        for (int i = 0; i < e.LHSs.Count; i++) {
          var lhs = e.LHSs[i];
          if (Contract.Exists(lhs.Vars, bv => !bv.IsGhost)) {
            var rhsName = $"_pat_let{GetUniqueAstNumber(e)}_{i}";
            w = CreateIIFE_ExprBody(rhsName, e.RHSs[i].Type, e.RHSs[i].tok, e.RHSs[i], inLetExprBody, e.Body.Type, e.Body.tok, w, ref wStmts);
            w = TrCasePattern(lhs, rhsName, e.RHSs[i].Type, e.Body.Type, w, ref wStmts);
          }
        }
        w.Append(TrExpr(e.Body, true, wStmts));
      } else if (e.BoundVars.All(bv => bv.IsGhost)) {
        // The Dafny "let" expression
        //    ghost var x,y :| Constraint; E
        // is compiled just like E is, because the resolver has already checked that x,y (or other ghost variables, for that matter) don't
        // occur in E (moreover, the verifier has checked that values for x,y satisfying Constraint exist).
        wr.Append(TrExpr(e.Body, inLetExprBody, wStmts));
      } else {
        // The Dafny "let" expression
        //    var x,y :| Constraint; E
        // is translated into C# as:
        //    LamLet(0, dummy => {  // the only purpose of this construction here is to allow us to add some code inside an expression in C#
        //        var x,y;
        //        // Embark on computation that fills in x,y according to Constraint; the computation stops when the first
        //        // such value is found, but since the verifier checks that x,y follows uniquely from Constraint, this is
        //        // not a source of nondeterminancy.
        //        return E;
        //      })
        Contract.Assert(e.RHSs.Count == 1);  // checked by resolution
        var missingBounds = ComprehensionExpr.BoolBoundedPool.MissingBounds(e.BoundVars.ToList<BoundVar>(), e.Constraint_Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable);
        if (missingBounds.Count != 0) {
          foreach (var bv in missingBounds) {
            Error(e.tok, "this let-such-that expression is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}'", wr, bv.Name);
          }
        } else {
          var w = CreateIIFE1(0, e.Body.Type, e.Body.tok, "_let_dummy_" + GetUniqueAstNumber(e), wr, wStmts);
          foreach (var bv in e.BoundVars) {
            DeclareLocalVar(IdName(bv), bv.Type, bv.tok, false, ForcePlaceboValue(bv.Type, wr, bv.tok, true), w);
          }
          TrAssignSuchThat(new List<IVariable>(e.BoundVars).ConvertAll(bv => (IVariable)bv), e.RHSs[0], e.Constraint_Bounds, e.tok.line, w, inLetExprBody);
          EmitReturnExpr(e.Body, e.Body.Type, true, w);
        }
      }
    } else if (expr is NestedMatchExpr nestedMatchExpr) {
      wr.Append(TrExpr(nestedMatchExpr.Flattened, inLetExprBody, wStmts));
    } else if (expr is MatchExpr) {
      var e = (MatchExpr)expr;
      // ((System.Func<SourceType, TargetType>)((SourceType _source) => {
      //   if (source.is_Ctor0) {
      //     FormalType f0 = ((Dt_Ctor0)source._D).a0;
      //     ...
      //     return Body0;
      //   } else if (...) {
      //     ...
      //   } else if (true) {
      //     ...
      //   }
      // }))(src)

      string source = ProtectedFreshId("_source");
      ConcreteSyntaxTree w;
      w = CreateLambda(new List<Type>() { e.Source.Type }, e.tok, new List<string>() { source }, e.Type, wr, wStmts);

      if (e.Cases.Count == 0) {
        // the verifier would have proved we never get here; still, we need some code that will compile
        EmitAbsurd(null, w);
      } else {
        int i = 0;
        var sourceType = (UserDefinedType)e.Source.Type.NormalizeExpand();
        foreach (MatchCaseExpr mc in e.Cases) {
          var wCase = MatchCasePrelude(source, sourceType, mc.Ctor, mc.Arguments, i, e.Cases.Count, w);
          EmitReturnExpr(mc.Body, mc.Body.Type, inLetExprBody, wCase);
          i++;
        }
      }
      // We end with applying the source expression to the delegate we just built
      wr.Write(LambdaExecute);
      TrParenExpr(e.Source, wr, inLetExprBody, wStmts);

    } else if (expr is QuantifierExpr) {
      var e = (QuantifierExpr)expr;

      // Compilation does not check whether a quantifier was split.

      wr = CaptureFreeVariables(expr, true, out var su, inLetExprBody, wr, ref wStmts);
      var logicalBody = su.Substitute(e.LogicalBody(true));

      Contract.Assert(e.Bounds != null);  // for non-ghost quantifiers, the resolver would have insisted on finding bounds
      var n = e.BoundVars.Count;
      Contract.Assert(e.Bounds.Count == n);
      var wBody = wr;
      for (int i = 0; i < n; i++) {
        var bound = e.Bounds[i];
        var bv = e.BoundVars[i];

        var collectionElementType = CompileCollection(bound, bv, inLetExprBody, false, su, out var collection, wStmts, e.Bounds, e.BoundVars, i);
        wBody.Write("{0}(", GetQuantifierName(TypeName(collectionElementType, wBody, bv.tok)));
        wBody.Append(collection);
        wBody.Write(", {0}, ", expr is ForallExpr ? True : False);
        var native = AsNativeType(e.BoundVars[i].Type);
        var tmpVarName = ProtectedFreshId(e is ForallExpr ? "_forall_var_" : "_exists_var_");
        ConcreteSyntaxTree newWBody = CreateLambda(new List<Type> { collectionElementType }, e.tok, new List<string> { tmpVarName }, Type.Bool, wBody, wStmts, untyped: true);
        wStmts = newWBody.Fork();
        newWBody = MaybeInjectSubtypeConstraint(
          tmpVarName, collectionElementType, bv.Type,
          inLetExprBody, e.tok, newWBody, true, e is ForallExpr);
        EmitDowncastVariableAssignment(
          IdName(bv), bv.Type, tmpVarName, collectionElementType, true, e.tok, newWBody);
        newWBody = MaybeInjectSubsetConstraint(
          bv, bv.Type, collectionElementType, inLetExprBody, e.tok, newWBody, true, e is ForallExpr);
        wBody.Write(')');
        wBody = newWBody;
      }
      wBody.Append(TrExpr(logicalBody, inLetExprBody, wStmts));

    } else if (expr is SetComprehension) {
      var e = (SetComprehension)expr;
      // For "set i,j,k,l | R(i,j,k,l) :: Term(i,j,k,l)" where the term has type "G", emit something like:
      // ((System.Func<Set<G>>)(() => {
      //   var _coll = new List<G>();
      //   foreach (var tmp_l in sq.Elements) { L l = (L)tmp_l;
      //     foreach (var tmp_k in st.Elements) { K k = (K)tmp_k;
      //       for (BigInteger j = Lo; j < Hi; j++) {
      //         for (bool i in Helper.AllBooleans) {
      //           if (R(i,j,k,l)) {
      //             _coll.Add(Term(i,j,k,l));
      //           }
      //         }
      //       }
      //     }
      //   }
      //   return Dafny.Set<G>.FromCollection(_coll);
      // }))()
      wr = CaptureFreeVariables(e, true, out var su, inLetExprBody, wr, ref wStmts);
      e = (SetComprehension)su.Substitute(e);

      Contract.Assert(e.Bounds != null);  // the resolver would have insisted on finding bounds
      var collectionName = ProtectedFreshId("_coll");
      var bwr = CreateIIFE0(e.Type.AsSetType, e.tok, wr, wStmts);
      wr = bwr;
      EmitSetBuilder_New(wr, e, collectionName);
      var n = e.BoundVars.Count;
      Contract.Assert(e.Bounds.Count == n);
      for (var i = 0; i < n; i++) {
        var bound = e.Bounds[i];
        var bv = e.BoundVars[i];
        var tmpVar = ProtectedFreshId("_compr_");
        var wStmtsLoop = wr.Fork();
        var elementType = CompileCollection(bound, bv, inLetExprBody, true, null, out var collection, wStmtsLoop);
        wr = CreateGuardedForeachLoop(tmpVar, elementType, bv, true, inLetExprBody, e.tok, collection, wr);
      }
      ConcreteSyntaxTree guardWriter;
      var thn = EmitIf(out guardWriter, false, wr);
      guardWriter.Append(TrExpr(e.Range, inLetExprBody, wStmts));
      EmitSetBuilder_Add(e.Type.AsSetType, collectionName, e.Term, inLetExprBody, thn);
      var s = GetCollectionBuilder_Build(e.Type.AsSetType, e.tok, collectionName, wr);
      EmitReturnExpr(s, bwr);

    } else if (expr is MapComprehension) {
      var e = (MapComprehension)expr;
      // For "map i | R(i) :: Term(i)" where the term has type "V" and i has type "U", emit something like:
      // ((System.Func<Map<U, V>>)(() => {
      //   var _coll = new List<Pair<U,V>>();
      //   foreach (L l in sq.Elements) {
      //     foreach (K k in st.Elements) {
      //       for (BigInteger j = Lo; j < Hi; j++) {
      //         for (bool i in Helper.AllBooleans) {
      //           if (R(i,j,k,l)) {
      //             _coll.Add(new Pair(i, Term(i));
      //           }
      //         }
      //       }
      //     }
      //   }
      //   return Dafny.Map<U, V>.FromCollection(_coll);
      // }))()
      wr = CaptureFreeVariables(e, true, out var su, inLetExprBody, wr, ref wStmts);
      e = (MapComprehension)su.Substitute(e);

      Contract.Assert(e.Bounds != null);  // the resolver would have insisted on finding bounds
      var domtypeName = TypeName(e.Type.AsMapType.Domain, wr, e.tok);
      var rantypeName = TypeName(e.Type.AsMapType.Range, wr, e.tok);
      var collection_name = ProtectedFreshId("_coll");
      var bwr = CreateIIFE0(e.Type.AsMapType, e.tok, wr, wStmts);
      wr = bwr;
      EmitMapBuilder_New(wr, e, collection_name);
      var n = e.BoundVars.Count;
      Contract.Assert(e.Bounds.Count == n);
      for (var i = 0; i < n; i++) {
        var bound = e.Bounds[i];
        var bv = e.BoundVars[i];
        var tmpVar = ProtectedFreshId("_compr_");
        var wStmtsLoop = wr.Fork();
        var elementType = CompileCollection(bound, bv, inLetExprBody, true, null, out var collection, wStmtsLoop);
        wr = CreateGuardedForeachLoop(tmpVar, elementType, bv, true, false, bv.tok, collection, wr);
      }
      ConcreteSyntaxTree guardWriter;
      var thn = EmitIf(out guardWriter, false, wr);
      guardWriter.Append(TrExpr(e.Range, inLetExprBody, wStmts));
      var termLeftWriter = EmitMapBuilder_Add(e.Type.AsMapType, e.tok, collection_name, e.Term, inLetExprBody, thn);
      if (e.TermLeft == null) {
        Contract.Assert(e.BoundVars.Count == 1);
        termLeftWriter.Write(IdName(e.BoundVars[0]));
      } else {
        termLeftWriter.Append(TrExpr(e.TermLeft, inLetExprBody, wStmts));
      }

      var s = GetCollectionBuilder_Build(e.Type.AsMapType, e.tok, collection_name, wr);
      EmitReturnExpr(s, bwr);

    } else if (expr is LambdaExpr) {
      var e = (LambdaExpr)expr;

      wr = CaptureFreeVariables(e, false, out var su, inLetExprBody, wr, ref wStmts);
      wr = CreateLambda(e.BoundVars.ConvertAll(bv => bv.Type), Token.NoToken, e.BoundVars.ConvertAll(IdName), e.Body.Type, wr, wStmts);
      wStmts = wr.Fork();
      wr = EmitReturnExpr(wr);
      // May need an upcast or boxing conversion to coerce to the generic arrow result type
      wr = EmitCoercionIfNecessary(e.Body.Type, TypeForCoercion(e.Type.AsArrowType.Result), e.Body.tok, wr);
      wr.Append(TrExpr(su.Substitute(e.Body), inLetExprBody, wStmts));
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      wr.Append(TrExpr(e.E, inLetExprBody, wStmts));

    } else if (expr is ITEExpr) {
      var e = (ITEExpr)expr;
      EmitITE(e.Test, e.Thn, e.Els, e.Type, inLetExprBody, wr, wStmts);

    } else if (expr is ConcreteSyntaxExpression) {
      var e = (ConcreteSyntaxExpression)expr;
      return TrExpr(e.ResolvedExpression, inLetExprBody, wStmts);

    } else {
      Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
    }

    return wr;
  }
}

public class CoverageInstrumenter {
  private readonly ConcreteSinglePassCompiler compiler;
  private List<(IToken, string)>/*?*/ legend;  // non-null implies DafnyOptions.O.CoverageLegendFile is non-null

  public CoverageInstrumenter(ConcreteSinglePassCompiler compiler) {
    this.compiler = compiler;
    if (DafnyOptions.O.CoverageLegendFile != null) {
      legend = new List<(IToken, string)>();
    }
  }

  public bool IsRecording {
    get => legend != null;
  }

  public void Instrument(IToken tok, string description, ConcreteSyntaxTree wr) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    Contract.Requires(wr != null || !IsRecording);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.Record({0})", legend.Count);
      compiler.EndStmt(wr);
      legend.Add((tok, description));
    }
  }

  public void UnusedInstrumentationPoint(IToken tok, string description) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    if (legend != null) {
      legend.Add((tok, description));
    }
  }

  public void InstrumentExpr(IToken tok, string description, bool resultValue, ConcreteSyntaxTree wr) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    Contract.Requires(wr != null || !IsRecording);
    if (legend != null) {
      // The "Record" call always returns "true", so we negate it to get the value "false"
      wr.Write("{1}DafnyProfiling.CodeCoverage.Record({0})", legend.Count, resultValue ? "" : "!");
      legend.Add((tok, description));
    }
  }

  /// <summary>
  /// Should be called once "n" has reached its final value
  /// </summary>
  public void EmitSetup(ConcreteSyntaxTree wr) {
    Contract.Requires(wr != null);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.Setup({0})", legend.Count);
      compiler.EndStmt(wr);
    }
  }

  public void EmitTearDown(ConcreteSyntaxTree wr) {
    Contract.Requires(wr != null);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.TearDown()");
      compiler.EndStmt(wr);
    }
  }

  public void WriteLegendFile() {
    if (legend != null) {
      var filename = DafnyOptions.O.CoverageLegendFile;
      Contract.Assert(filename != null);
      TextWriter wr = filename == "-" ? System.Console.Out : new StreamWriter(new FileStream(Path.GetFullPath(filename), System.IO.FileMode.Create));
      {
        for (var i = 0; i < legend.Count; i++) {
          var e = legend[i];
          wr.WriteLine("{0}: {1}({2},{3}): {4}", i, e.Item1.Filename, e.Item1.line, e.Item1.col, e.Item2);
        }
      }
      legend = null;
    }
  }
}