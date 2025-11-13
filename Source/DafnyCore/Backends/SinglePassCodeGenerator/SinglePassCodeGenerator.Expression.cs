//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using DafnyCore;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using static Microsoft.Dafny.GeneratorErrors;

namespace Microsoft.Dafny.Compilers {
  public abstract partial class SinglePassCodeGenerator {

    public virtual Type GetRuntimeType(Type tpe) {
      return tpe.GetRuntimeType();
    }

    public virtual void EmitExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      switch (expr) {
        case LiteralExpr literalExpr: {
            LiteralExpr e = literalExpr;
            EmitLiteralExpr(wr, e);
            break;
          }
        case ThisExpr: {
            if (thisContext != null) {
              var instantiatedType = expr.Type.Subst(thisContext.ParentFormalTypeParametersToActuals);
              var contextType = UserDefinedType.FromTopLevelDecl(expr.Origin, thisContext);
              if (contextType.ResolvedClass is ClassLikeDecl { NonNullTypeDecl: { } } cls) {
                contextType = UserDefinedType.FromTopLevelDecl(expr.Origin, cls.NonNullTypeDecl);
              }

              wr = EmitCoercionIfNecessary(contextType, instantiatedType, expr.Origin, wr);
            }

            EmitThis(wr);
            break;
          }
        case IdentifierExpr identifierExpr: {
            var e = identifierExpr;
            if (inLetExprBody && !(e.Var is BoundVar)) {
              // copy variable to a temp since
              //   - C# doesn't allow out param in letExpr body, and
              //   - Java doesn't allow any non-final variable in letExpr body.
              var name = ProtectedFreshId("_pat_let_tv");
              EmitIdentifier(name, wr);
              DeclareLocalVar(name, null, null, false, IdName(e.Var), copyInstrWriters.Peek(), e.Type);
            } else {
              EmitIdentifier(IdName(e.Var), wr);
            }

            break;
          }
        case SetDisplayExpr displayExpr: {
            var e = displayExpr;
            EmitCollectionDisplay(e.Type.NormalizeToAncestorType().AsSetType, e.Origin, e.Elements, inLetExprBody, wr, wStmts);
            break;
          }
        case MultiSetDisplayExpr displayExpr: {
            var e = displayExpr;
            EmitCollectionDisplay(e.Type.NormalizeToAncestorType().AsMultiSetType, e.Origin, e.Elements, inLetExprBody, wr,
              wStmts);
            break;
          }
        case SeqDisplayExpr displayExpr: {
            var e = displayExpr;
            EmitCollectionDisplay(e.Type.NormalizeToAncestorType().AsSeqType, e.Origin, e.Elements, inLetExprBody, wr, wStmts);
            break;
          }
        case MapDisplayExpr displayExpr: {
            var e = displayExpr;
            EmitMapDisplay(e.Type.NormalizeToAncestorType().AsMapType, e.Origin, e.Elements, inLetExprBody, wr, wStmts);
            break;
          }
        case MemberSelectExpr selectExpr: {
            MemberSelectExpr e = selectExpr;
            if (e.Member is Field field and (ConstantField or SpecialField)) {
              string preStr;
              string postStr;
              if (field is SpecialField specialField) {
                GetSpecialFieldInfo(specialField.SpecialId, specialField.IdParam, e.Obj.Type, out var compiledName, out preStr,
                  out postStr);
              } else {
                preStr = "";
                postStr = "";
              }
              wr.Write(preStr);

              if (field.IsStatic && !SupportsStaticsInGenericClasses && field.EnclosingClass.TypeArgs.Count != 0) {
                var typeArgs = e.TypeApplicationAtEnclosingClass;
                Contract.Assert(typeArgs.Count == field.EnclosingClass.TypeArgs.Count);
                wr.Write("{0}.", TypeName_Companion(e.Obj.Type, wr, e.Origin, field));
                EmitNameAndActualTypeArgs(IdName(e.Member), typeArgs, e.Origin, null, false, wr);
                var tas = TypeArgumentInstantiation.ListFromClass(field.EnclosingClass, typeArgs);
                EmitTypeDescriptorsActuals(tas, e.Origin, wr.ForkInParens());
              } else {
                // Special handling for static special fields (like fp64.NaN)
                if (field.IsStatic && field is SpecialField && preStr != "") {
                  // GetSpecialFieldInfo already provided the complete reference in preStr
                } else {
                  void WriteObj(ConcreteSyntaxTree w) {
                    if (field.IsStatic) {
                      w.Write("{0}", TypeName_Companion(e.Obj.Type, w, e.Origin, field));
                    } else {
                      w = EmitCoercionIfNecessary(e.Obj.Type, UserDefinedType.UpcastToMemberEnclosingType(e.Obj.Type, e.Member),
                        e.Origin, w);
                      TrParenExpr(e.Obj, w, inLetExprBody, wStmts);
                    }
                  }

                  var typeArgs = CombineAllTypeArguments(e.Member, e.TypeApplicationAtEnclosingClass,
                    e.TypeApplicationJustMember);
                  EmitMemberSelect(WriteObj, e.Obj.Type, e.Member, typeArgs, e.TypeArgumentSubstitutionsWithParents(),
                    selectExpr.Type).EmitRead(wr);
                }
              }

              wr.Write(postStr);
            } else {
              var typeArgs =
                CombineAllTypeArguments(e.Member, e.TypeApplicationAtEnclosingClass, e.TypeApplicationJustMember);
              var typeMap = e.TypeArgumentSubstitutionsWithParents();
              var customReceiver = NeedsCustomReceiverNotTrait(e.Member);
              if (!customReceiver && !e.Member.IsStatic) {
                Action<ConcreteSyntaxTree> obj;
                // The eta conversion here is to avoid capture of the receiver, because the call to EmitMemberSelect below may generate
                // a lambda expression in the target language.
                if (e.Member is Function && typeArgs.Count != 0) {
                  // need to eta-expand wrap the receiver
                  var etaReceiver = ProtectedFreshId("_eta_this");
                  wr = CreateIIFE_ExprBody(etaReceiver, e.Obj.Type, e.Obj.Origin, e.Obj, inLetExprBody, e.Type.Subst(typeMap),
                    e.Origin, wr, ref wStmts);
                  obj = w => EmitIdentifier(etaReceiver, w);
                } else {
                  obj = w => EmitExpr(e.Obj, inLetExprBody, w, wStmts);
                }

                EmitMemberSelect(obj, e.Obj.Type, e.Member, typeArgs, typeMap, selectExpr.Type).EmitRead(wr);
              } else {
                string customReceiverName = null;
                if (customReceiver && e.Member is Function) {
                  // need to eta-expand wrap the receiver
                  customReceiverName = ProtectedFreshId("_eta_this");
                  wr = CreateIIFE_ExprBody(customReceiverName, e.Obj.Type, e.Obj.Origin, e.Obj, inLetExprBody,
                    e.Type.Subst(typeMap), e.Origin, wr, ref wStmts);
                }

                Action<ConcreteSyntaxTree> obj = w => EmitTypeName_Companion(e.Obj.Type, w, wr, e.Origin, e.Member);
                EmitMemberSelect(obj, e.Obj.Type, e.Member, typeArgs, typeMap, selectExpr.Type, customReceiverName).EmitRead(wr);
              }
            }

            break;
          }
        case SeqSelectExpr selectExpr: {
            SeqSelectExpr e = selectExpr;
            Contract.Assert(e.Seq.Type != null);
            if (e.Seq.Type.IsArrayType) {
              if (e.SelectOne) {
                Contract.Assert(e.E0 != null && e.E1 == null);
                var w = EmitArraySelect([e.E0], e.Type, inLetExprBody, wr, wStmts);
                w = EmitCoercionIfNecessary(
                  e.Seq.Type,
                  e.Seq.Type.IsNonNullRefType || !e.Seq.Type.IsRefType
                    ? null
                    : UserDefinedType.CreateNonNullType((UserDefinedType)e.Seq.Type.NormalizeExpand()),
                  e.Origin,
                  w
                );
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

            break;
          }
        case SeqConstructionExpr constructionExpr: {
            var e = constructionExpr;
            EmitSeqConstructionExpr(e, inLetExprBody, wr, wStmts);
            break;
          }
        case MultiSetFormingExpr formingExpr: {
            var e = formingExpr;
            EmitMultiSetFormingExpr(e, inLetExprBody, wr, wStmts);
            break;
          }
        case MultiSelectExpr selectExpr: {
            MultiSelectExpr e = selectExpr;
            WriteCast(TypeName(e.Type.NormalizeExpand(), wr, e.Origin), wr);
            var w = EmitArraySelect(e.Indices, e.Type, inLetExprBody, wr, wStmts);
            TrParenExpr(e.Array, w, inLetExprBody, wStmts);
            break;
          }
        case SeqUpdateExpr updateExpr: {
            SeqUpdateExpr e = updateExpr;
            var collectionType = e.Type.NormalizeToAncestorType().AsCollectionType;
            Contract.Assert(collectionType != null);
            EmitIndexCollectionUpdate(e.Seq, e.Index, e.Value, collectionType, inLetExprBody, wr, wStmts);
            break;
          }
        case DatatypeUpdateExpr updateExpr: {
            var e = updateExpr;
            if (e.Members.All(member => member.IsGhost)) {
              // all fields to be updated are ghost, which doesn't change the value
              EmitExpr(e.Root, inLetExprBody, wr, wStmts);
              return;
            }

            if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, e.Root.Type.AsDatatype, out var dtor)) {
              var i = e.Members.IndexOf(dtor);
              if (0 <= i) {
                // the datatype is an erasable wrapper and its core destructor is part of the update (which implies everything else must be a ghost),
                // so proceed as with the rhs
                Contract.Assert(Enumerable.Range(0, e.Members.Count).All(j => j == i || e.Members[j].IsGhost));
                Contract.Assert(e.Members.Count == e.Updates.Count);
                var rhs = e.Updates[i].Item3;
                EmitExpr(rhs, inLetExprBody, wr, wStmts);
                return;
              }
            }

            // the optimized cases don't apply, so proceed according to the desugaring
            EmitExpr(e.ResolvedExpression, inLetExprBody, wr, wStmts);
            break;
          }
        case FunctionCallExpr callExpr: {
            FunctionCallExpr e = callExpr;

            void EmitExpr(Expression e2, ConcreteSyntaxTree wr2, bool inLetExpr, ConcreteSyntaxTree wStmts2) {
              this.EmitExpr(e2, inLetExpr, wr2, wStmts2);
            }

            if (e.Function is SpecialFunction) {
              CompileSpecialFunctionCallExpr(e, wr, inLetExprBody, wStmts, EmitExpr);
            } else {
              CompileFunctionCallExpr(e, wr, inLetExprBody, wStmts, EmitExpr);
            }

            break;
          }
        case ApplyExpr applyExpr: {
            var e = applyExpr;
            EmitApplyExpr(e.Function.Type, e.Origin, e.Function, e.Args, inLetExprBody, wr, wStmts);
            break;
          }
        case DatatypeValue value: {
            var dtv = value;
            Contract.Assert(dtv.Ctor != null); // since dtv has been successfully resolved

            if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dtv.Ctor.EnclosingDatatype, out var dtor)) {
              var i = dtv.Ctor.Destructors.IndexOf(dtor);
              Contract.Assert(0 <= i);
              EmitExpr(dtv.Arguments[i], inLetExprBody, wr, wStmts);
              return;
            }

            var wrArgumentList = new ConcreteSyntaxTree();
            var wTypeDescriptorArguments = new ConcreteSyntaxTree();
            var typeSubst = TypeParameter.SubstitutionMap(dtv.Ctor.EnclosingDatatype.TypeArgs, dtv.InferredTypeArgs);
            string sep = "";
            Contract.Assert(dtv.Ctor.EnclosingDatatype.TypeArgs.Count == dtv.InferredTypeArgs.Count);
            WriteTypeDescriptors(dtv.Ctor.EnclosingDatatype, dtv.InferredTypeArgs, wTypeDescriptorArguments, ref sep);
            sep = "";
            for (var i = 0; i < dtv.Arguments.Count; i++) {
              var formal = dtv.Ctor.Formals[i];
              if (!formal.IsGhost) {
                wrArgumentList.Write(sep);
                var w = EmitCoercionIfNecessary(from: dtv.Arguments[i].Type, to: dtv.Ctor.Formals[i].Type.Subst(typeSubst),
                  toOrig: dtv.Ctor.Formals[i].Type, tok: dtv.Origin, wr: wrArgumentList);
                EmitExpr(dtv.Arguments[i], inLetExprBody, w, wStmts);
                sep = ", ";
              }
            }

            EmitDatatypeValue(dtv, wTypeDescriptorArguments.ToString(), wrArgumentList.ToString(), wr);
            break;
          }
        case OldExpr:
          Contract.Assert(false);
          throw new Cce.UnreachableException(); // 'old' is always a ghost
        case UnaryOpExpr opExpr: {
            var e = opExpr;
            if (e.ResolvedOp == UnaryOpExpr.ResolvedOpcode.BVNot) {
              wr = EmitBitvectorTruncation(e.Type.NormalizeToAncestorType().AsBitVectorType, e.Type.AsNativeType(), true,
                wr);
            }

            EmitUnaryExpr(UnaryOpCodeMap[e.ResolvedOp], e.E, inLetExprBody, wr, wStmts);
            break;
          }
        case ConversionExpr conversionExpr: {
            var e = conversionExpr;
            var fromType = GetRuntimeType(e.E.Type);
            var toType = GetRuntimeType(e.ToType);
            Contract.Assert(Options.Get(CommonOptionBag.GeneralTraits) != CommonOptionBag.GeneralTraitsOptions.Legacy ||
                            toType.IsRefType == fromType.IsRefType ||
                            (fromType.IsTypeParameter && toType.IsTraitType));
            if (toType.IsRefType || toType.IsTraitType || fromType.IsTraitType) {
              var w = EmitCoercionIfNecessary(e.E.Type, e.ToType, e.Origin, wr);
              w = EmitDowncastIfNecessary(e.E.Type, e.ToType, e.Origin, w);
              EmitExpr(e.E, inLetExprBody, w, wStmts);
            } else if (e.E.Type.IsSubtypeOf(e.ToType, false, false)) {
              // conversion is a no-op -- almost, because it may need a cast to deal with bounded type parameters
              var w = EmitDowncastIfNecessary(e.E.Type, e.ToType, e.Origin, wr);
              EmitExpr(e.E, inLetExprBody, w, wStmts);
            } else {
              EmitConversionExpr(e.E, fromType, toType, inLetExprBody, wr, wStmts);
            }

            break;
          }
        case TypeTestExpr typeTestExpr:
          CompileTypeTest(typeTestExpr, inLetExprBody, wr, ref wStmts);
          break;
        case BinaryExpr binary:
          EmitBinaryExpr(inLetExprBody, wr, wStmts, binary);
          break;
        case TernaryExpr:
          Contract.Assume(false); // currently, none of the ternary expressions is compilable
          break;
        case LetExpr letExpr: {
            var e = letExpr;
            if (e.Exact) {
              // The Dafny "let" expression
              //    var Pattern(x,y) := G; E
              // is translated into C# as:
              //    LamLet(G, tmp =>
              //      LamLet(dtorX(tmp), x =>
              //      LamLet(dtorY(tmp), y => E)))
              Contract.Assert(e.LHSs.Count == e.RHSs.Count); // checked by resolution
              var w = wr;
              for (int i = 0; i < e.LHSs.Count; i++) {
                var lhs = e.LHSs[i];
                if (Contract.Exists(lhs.Vars, bv => !bv.IsGhost)) {
                  var rhsName = $"_pat_let{GetUniqueAstNumber(e)}_{i}";
                  w = CreateIIFE_ExprBody(rhsName, e.RHSs[i].Type, e.RHSs[i].Origin, e.RHSs[i], inLetExprBody, e.Body.Type,
                    e.Body.Origin, w, ref wStmts);
                  w = TrCasePattern(lhs, wr => EmitIdentifier(rhsName, wr), e.RHSs[i].Type, e.Body.Type, w, ref wStmts);
                }
              }

              EmitExpr(e.Body, true, w, wStmts);
            } else if (e.BoundVars.All(bv => bv.IsGhost)) {
              // The Dafny "let" expression
              //    ghost var x,y :| Constraint; E
              // is compiled just like E is, because the resolver has already checked that x,y (or other ghost variables, for that matter) don't
              // occur in E (moreover, the verifier has checked that values for x,y satisfying Constraint exist).
              EmitExpr(e.Body, inLetExprBody, wr, wStmts);
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
              Contract.Assert(e.RHSs.Count == 1); // checked by resolution
              var missingBounds = BoolBoundedPool.MissingBounds(e.BoundVars.ToList<BoundVar>(), e.Constraint_Bounds,
                BoundedPool.PoolVirtues.Enumerable);
              if (missingBounds.Count != 0) {
                foreach (var bv in missingBounds) {
                  Error(ErrorId.c_let_such_that_is_too_complex, e.Origin, wr,
                    "this let-such-that expression is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}'",
                    bv.Name);
                }
              } else {
                var w = CreateIIFE1(0, e.Body.Type, e.Body.Origin, "_let_dummy_" + GetUniqueAstNumber(e), wr, wStmts);
                foreach (var bv in e.BoundVars) {
                  DeclareLocalVar(IdName(bv), bv.Type, bv.Origin, false, ForcePlaceboValue(bv.Type, wr, bv.Origin, true), w);
                }

                TrAssignSuchThat(new List<IVariable>(e.BoundVars).ConvertAll(bv => (IVariable)bv), e.RHSs[0],
                  e.Constraint_Bounds, w, inLetExprBody);
                EmitReturnExpr(e.Body, e.Body.Type, true, w);
              }
            }

            break;
          }
        case NestedMatchExpr nestedMatchExpr:
          EmitNestedMatchExpr(nestedMatchExpr, inLetExprBody, wr, wStmts);
          break;
        case MatchExpr matchExpr:
          EmitMatchExpr(matchExpr, inLetExprBody, wr, wStmts);
          break;
        case QuantifierExpr quantifierExpr: {
            var e = quantifierExpr;

            // Compilation does not check whether a quantifier was split.

            wr = CaptureFreeVariables(quantifierExpr, true, out var su, inLetExprBody, wr, ref wStmts);
            var logicalBody = su.Substitute(e.LogicalBody(true));

            Contract.Assert(e.Bounds !=
                            null); // for non-ghost quantifiers, the resolver would have insisted on finding bounds
            var n = e.BoundVars.Count;
            Contract.Assert(e.Bounds.Count == n);
            var wBody = wr;
            for (int i = 0; i < n; i++) {
              var bound = e.Bounds[i];
              var bv = e.BoundVars[i];

              var collectionElementType = CompileCollection(bound, bv, inLetExprBody, false, su, out var collection,
            out var newtypeConversionsWereExplicit, wStmts,
                e.Bounds, e.BoundVars, i);
              wBody = EmitQuantifierExpr(collection, quantifierExpr is ForallExpr, collectionElementType, bv, wBody);
              var native = AsNativeType(e.BoundVars[i].Type);
              var tmpVarName = ProtectedFreshId(e is ForallExpr ? "_forall_var_" : "_exists_var_");
              ConcreteSyntaxTree newWBody = CreateLambda([collectionElementType], e.Origin,
                [tmpVarName], Type.Bool, wBody, wStmts, untyped: true);
              wStmts = newWBody.Fork();
              newWBody = MaybeInjectSubtypeConstraintWrtTraits(
                tmpVarName, collectionElementType, bv.Type,
                inLetExprBody, e.Origin, newWBody, true, e is ForallExpr);
              EmitDowncastVariableAssignment(
                IdName(bv), bv.Type, tmpVarName, collectionElementType, true, e.Origin, newWBody);
              newWBody = MaybeInjectSubsetConstraint(
                bv, bv.Type, inLetExprBody, e.Origin, newWBody, newtypeConversionsWereExplicit, isReturning: true, elseReturnValue: e is ForallExpr);
              wBody = newWBody;
            }

            EmitExpr(logicalBody, inLetExprBody, wBody, wStmts);
            break;
          }
        case SetComprehension comprehension: {
            var e = comprehension;
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
            // We also split R(i,j,k,l) to evaluate it as early as possible.
            wr = CaptureFreeVariables(e, true, out var su, inLetExprBody, wr, ref wStmts);
            e = (SetComprehension)su.Substitute(e);

            Contract.Assert(e.Bounds != null); // the resolver would have insisted on finding bounds
            var collectionName = ProtectedFreshId("_coll");
            var setType = e.Type.NormalizeToAncestorType().AsSetType;
            var bwr = CreateIIFE0(setType, e.Origin, wr, wStmts);
            wStmts = bwr.Fork();
            wr = bwr;
            EmitSetBuilder_New(wr, e, collectionName);
            var n = e.BoundVars.Count;
            Contract.Assert(e.Bounds.Count == n);
            var processedBounds = new HashSet<IVariable>();
            List<(Expression conj, ISet<IVariable> frees)> unusedConjuncts = Expression.Conjuncts(e.Range)
              .Select(conj => (conj, ModuleResolver.FreeVariables(conj))).ToList();
            unusedConjuncts.ForEach(entry => entry.frees.IntersectWith(e.BoundVars));
            wr = EmitGuardFragment(unusedConjuncts, processedBounds, wr);
            for (var i = 0; i < n; i++) {
              var bound = e.Bounds[i];
              var bv = e.BoundVars[i];
              processedBounds.Add(bv);
              var tmpVar = ProtectedFreshId("_compr_");
              var wStmtsLoop = wr.Fork();
              var elementType = CompileCollection(bound, bv, inLetExprBody, true, null, out var collection, out var newtypeConversionsWereExplicit, wStmtsLoop);
              wr = CreateGuardedForeachLoop(tmpVar, elementType, bv, newtypeConversionsWereExplicit, true, inLetExprBody, e.Origin, collection, wr);
              wr = EmitGuardFragment(unusedConjuncts, processedBounds, wr);
            }

            EmitSetBuilder_Add(setType, collectionName, e.Term, inLetExprBody, wr);
            var returned = EmitReturnExpr(bwr);
            GetCollectionBuilder_Build(setType, e.Origin, collectionName, returned, wStmts);
            break;
          }
        case MapComprehension comprehension: {
            var e = comprehension;
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
            // We also split R(i,j,k,l) to evaluate it as early as possible.
            wr = CaptureFreeVariables(e, true, out var su, inLetExprBody, wr, ref wStmts);
            e = (MapComprehension)su.Substitute(e);

            Contract.Assert(e.Bounds != null); // the resolver would have insisted on finding bounds
            var mapType = e.Type.NormalizeToAncestorType().AsMapType;
            var domtypeName = TypeName(mapType.Domain, wr, e.Origin);
            var rantypeName = TypeName(mapType.Range, wr, e.Origin);
            var collection_name = ProtectedFreshId("_coll");
            var bwr = CreateIIFE0(mapType, e.Origin, wr, wStmts);
            wStmts = bwr.Fork();
            wr = bwr;
            EmitMapBuilder_New(wr, e, collection_name);
            var n = e.BoundVars.Count;
            Contract.Assert(e.Bounds.Count == n);
            var processedBounds = new HashSet<IVariable>();
            List<(Expression conj, ISet<IVariable> frees)> unusedConjuncts = Expression.Conjuncts(e.Range)
              .Select(conj => (conj, ModuleResolver.FreeVariables(conj))).ToList();
            unusedConjuncts.ForEach(entry => entry.frees.IntersectWith(e.BoundVars));
            wr = EmitGuardFragment(unusedConjuncts, processedBounds, wr);
            for (var i = 0; i < n; i++) {
              var bound = e.Bounds[i];
              var bv = e.BoundVars[i];
              processedBounds.Add(bv);
              var tmpVar = ProtectedFreshId("_compr_");
              var wStmtsLoop = wr.Fork();
              var elementType = CompileCollection(bound, bv, inLetExprBody, true, null, out var collection, out var newtypeConversionsWereExplicit, wStmtsLoop);
              wr = CreateGuardedForeachLoop(tmpVar, elementType, bv, newtypeConversionsWereExplicit, true, false, bv.Origin, collection, wr);
              wr = EmitGuardFragment(unusedConjuncts, processedBounds, wr);
            }

            var termLeftWriter = EmitMapBuilder_Add(mapType, e.Origin, collection_name, e.Term, inLetExprBody, wr);
            if (e.TermLeft == null) {
              Contract.Assert(e.BoundVars.Count == 1);
              EmitIdentifier(IdName(e.BoundVars[0]), termLeftWriter);
            } else {
              EmitExpr(e.TermLeft, inLetExprBody, termLeftWriter, wStmts);
            }

            var returned = EmitReturnExpr(bwr);
            GetCollectionBuilder_Build(mapType, e.Origin, collection_name, returned, wStmts);
            break;
          }
        case LambdaExpr lambdaExpr: {
            var e = lambdaExpr;

            IVariable receiver = null;
            if (thisContext != null && (enclosingMethod is { IsTailRecursive: true } || enclosingFunction is { IsTailRecursive: true })) {
              var name = ProtectedFreshId("_this");
              var ty = ModuleResolver.GetThisType(e.Origin, thisContext);
              receiver = new LocalVariable(SourceOrigin.NoToken, name, ty, false) {
                type = ty
              };
              var _this = new ThisExpr(thisContext);
              wr = EmitBetaRedex([IdName(receiver)], [_this],
                [_this.Type], lambdaExpr.Type, lambdaExpr.Origin, inLetExprBody, wr, ref wStmts);
            }

            wr = CaptureFreeVariables(e, false, out var su, inLetExprBody, wr, ref wStmts);
            if (receiver != null) {
              su = new Substituter(new IdentifierExpr(e.Origin, receiver), su.substMap, su.typeMap);
            }

            wr = CreateLambda(e.BoundVars.ConvertAll(bv => bv.Type), Token.NoToken, e.BoundVars.ConvertAll(IdName),
              e.Body.Type, wr, wStmts);
            wStmts = wr.Fork();
            wr = EmitReturnExpr(wr);
            // May need an upcast or boxing conversion to coerce to the generic arrow result type
            wr = EmitCoercionIfNecessary(e.Body.Type, TypeForCoercion(e.Type.AsArrowType.Result), e.Body.Origin, wr);
            EmitExpr(su.Substitute(e.Body), inLetExprBody, wr, wStmts);
            break;
          }
        case StmtExpr stmtExpr: {
            var e = stmtExpr;
            EmitExpr(e.E, inLetExprBody, wr, wStmts);
            break;
          }
        case ITEExpr iteExpr: {
            var e = iteExpr;
            // The ghost-ITE optimization applies only to at "the top" of the expression structure of a function
            // body. Those cases are handled in TrExprOpt, so we expect the be compiling both branches here.
            Contract.Assert(e.HowToCompile == ITEExpr.ITECompilation.CompileBothBranches);
            EmitITE(e.Test, e.Thn, e.Els, e.Type, inLetExprBody, wr, wStmts);
            break;
          }
        case ConcreteSyntaxExpression expression: {
            var e = expression;
            EmitExpr(e.ResolvedExpression, inLetExprBody, wr, wStmts);
            break;
          }
        default:
          Contract.Assert(false);
          throw new Cce.UnreachableException(); // unexpected expression
      }

      ConcreteSyntaxTree EmitGuardFragment(List<(Expression conj, ISet<IVariable> frees)> unusedConjuncts,
        HashSet<IVariable> processedBounds, ConcreteSyntaxTree wr) {
        Expression localGuard = Expression.CreateBoolLiteral(expr.Origin, true);

        foreach (var entry in unusedConjuncts.ToList().Where(entry => entry.frees.IsSubsetOf(processedBounds))) {
          localGuard = Expression.CreateAnd(localGuard, entry.conj);
          unusedConjuncts.Remove(entry);
        }

        if (!LiteralExpr.IsTrue(localGuard)) {
          wr = EmitIf(out var guardWriter, false, wr);
          EmitExpr(localGuard, inLetExprBody, guardWriter, wStmts);
        }

        return wr;
      }
    }

    private void EmitBinaryExpr(bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts, BinaryExpr binary) {
      if (IsComparisonToZero(binary, out var arg, out var sign, out var negated) &&
          CompareZeroUsingSign(arg.Type)) {
        // Transform e.g. x < BigInteger.Zero into x.Sign == -1
        var w = EmitSign(arg.Type, wr);
        TrParenExpr(arg, w, inLetExprBody, wStmts);
        wr.Write(negated ? " != " : " == ");
        wr.Write(sign.ToString());
      } else {
        CompileBinOp(binary.ResolvedOp, binary.E0.Type, binary.E1.Type, binary.Origin, GetRuntimeType(binary.Type),
          out var opString,
          out var preOpString,
          out var postOpString,
          out var callString,
          out var staticCallString,
          out var reverseArguments,
          out var truncateResult,
          out var convertE1_to_int,
          out var coerceE1,
          wr);

        if (truncateResult && binary.Type.NormalizeToAncestorType().AsBitVectorType is { } bitvectorType) {
          wr = EmitBitvectorTruncation(bitvectorType, binary.Type.AsNativeType(), true, wr);
        }

        var e0 = reverseArguments ? binary.E1 : binary.E0;
        var e1 = reverseArguments ? binary.E0 : binary.E1;

        var left = Expr(e0, inLetExprBody, wStmts);
        ConcreteSyntaxTree right;
        if (convertE1_to_int) {
          right = ExprAsNativeInt(e1, inLetExprBody, wStmts);
        } else {
          right = Expr(e1, inLetExprBody, wStmts);
          if (coerceE1) {
            right = CoercionIfNecessary(e1.Type, TypeForCoercion(e1.Type), e1.Origin, right);
          }
        }

        EmitBinaryExprUsingConcreteSyntax(wr, binary.Type, preOpString, opString, left, right, callString, staticCallString, postOpString);
      }
    }

    protected void EmitBinaryExprUsingConcreteSyntax(ConcreteSyntaxTree wr, Type resultType, string preOpString,
      string opString, ICanRender left, ICanRender right, string callString, string staticCallString,
      string postOpString) {
      wr.Write(preOpString);
      if (opString != null) {
        var nativeType = AsNativeType(resultType);
        string nativeName = null;
        bool needsCast = false;
        if (nativeType != null) {
          GetNativeInfo(nativeType.Sel, out nativeName, out _, out needsCast);
        }

        var opResult = ConcreteSyntaxTree.Create($"{left.InParens()} {opString} {right.InParens()}");
        if (needsCast) {
          opResult = Cast(new LineSegment(nativeName), opResult);
        }

        wr.Append(opResult);
      } else if (callString != null) {
        wr.Format($"{left.InParens()}.{callString}({right})");
      } else if (staticCallString != null) {
        wr.Format($"{staticCallString}({left}, {right})");
      }

      wr.Write(postOpString);
    }

    private void EmitMatchExpr(MatchExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
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

      EmitLambdaApply(wr, out var wLambda, out var wArg);

      string source = ProtectedFreshId("_source");
      ConcreteSyntaxTree w;
      w = CreateLambda([e.Source.Type], e.Origin, [source], e.Type, wLambda,
        wStmts);

      if (e.Cases.Count == 0) {
        // the verifier would have proved we never get here; still, we need some code that will compile
        EmitAbsurd(null, w);
      } else {
        int i = 0;
        var sourceType = (UserDefinedType)e.Source.Type.NormalizeExpand();
        foreach (MatchCaseExpr mc in e.Cases) {
          var wCase = MatchCasePrelude(source, sourceType, mc.Ctor, mc.Arguments, i, e.Cases.Count, w);
          var continuation = new OptimizedExpressionContinuation(EmitReturnExpr, false);
          TrExprOpt(mc.Body, mc.Body.Type, wCase, wStmts, inLetExprBody: true, accumulatorVar: null, continuation);
          i++;
        }
      }

      // We end with applying the source expression to the delegate we just built
      EmitExpr(e.Source, inLetExprBody, wArg, wStmts);
    }

    protected virtual void EmitNestedMatchExpr(NestedMatchExpr match, bool inLetExprBody, ConcreteSyntaxTree output, ConcreteSyntaxTree wStmts) {
      var lambdaBody = EmitAppliedLambda(output, wStmts, match.Origin, match.Type);
      var continuation = new OptimizedExpressionContinuation(EmitReturnExpr, false);
      TrOptNestedMatchExpr(match, match.Type, lambdaBody, wStmts, inLetExprBody, null, continuation);
    }

    protected virtual void TrOptNestedMatchExpr(NestedMatchExpr match, Type resultType, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts, bool inLetExprBody, IVariable accumulatorVar, OptimizedExpressionContinuation continuation) {

      wStmts = wr.Fork();

      EmitNestedMatchGeneric(match, continuation.PreventCaseFallThrough, (caseIndex, caseBody) => {
        var myCase = match.Cases[caseIndex];
        TrExprOpt(myCase.Body, myCase.Body.Type, caseBody, wStmts, inLetExprBody, accumulatorVar: null, continuation);
      }, inLetExprBody, wr);
    }

    private ConcreteSyntaxTree EmitAppliedLambda(ConcreteSyntaxTree output, ConcreteSyntaxTree wStmts,
      IOrigin token, Type resultType) {
      EmitLambdaApply(output, out var lambdaApplyTarget, out _);
      return CreateLambda([], token, [], resultType, lambdaApplyTarget, wStmts);
    }
  }
}
