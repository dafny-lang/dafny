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
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public partial class Translator {
    /// <summary>
    /// Instances of WFContext are used as an argument to CheckWellformed, supplying options for the
    /// checks to be performed.
    /// If "SelfCallsAllowance" is non-null, termination checks will be omitted for calls that look
    /// like it.  This is useful in function postconditions, where the result of the function is
    /// syntactically given as what looks like a recursive call with the same arguments.
    /// "DoReadsChecks" indicates whether or not to perform reads checks.  If so, the generated code
    /// will make references to $_Frame.  If "saveReadsChecks" is true, then the reads checks will
    /// be recorded but postponsed.  In particular, CheckWellformed will append to .Locals a list of
    /// fresh local variables and will append to .Assert assertions with appropriate error messages
    /// that can be used later.  As a convenience, the ProcessSavedReadsChecks will make use of .Locals
    /// and .Asserts (and AssignLocals) and update a given StmtListBuilder.
    /// "LValueContext" indicates that the expression checked for well-formedness is an L-value of
    /// some assignment.
    /// </summary>
    private class WFOptions {
      public readonly Function SelfCallsAllowance;
      public readonly bool DoReadsChecks;
      public readonly bool DoOnlyCoarseGrainedTerminationChecks; // termination checks don't look at decreases clause, but reports errors for any intra-SCC call (this is used in default-value expressions)
      public readonly List<Bpl.Variable> Locals;
      public readonly List<Bpl.Cmd> Asserts;
      public readonly bool LValueContext;
      public readonly Bpl.QKeyValue AssertKv;

      public WFOptions() {
      }

      public WFOptions(Function selfCallsAllowance, bool doReadsChecks, bool saveReadsChecks = false, bool doOnlyCoarseGrainedTerminationChecks = false) {
        Contract.Requires(!saveReadsChecks || doReadsChecks);  // i.e., saveReadsChecks ==> doReadsChecks
        SelfCallsAllowance = selfCallsAllowance;
        DoReadsChecks = doReadsChecks;
        DoOnlyCoarseGrainedTerminationChecks = doOnlyCoarseGrainedTerminationChecks;
        if (saveReadsChecks) {
          Locals = new List<Variable>();
          Asserts = new List<Bpl.Cmd>();
        }
      }

      public WFOptions(Bpl.QKeyValue kv) {
        AssertKv = kv;
      }

      /// <summary>
      /// This constructor clones the given "options", but turns off reads checks.  (I wish C# allowed
      /// me to name the constructor something to indicate this semantics in its name.  Sigh.)
      /// </summary>
      public WFOptions(WFOptions options) {
        Contract.Requires(options != null);
        SelfCallsAllowance = options.SelfCallsAllowance;
        DoReadsChecks = false;  // so just leave .Locals and .Asserts as null
        DoOnlyCoarseGrainedTerminationChecks = options.DoOnlyCoarseGrainedTerminationChecks;
        LValueContext = options.LValueContext;
        AssertKv = options.AssertKv;
      }

      /// <summary>
      /// This constructor clones the given "options", but sets "LValueContext" to "lValueContext".
      /// (I wish C# allowed me to name the constructor something to indicate this semantics in its name.  Sigh.)
      /// </summary>
      public WFOptions(bool lValueContext, WFOptions options) {
        Contract.Requires(options != null);
        SelfCallsAllowance = options.SelfCallsAllowance;
        DoReadsChecks = options.DoReadsChecks;
        DoOnlyCoarseGrainedTerminationChecks = options.DoOnlyCoarseGrainedTerminationChecks;
        Locals = options.Locals;
        Asserts = options.Asserts;
        LValueContext = lValueContext;
        AssertKv = options.AssertKv;
      }

      public Action<IToken, Bpl.Expr, PODesc.ProofObligationDescription, Bpl.QKeyValue> AssertSink(Translator tran, BoogieStmtListBuilder builder) {
        return (t, e, d, qk) => {
          if (Locals != null) {
            var b = BplLocalVar(tran.CurrentIdGenerator.FreshId("b$reqreads#"), Bpl.Type.Bool, Locals);
            Asserts.Add(tran.Assert(t, b, d, qk));
            builder.Add(Bpl.Cmd.SimpleAssign(e.tok, (Bpl.IdentifierExpr)b, e));
          } else {
            builder.Add(tran.Assert(t, e, d, qk));
          }
        };
      }

      public List<Bpl.AssignCmd> AssignLocals {
        get {
          return Map(Locals, l =>
            Bpl.Cmd.SimpleAssign(l.tok,
              new Bpl.IdentifierExpr(Token.NoToken, l),
              Bpl.Expr.True)
            );
        }
      }

      public void ProcessSavedReadsChecks(List<Variable> locals, BoogieStmtListBuilder builderInitializationArea, BoogieStmtListBuilder builder) {
        Contract.Requires(locals != null);
        Contract.Requires(builderInitializationArea != null);
        Contract.Requires(builder != null);
        Contract.Requires(Locals != null && Asserts != null);  // ProcessSavedReadsChecks should be called only if the constructor was called with saveReadsChecks

        // var b$reads_guards#0 : bool  ...
        locals.AddRange(Locals);
        // b$reads_guards#0 := true   ...
        foreach (var cmd in AssignLocals) {
          builderInitializationArea.Add(cmd);
        }
        // assert b$reads_guards#0;  ...
        foreach (var a in Asserts) {
          builder.Add(a);
        }
      }
    }

    void CheckWellformedAndAssume(Expression expr, WFOptions options, List<Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type != null && expr.Type.IsBoolType);
      Contract.Requires(options != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
            // WF[e0]; assume e0; WF[e1]; assume e1;
            CheckWellformedAndAssume(e.E0, options, locals, builder, etran);
            CheckWellformedAndAssume(e.E1, options, locals, builder, etran);
            return;
          case BinaryExpr.ResolvedOpcode.Imp: {
              // if (*) {
              //   WF[e0]; assume e0; WF[e1]; assume e1;
              // } else {
              //   assume e0 ==> e1;
              // }
              var bAnd = new BoogieStmtListBuilder(this);
              CheckWellformedAndAssume(e.E0, options, locals, bAnd, etran);
              CheckWellformedAndAssume(e.E1, options, locals, bAnd, etran);
              var bImp = new BoogieStmtListBuilder(this);
              bImp.Add(TrAssumeCmd(expr.tok, etran.TrExpr(expr)));
              builder.Add(new Bpl.IfCmd(expr.tok, null, bAnd.Collect(expr.tok), null, bImp.Collect(expr.tok)));
            }
            return;
          case BinaryExpr.ResolvedOpcode.Or: {
              // if (*) {
              //   WF[e0]; assume e0;
              // } else {
              //   assume !e0;
              //   WF[e1]; assume e1;
              // }
              var b0 = new BoogieStmtListBuilder(this);
              CheckWellformedAndAssume(e.E0, options, locals, b0, etran);
              var b1 = new BoogieStmtListBuilder(this);
              b1.Add(TrAssumeCmd(expr.tok, Bpl.Expr.Not(etran.TrExpr(e.E0))));
              CheckWellformedAndAssume(e.E1, options, locals, b1, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, null, b0.Collect(expr.tok), null, b1.Collect(expr.tok)));
            }
            return;
          default:
            break;
        }
      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        // if (*) {
        //   WF[test]; assume test;
        //   WF[thn]; assume thn;
        // } else {
        //   assume !test;
        //   WF[els]; assume els;
        // }
        var bThn = new BoogieStmtListBuilder(this);
        CheckWellformedAndAssume(e.Test, options, locals, bThn, etran);
        CheckWellformedAndAssume(e.Thn, options, locals, bThn, etran);
        var bEls = new BoogieStmtListBuilder(this);
        bEls.Add(TrAssumeCmd(expr.tok, Bpl.Expr.Not(etran.TrExpr(e.Test))));
        CheckWellformedAndAssume(e.Els, options, locals, bEls, etran);
        builder.Add(new Bpl.IfCmd(expr.tok, null, bThn.Collect(expr.tok), null, bEls.Collect(expr.tok)));
        return;
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        // For (Q x :: body(x)), introduce fresh local variable x'.  Then:
        //   havoc x'
        //   WF[body(x')]; assume body(x');
        // If the quantifier is universal, then continue as:
        //   assume (\forall x :: body(x));

        // Create local variables corresponding to the bound variables:
        var substMap = SetupBoundVarsAsLocals(e.BoundVars, builder, locals, etran);
        // Get the body of the quantifier and suitably substitute for the type variables and bound variables
        var body = Substitute(e.LogicalBody(true), null, substMap);
        CheckWellformedAndAssume(body, options, locals, builder, etran);

        if (e is ForallExpr) {
          // Although we do the WF check on the original quantifier, we assume the split one.
          // This ensures that cases like forall x :: x != null && f(x.a) do not fail to verify.
          builder.Add(TrAssumeCmd(expr.tok, etran.TrExpr(e.SplitQuantifierExpression ?? e)));
        }
        return;
      }

      // resort to the behavior of simply checking well-formedness followed by assuming the translated expression
      CheckWellformed(expr, options, locals, builder, etran);

      // NOTE: If the CheckWellformed call above found a split quantifier, it ignored
      //       the splitting and proceeded to decompose the full quantifier as
      //       normal. This call to TrExpr, on the other hand, will indeed use the
      //       split quantifier.
      builder.Add(TrAssumeCmd(expr.tok, etran.TrExpr(expr)));
    }

    /// <summary>
    /// Check the well-formedness of "expr" (but don't leave hanging around any assumptions that affect control flow)
    /// </summary>
    void CheckWellformed(Expression expr, WFOptions options, List<Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      CheckWellformedWithResult(expr, options, null, null, locals, builder, etran);
    }

    /// <summary>
    /// Adds to "builder" code that checks the well-formedness of "expr".  Any local variables introduced
    /// in this code are added to "locals".
    /// If "result" is non-null, then after checking the well-formedness of "expr", the generated code will
    /// assume the equivalent of "result == expr".
    /// See class WFOptions for descriptions of the specified options.
    /// </summary>
    void CheckWellformedWithResult(Expression expr, WFOptions options, Bpl.Expr result, Type resultType,
                                   List<Bpl.Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      Contract.Requires((result == null) == (resultType == null));
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      var origOptions = options;
      if (options.LValueContext) {
        // Turn off LValueContext for any recursive call
        options = new WFOptions(false, options);
      }

      if (expr is StaticReceiverExpr stexpr) {
        if (stexpr.ObjectToDiscard != null) {
          CheckWellformedWithResult(stexpr.ObjectToDiscard, options, null, null, locals, builder, etran);
        }
      } else if (expr is LiteralExpr) {
        CheckResultToBeInType(expr.tok, expr, expr.Type, locals, builder, etran);
      } else if (expr is ThisExpr || expr is WildcardExpr || expr is BoogieWrapper) {
        // always allowed
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        if (!origOptions.LValueContext) {
          CheckDefiniteAssignment(e, builder);
        }
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Contract.Assert(e.Type is CollectionType);
        var elementType = ((CollectionType)e.Type).Arg;
        foreach (Expression el in e.Elements) {
          CheckWellformed(el, options, locals, builder, etran);
          CheckSubrange(el.tok, etran.TrExpr(el), el.Type, elementType, builder);
        }
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        Contract.Assert(e.Type is MapType);
        var keyType = ((MapType)e.Type).Domain;
        var valType = ((MapType)e.Type).Range;
        foreach (ExpressionPair p in e.Elements) {
          CheckWellformed(p.A, options, locals, builder, etran);
          CheckSubrange(p.A.tok, etran.TrExpr(p.A), p.A.Type, keyType, builder);
          CheckWellformed(p.B, options, locals, builder, etran);
          CheckSubrange(p.B.tok, etran.TrExpr(p.B), p.B.Type, valType, builder);
        }
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        CheckFunctionSelectWF("naked function", builder, etran, e, " Possible solution: eta expansion.");
        CheckWellformed(e.Obj, options, locals, builder, etran);
        if (e.Obj.Type.IsRefType) {
          if (inBodyInitContext && Expression.AsThis(e.Obj) != null && !e.Member.IsInstanceIndependentConstant) {
            // this uses the surrogate local
            if (!origOptions.LValueContext) {
              CheckDefiniteAssignmentSurrogate(expr.tok, (Field)e.Member, false, builder);
            }
          } else {
            CheckNonNull(expr.tok, e.Obj, builder, etran, options.AssertKv);
            // Check that the receiver is available in the state in which the dereference occurs
          }
        } else if (e.Member is DatatypeDestructor dtor) {
          var correctConstructor = BplOr(dtor.EnclosingCtors.ConvertAll(
            ctor => FunctionCall(e.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Obj))));
          if (dtor.EnclosingCtors.Count == dtor.EnclosingCtors[0].EnclosingDatatype.Ctors.Count) {
            // Every constructor has this destructor; might as well assume that here.
            builder.Add(TrAssumeCmd(expr.tok, correctConstructor));
          } else {
            builder.Add(Assert(GetToken(expr), correctConstructor,
              new PODesc.DestructorValid(dtor.Name, dtor.EnclosingCtorNames("or"))));
          }
          CheckNotGhostVariant(e, "destructor", dtor.EnclosingCtors, builder, etran);
        } else if (e.Member is DatatypeDiscriminator discriminator) {
          CheckNotGhostVariant(e, "discriminator", ((DatatypeDecl)discriminator.EnclosingClass).Ctors, builder, etran);
        }
        if (!e.Member.IsStatic) {
          if (e.Member is TwoStateFunction) {
            Bpl.Expr wh = GetWhereClause(expr.tok, etran.TrExpr(e.Obj), e.Obj.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
            if (wh != null) {
              var desc = new PODesc.IsAllocated("receiver argument", "in the two-state function's previous state");
              builder.Add(Assert(GetToken(expr), wh, desc));
            }
          } else if (etran.UsesOldHeap) {
            Bpl.Expr wh = GetWhereClause(expr.tok, etran.TrExpr(e.Obj), e.Obj.Type, etran, ISALLOC, true);
            if (wh != null) {
              var desc = new PODesc.IsAllocated("receiver",
                $"in the state in which its {(e.Member is Field ? "fields" : "members")} are accessed");
              builder.Add(Assert(GetToken(expr), wh, desc));
            }
          }
        }
        if (options.DoReadsChecks && e.Member is Field && ((Field)e.Member).IsMutable) {
          options.AssertSink(this, builder)(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), etran.TrExpr(e.Obj), GetField(e)),
            new PODesc.FrameSubset("read field", false), options.AssertKv);
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        var eSeqType = e.Seq.Type.NormalizeExpand();
        bool isSequence = eSeqType is SeqType;
        CheckWellformed(e.Seq, options, locals, builder, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        if (eSeqType.IsArrayType) {
          builder.Add(Assert(GetToken(e.Seq), Bpl.Expr.Neq(seq, predef.Null), new PODesc.NonNull("array")));
          if (!CommonHeapUse || etran.UsesOldHeap) {
            builder.Add(Assert(GetToken(e.Seq), MkIsAlloc(seq, eSeqType, etran.HeapExpr), new PODesc.IsAllocated("array", null)));
          }
        }
        Bpl.Expr e0 = null;
        if (eSeqType is MapType) {
          bool finite = ((MapType)eSeqType).Finite;
          e0 = etran.TrExpr(e.E0);
          CheckWellformed(e.E0, options, locals, builder, etran);
          var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
          Bpl.Expr inDomain = FunctionCall(expr.tok, f, predef.MapType(e.tok, finite, predef.BoxType, predef.BoxType), seq);
          inDomain = Bpl.Expr.Select(inDomain, BoxIfNecessary(e.tok, e0, e.E0.Type));
          builder.Add(Assert(GetToken(expr), inDomain, new PODesc.ElementInDomain(), options.AssertKv));
        } else if (eSeqType is MultiSetType) {
          // cool

        } else {
          if (e.E0 != null) {
            e0 = etran.TrExpr(e.E0);
            CheckWellformed(e.E0, options, locals, builder, etran);
            var desc = new PODesc.InRange(e.SelectOne ? "index" : "lower bound");
            builder.Add(Assert(GetToken(expr), InSeqRange(expr.tok, e0, e.E0.Type, seq, isSequence, null, !e.SelectOne), desc, options.AssertKv));
          }
          if (e.E1 != null) {
            CheckWellformed(e.E1, options, locals, builder, etran);
            Bpl.Expr lowerBound;
            if (e0 != null && e.E0.Type.IsBitVectorType) {
              lowerBound = ConvertExpression(e.E0.tok, e0, e.E0.Type, Type.Int);
            } else {
              lowerBound = e0;
            }
            builder.Add(Assert(GetToken(expr), InSeqRange(expr.tok, etran.TrExpr(e.E1), e.E1.Type, seq, isSequence, lowerBound, true), new PODesc.SequenceSelectRangeValid(isSequence ? "sequence" : "array"), options.AssertKv));
          }
        }
        if (options.DoReadsChecks && eSeqType.IsArrayType) {
          if (e.SelectOne) {
            Contract.Assert(e.E0 != null);
            var i = etran.TrExpr(e.E0);
            i = ConvertExpression(expr.tok, i, e.E0.Type, Type.Int);
            Bpl.Expr fieldName = FunctionCall(expr.tok, BuiltinFunction.IndexField, null, i);
            options.AssertSink(this, builder)(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), seq, fieldName),
              new PODesc.FrameSubset("read array element", false), options.AssertKv);
          } else {
            Bpl.Expr lowerBound = e.E0 == null ? Bpl.Expr.Literal(0) : etran.TrExpr(e.E0);
            Contract.Assert(eSeqType.AsArrayType.Dims == 1);
            Bpl.Expr upperBound = e.E1 == null ? ArrayLength(e.tok, seq, 1, 0) : etran.TrExpr(e.E1);
            // check that, for all i in lowerBound..upperBound, a[i] is in the frame
            Bpl.BoundVariable iVar = new Bpl.BoundVariable(e.tok, new Bpl.TypedIdent(e.tok, "$i", Bpl.Type.Int));
            Bpl.IdentifierExpr i = new Bpl.IdentifierExpr(e.tok, iVar);
            var range = BplAnd(Bpl.Expr.Le(lowerBound, i), Bpl.Expr.Lt(i, upperBound));
            var fieldName = FunctionCall(e.tok, BuiltinFunction.IndexField, null, i);
            var allowedToRead = Bpl.Expr.SelectTok(e.tok, etran.TheFrame(e.tok), seq, fieldName);
            var trigger = BplTrigger(allowedToRead); // Note, the assertion we're about to produce only seems useful in the check-only mode (that is, with subsumption 0), but if it were to be assumed, we'll use this entire RHS as the trigger
            var qq = new Bpl.ForallExpr(e.tok, new List<Variable> { iVar }, trigger, BplImp(range, allowedToRead));
            options.AssertSink(this, builder)(expr.tok, qq,
              new PODesc.FrameSubset("read the indicated range of array elements", false),
              options.AssertKv);
          }
        }
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        CheckWellformed(e.Array, options, locals, builder, etran);
        Bpl.Expr array = etran.TrExpr(e.Array);
        builder.Add(Assert(GetToken(e.Array), Bpl.Expr.Neq(array, predef.Null), new PODesc.NonNull("array")));
        if (!CommonHeapUse || etran.UsesOldHeap) {
          builder.Add(Assert(GetToken(e.Array), MkIsAlloc(array, e.Array.Type, etran.HeapExpr), new PODesc.IsAllocated("array", null)));
        }
        for (int idxId = 0; idxId < e.Indices.Count; idxId++) {
          var idx = e.Indices[idxId];
          CheckWellformed(idx, options, locals, builder, etran);

          var index = etran.TrExpr(idx);
          index = ConvertExpression(idx.tok, index, idx.Type, Type.Int);
          var lower = Bpl.Expr.Le(Bpl.Expr.Literal(0), index);
          var length = ArrayLength(idx.tok, array, e.Indices.Count, idxId);
          var upper = Bpl.Expr.Lt(index, length);
          var tok = idx is IdentifierExpr ? e.tok : idx.tok; // TODO: Reusing the token of an identifier expression would underline its definition. but this is still not perfect.

          var desc = new PODesc.InRange($"index {idxId}");
          builder.Add(Assert(tok, Bpl.Expr.And(lower, upper), desc, options.AssertKv));
        }
        if (options.DoReadsChecks) {
          Bpl.Expr fieldName = etran.GetArrayIndexFieldName(e.tok, e.Indices);
          options.AssertSink(this, builder)(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), array, fieldName),
            new PODesc.FrameSubset("read array element", false), options.AssertKv);
        }
      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        CheckWellformed(e.Seq, options, locals, builder, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        Bpl.Expr index = etran.TrExpr(e.Index);
        Bpl.Expr value = etran.TrExpr(e.Value);
        var collectionType = (CollectionType)e.Seq.Type.NormalizeExpand();
        // validate index
        CheckWellformed(e.Index, options, locals, builder, etran);
        if (collectionType is SeqType) {
          var desc = new PODesc.InRange("index");
          builder.Add(Assert(GetToken(e.Index), InSeqRange(expr.tok, index, e.Index.Type, seq, true, null, false), desc, options.AssertKv));
        } else {
          CheckSubrange(e.Index.tok, index, e.Index.Type, collectionType.Arg, builder);
        }
        // validate value
        CheckWellformed(e.Value, options, locals, builder, etran);
        if (collectionType is SeqType) {
          CheckSubrange(e.Value.tok, value, e.Value.Type, collectionType.Arg, builder);
        } else if (collectionType is MapType mapType) {
          CheckSubrange(e.Value.tok, value, e.Value.Type, mapType.Range, builder);
        } else if (collectionType is MultiSetType) {
          var desc = new PODesc.NonNegative("new number of occurrences");
          builder.Add(Assert(GetToken(e.Value), Bpl.Expr.Le(Bpl.Expr.Literal(0), value), desc, options.AssertKv));
        } else {
          Contract.Assert(false);
        }
      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        int arity = e.Args.Count;
        var tt = e.Function.Type.AsArrowType;
        Contract.Assert(tt != null);
        Contract.Assert(tt.Arity == arity);

        // check WF of receiver and arguments
        CheckWellformed(e.Function, options, locals, builder, etran);
        foreach (Expression arg in e.Args) {
          CheckWellformed(arg, options, locals, builder, etran);
        }

        // check subranges of arguments
        for (int i = 0; i < arity; ++i) {
          CheckSubrange(e.Args[i].tok, etran.TrExpr(e.Args[i]), e.Args[i].Type, tt.Args[i], builder);
        }

        // check parameter availability
        if (etran.UsesOldHeap) {
          Bpl.Expr wh = GetWhereClause(e.Function.tok, etran.TrExpr(e.Function), e.Function.Type, etran, ISALLOC, true);
          if (wh != null) {
            var desc = new PODesc.IsAllocated("function", "in the state in which the function is invoked");
            builder.Add(Assert(GetToken(e.Function), wh, desc));
          }
          for (int i = 0; i < e.Args.Count; i++) {
            Expression ee = e.Args[i];
            wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
            if (wh != null) {
              var desc = new PODesc.IsAllocated("argument", "in the state in which the function is invoked");
              builder.Add(Assert(GetToken(ee), wh, desc));
            }
          }
        }

        // translate arguments to requires and reads
        Func<Expression, Bpl.Expr> TrArg = arg => {
          Bpl.Expr inner = etran.TrExpr(arg);
          if (ModeledAsBoxType(arg.Type)) {
            return inner;
          } else {
            return FunctionCall(arg.tok, BuiltinFunction.Box, null, inner);
          }
        };

        var args = Concat(
          Map(tt.TypeArgs, TypeToTy),
          Cons(etran.HeapExpr,
          Cons(etran.TrExpr(e.Function),
          e.Args.ConvertAll(arg => TrArg(arg)))));

        // Because type inference often gravitates towards inferring non-constrained types, we'll
        // do some digging on our own to see if we can discover a more precise type.
        var fnCore = e.Function;
        while (true) {
          var prevCore = fnCore;
          fnCore = Expression.StripParens(fnCore.Resolved);
          if (object.ReferenceEquals(fnCore, prevCore)) {
            break;  // we've done what we can do
          }
        }
        Type fnCoreType;
        if (fnCore is IdentifierExpr) {
          var v = (IdentifierExpr)fnCore;
          fnCoreType = v.Var.Type;
        } else if (fnCore is MemberSelectExpr) {
          var m = (MemberSelectExpr)fnCore;
          fnCoreType = m.Member is Field ? ((Field)m.Member).Type : ((Function)m.Member).GetMemberType((ArrowTypeDecl)tt.ResolvedClass);
        } else {
          fnCoreType = fnCore.Type;
        }

        if (!fnCoreType.IsArrowTypeWithoutPreconditions) {
          // check precond
          var precond = FunctionCall(e.tok, Requires(arity), Bpl.Type.Bool, args);
          builder.Add(Assert(GetToken(expr), precond, new PODesc.PreconditionSatisfied(null)));
        }

        if (options.DoReadsChecks && !fnCoreType.IsArrowTypeWithoutReadEffects) {
          // check read effects
          Type objset = new SetType(true, program.BuiltIns.ObjectQ());
          Expression wrap = new BoogieWrapper(
            FunctionCall(e.tok, Reads(arity), TrType(objset), args),
            objset);
          var reads = new FrameExpression(e.RangeToken, wrap, null);
          CheckFrameSubset(expr.tok, new List<FrameExpression> { reads }, null, null,
            etran, options.AssertSink(this, builder), new PODesc.FrameSubset("invoke function", false), options.AssertKv);
        }

      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
        if (e.Function is SpecialFunction) {
          CheckWellformedSpecialFunction(e, options, null, null, locals, builder, etran);
        } else {
          // check well-formedness of receiver
          CheckWellformed(e.Receiver, options, locals, builder, etran);
          if (!e.Function.IsStatic && !(e.Receiver is ThisExpr) && !e.Receiver.Type.IsArrowType) {
            CheckNonNull(expr.tok, e.Receiver, builder, etran, options.AssertKv);
          } else if (e.Receiver.Type.IsArrowType) {
            CheckFunctionSelectWF("function specification", builder, etran, e.Receiver, "");
          }
          if (!e.Function.IsStatic && CommonHeapUse && !etran.UsesOldHeap) {
            // the argument can't be assumed to be allocated for the old heap
            Type et = UserDefinedType.FromTopLevelDecl(e.RangeToken, e.Function.EnclosingClass).Subst(e.GetTypeArgumentSubstitutions());
            builder.Add(new Bpl.CommentCmd("assume allocatedness for receiver argument to function"));
            builder.Add(TrAssumeCmd(e.Receiver.tok, MkIsAlloc(etran.TrExpr(e.Receiver), et, etran.HeapExpr)));
          }
          // check well-formedness of the other parameters
          foreach (Expression arg in e.Args) {
            if (!(arg is DefaultValueExpression)) {
              CheckWellformed(arg, options, locals, builder, etran);
            }
          }
          // create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
          Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
          for (int i = 0; i < e.Function.Formals.Count; i++) {
            Formal p = e.Function.Formals[i];
            // Note, in the following, the "##" makes the variable invisible in BVD.  An alternative would be to communicate
            // to BVD what this variable stands for and display it as such to the user.
            Type et = p.Type.Subst(e.GetTypeArgumentSubstitutions());
            LocalVariable local = new LocalVariable(p.RangeToken, "##" + p.Name, et, p.IsGhost);
            local.type = local.OptionalType;  // resolve local here
            IdentifierExpr ie = new IdentifierExpr(local.RangeToken, local.AssignUniqueName(currentDeclaration.IdGenerator));
            ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
            substMap.Add(p, ie);
            locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type))));
            Bpl.IdentifierExpr lhs = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
            Expression ee = e.Args[i];
            CheckSubrange(ee.tok, etran.TrExpr(ee), ee.Type, et, builder);
            Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(p.tok, lhs, CondApplyBox(p.tok, etran.TrExpr(ee), cce.NonNull(ee.Type), et));
            builder.Add(cmd);
            if (CommonHeapUse && !etran.UsesOldHeap) {
              // the argument can't be assumed to be allocated for the old heap
              builder.Add(new Bpl.CommentCmd("assume allocatedness for argument to function"));
              builder.Add(TrAssumeCmd(e.Args[i].tok, MkIsAlloc(lhs, et, etran.HeapExpr)));
            }
          }

          // Check that every parameter is available in the state in which the function is invoked; this means checking that it has
          // the right type and is allocated.  These checks usually hold trivially, on account of that the Dafny language only gives
          // access to expressions of the appropriate type and that are allocated in the current state.  However, if the function is
          // invoked in the 'old' state or if the function invoked is a two-state function with a non-new parameter, then we need to
          // check that its arguments were all available at that time as well.
          if (etran.UsesOldHeap) {
            if (!e.Function.IsStatic) {
              Bpl.Expr wh = GetWhereClause(e.Receiver.tok, etran.TrExpr(e.Receiver), e.Receiver.Type, etran, ISALLOC, true);
              if (wh != null) {
                var desc = new PODesc.IsAllocated("receiver argument", "in the state in which the function is invoked");
                builder.Add(Assert(GetToken(e.Receiver), wh, desc));
              }
            }
            for (int i = 0; i < e.Args.Count; i++) {
              Expression ee = e.Args[i];
              Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
              if (wh != null) {
                var desc = new PODesc.IsAllocated("argument", "in the state in which the function is invoked");
                builder.Add(Assert(GetToken(ee), wh, desc));
              }
            }
          } else if (e.Function is TwoStateFunction) {
            if (!e.Function.IsStatic) {
              Bpl.Expr wh = GetWhereClause(e.Receiver.tok, etran.TrExpr(e.Receiver), e.Receiver.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
              if (wh != null) {
                var desc = new PODesc.IsAllocated("receiver argument", "in the two-state function's previous state");
                builder.Add(Assert(GetToken(e.Receiver), wh, desc));
              }
            }
            Contract.Assert(e.Function.Formals.Count == e.Args.Count);
            for (int i = 0; i < e.Args.Count; i++) {
              var formal = e.Function.Formals[i];
              if (formal.IsOld) {
                Expression ee = e.Args[i];
                Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
                if (wh != null) {
                  var pIdx = e.Args.Count == 1 ? "" : " at index " + i;
                  var desc = new PODesc.IsAllocated($"argument{pIdx} ('{formal.Name}')", "in the two-state function's previous state");
                  builder.Add(Assert(GetToken(ee), wh, desc));
                }
              }
            }
          }
          // check that the preconditions for the call hold
          foreach (AttributedExpression p in e.Function.Req) {
            Expression precond = Substitute(p.E, e.Receiver, substMap, e.GetTypeArgumentSubstitutions());
            bool splitHappened;  // we don't actually care
            string errorMessage = CustomErrorMessage(p.Attributes);
            foreach (var ss in TrSplitExpr(precond, etran, true, out splitHappened)) {
              if (ss.IsChecked) {
                var tok = new NestedToken(GetToken(expr), ss.Tok);
                var desc = new PODesc.PreconditionSatisfied(errorMessage);
                if (options.AssertKv != null) {
                  // use the given assert attribute only
                  builder.Add(Assert(tok, ss.E, new PODesc.PreconditionSatisfied(errorMessage), options.AssertKv));
                } else {
                  builder.Add(AssertNS(tok, ss.E, new PODesc.PreconditionSatisfied(errorMessage)));
                }
              }
            }
            if (options.AssertKv == null) {
              // assume only if no given assert attribute is given
              builder.Add(TrAssumeCmd(expr.tok, etran.TrExpr(precond)));
            }
          }
          if (options.DoReadsChecks) {
            // check that the callee reads only what the caller is already allowed to read
            var s = new Substituter(null, new Dictionary<IVariable, Expression>(), e.GetTypeArgumentSubstitutions());
            CheckFrameSubset(expr.tok,
              e.Function.Reads.ConvertAll(s.SubstFrameExpr),
              e.Receiver, substMap, etran, options.AssertSink(this, builder), new PODesc.FrameSubset("invoke function", false), options.AssertKv);
          }

          Bpl.Expr allowance = null;
          if (codeContext != null && e.CoCall != FunctionCallExpr.CoCallResolution.Yes && !(e.Function is ExtremePredicate)) {
            // check that the decreases measure goes down
            var calleeSCCLookup = e.IsByMethodCall ? (ICallable)e.Function.ByMethodDecl : e.Function;
            Contract.Assert(calleeSCCLookup != null);
            if (ModuleDefinition.InSameSCC(calleeSCCLookup, codeContext)) {
              if (options.DoOnlyCoarseGrainedTerminationChecks) {
                builder.Add(Assert(GetToken(expr), Bpl.Expr.False, new PODesc.IsNonRecursive()));
              } else {
                List<Expression> contextDecreases = codeContext.Decreases.Expressions;
                List<Expression> calleeDecreases = e.Function.Decreases.Expressions;
                if (e.Function == options.SelfCallsAllowance) {
                  allowance = Bpl.Expr.True;
                  if (!e.Function.IsStatic) {
                    allowance = BplAnd(allowance, Bpl.Expr.Eq(etran.TrExpr(e.Receiver), new Bpl.IdentifierExpr(e.tok, etran.This)));
                  }
                  for (int i = 0; i < e.Args.Count; i++) {
                    Expression ee = e.Args[i];
                    Formal ff = e.Function.Formals[i];
                    allowance = BplAnd(allowance,
                      Bpl.Expr.Eq(etran.TrExpr(ee),
                        new Bpl.IdentifierExpr(e.tok, ff.AssignUniqueName(currentDeclaration.IdGenerator), TrType(ff.Type))));
                  }
                }
                string hint;
                switch (e.CoCall) {
                  case FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasSideEffects:
                    hint = "note that only functions without side effects can be called co-recursively";
                    break;
                  case FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasPostcondition:
                    hint = "note that only functions without any ensures clause can be called co-recursively";
                    break;
                  case FunctionCallExpr.CoCallResolution.NoBecauseIsNotGuarded:
                    hint = "note that the call is not sufficiently guarded to be used co-recursively";
                    break;
                  case FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsAreNotAllowedInThisContext:
                    hint = "note that calls cannot be co-recursive in this context";
                    break;
                  case FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsInDestructiveContext:
                    hint = "note that a call can be co-recursive only if all intra-cluster calls are in non-destructive contexts";
                    break;
                  case FunctionCallExpr.CoCallResolution.No:
                    hint = null;
                    break;
                  default:
                    Contract.Assert(false); // unexpected CoCallResolution
                    goto case FunctionCallExpr.CoCallResolution.No; // please the compiler
                }
                if (e.CoCallHint != null) {
                  hint = hint == null ? e.CoCallHint : string.Format("{0}; {1}", hint, e.CoCallHint);
                }
                CheckCallTermination(expr.tok, contextDecreases, calleeDecreases, allowance, e.Receiver, substMap, e.GetTypeArgumentSubstitutions(),
                  etran, etran, builder, codeContext.InferredDecreases, hint);
              }
            }
          }
          // all is okay, so allow this function application access to the function's axiom, except if it was okay because of the self-call allowance.
          Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, e.Function.FullSanitizedName + "#canCall", Bpl.Type.Bool);
          List<Bpl.Expr> args = etran.FunctionInvocationArguments(e, null);
          Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(GetToken(expr), new Bpl.FunctionCall(canCallFuncID), args);
          builder.Add(TrAssumeCmd(expr.tok, allowance == null ? canCallFuncAppl : Bpl.Expr.Or(allowance, canCallFuncAppl)));

          var returnType = e.Type.AsDatatype;
          if (returnType != null && returnType.Ctors.Count == 1) {
            var correctConstructor = FunctionCall(e.tok, returnType.Ctors[0].QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e));
            // There is only one constructor, so the value must be been constructed by it; might as well assume that here.
            builder.Add(TrAssumeCmd(expr.tok, correctConstructor));
          }
        }
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
          var formal = dtv.Ctor.Formals[i];
          var arg = dtv.Arguments[i];
          if (!(arg is DefaultValueExpression)) {
            CheckWellformed(arg, options, locals, builder, etran);
          }
          // Cannot use the datatype's formals, so we substitute the inferred type args:
          var su = new Dictionary<TypeParameter, Type>();
          foreach (var p in LinqExtender.Zip(dtv.Ctor.EnclosingDatatype.TypeArgs, dtv.InferredTypeArgs)) {
            su[p.Item1] = p.Item2;
          }
          Type ty = formal.Type.Subst(su);
          CheckSubrange(arg.tok, etran.TrExpr(arg), arg.Type, ty, builder);
        }
      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        CheckWellformed(e.N, options, locals, builder, etran);
        var desc = new PODesc.NonNegative("sequence size");
        builder.Add(Assert(GetToken(e.N), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.N)), desc));

        CheckWellformed(e.Initializer, options, locals, builder, etran);
        var eType = e.Type.AsSeqType.Arg;
        CheckElementInit(e.RangeToken, false, new List<Expression>() { e.N }, eType, e.Initializer, null, builder, etran, options);
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        // Anything read inside the 'old' expressions depends only on the old heap, which isn't included in the
        // frame axiom.  In other words, 'old' expressions have no dependencies on the current heap.  Therefore,
        // we turn off any reads checks for "e.E".
        CheckWellformed(e.E, new WFOptions(options), locals, builder, etran.OldAt(e.AtLabel));
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        foreach (var fe in e.Frame) {
          CheckWellformed(fe.E, options, locals, builder, etran);

          EachReferenceInFrameExpression(fe.E, locals, builder, etran, out var description, out var ty, out var r, out var ante);
          Bpl.Expr nonNull;
          if (ty.IsNonNullRefType) {
            nonNull = Bpl.Expr.True;
          } else {
            Contract.Assert(ty.IsRefType);
            nonNull = Bpl.Expr.Neq(r, predef.Null);
            builder.Add(Assert(GetToken(fe.E), BplImp(ante, nonNull), new PODesc.NonNull(description, description != "object")));
          }
          // check that "r" was allocated in the "e.AtLabel" state
          Bpl.Expr wh = GetWhereClause(fe.E.tok, r, ty, etran.OldAt(e.AtLabel), ISALLOC, true);
          if (wh != null) {
            var desc = new PODesc.IsAllocated(description, "in the old-state of the 'unchanged' predicate",
              description != "object");
            builder.Add(Assert(GetToken(fe.E), BplImp(BplAnd(ante, nonNull), wh), desc));
          }
          // check that the 'unchanged' argument reads only what the context is allowed to read
          if (options.DoReadsChecks) {
            CheckFrameSubset(fe.E.tok,
              new List<FrameExpression>() { fe },
              null, new Dictionary<IVariable, Expression>(), etran, options.AssertSink(this, builder),
              new PODesc.FrameSubset($"read state of 'unchanged' {description}", false), options.AssertKv);
          }
        }
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
        if (e is ConversionExpr) {
          var ee = (ConversionExpr)e;
          CheckResultToBeInType(expr.tok, ee.E, ee.ToType, locals, builder, etran, ee.messagePrefix);
        }
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        CheckWellformed(e.E0, options, locals, builder, etran);
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
          case BinaryExpr.ResolvedOpcode.Imp: {
              BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
              CheckWellformed(e.E1, options, locals, b, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(e.E0), b.Collect(expr.tok), null, null));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Or: {
              BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
              CheckWellformed(e.E1, options, locals, b, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, Bpl.Expr.Not(etran.TrExpr(e.E0)), b.Collect(expr.tok), null, null));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Add:
          case BinaryExpr.ResolvedOpcode.Sub:
          case BinaryExpr.ResolvedOpcode.Mul:
            CheckWellformed(e.E1, options, locals, builder, etran);
            if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub && e.E0.Type.IsBigOrdinalType) {
              var rhsIsNat = FunctionCall(expr.tok, "ORD#IsNat", Bpl.Type.Bool, etran.TrExpr(e.E1));
              builder.Add(Assert(GetToken(expr), rhsIsNat, new PODesc.OrdinalSubtractionIsNatural()));
              var offset0 = FunctionCall(expr.tok, "ORD#Offset", Bpl.Type.Int, etran.TrExpr(e.E0));
              var offset1 = FunctionCall(expr.tok, "ORD#Offset", Bpl.Type.Int, etran.TrExpr(e.E1));
              builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(offset1, offset0), new PODesc.OrdinalSubtractionUnderflow()));
            } else if (e.Type.IsCharType) {
              var e0 = FunctionCall(expr.tok, "char#ToInt", Bpl.Type.Int, etran.TrExpr(e.E0));
              var e1 = FunctionCall(expr.tok, "char#ToInt", Bpl.Type.Int, etran.TrExpr(e.E1));
              if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
                builder.Add(Assert(GetToken(expr),
                  FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null,
                    Bpl.Expr.Binary(BinaryOperator.Opcode.Add, e0, e1)), new PODesc.CharOverflow()));
              } else {
                Contract.Assert(e.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub);  // .Mul is not supported for char
                builder.Add(Assert(GetToken(expr),
                  FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null,
                    Bpl.Expr.Binary(BinaryOperator.Opcode.Sub, e0, e1)), new PODesc.CharUnderflow()));
              }
            }
            CheckResultToBeInType(expr.tok, expr, expr.Type, locals, builder, etran);
            break;
          case BinaryExpr.ResolvedOpcode.Div:
          case BinaryExpr.ResolvedOpcode.Mod: {
              Bpl.Expr zero;
              if (e.E1.Type.IsBitVectorType) {
                zero = BplBvLiteralExpr(e.tok, BaseTypes.BigNum.ZERO, e.E1.Type.AsBitVectorType);
              } else if (e.E1.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
                zero = Bpl.Expr.Literal(BaseTypes.BigDec.ZERO);
              } else {
                zero = Bpl.Expr.Literal(0);
              }
              CheckWellformed(e.E1, options, locals, builder, etran);
              builder.Add(Assert(GetToken(expr), Bpl.Expr.Neq(etran.TrExpr(e.E1), zero), new PODesc.DivisorNonZero(), options.AssertKv));
              CheckResultToBeInType(expr.tok, expr, expr.Type, locals, builder, etran);
            }
            break;
          case BinaryExpr.ResolvedOpcode.LeftShift:
          case BinaryExpr.ResolvedOpcode.RightShift: {
              CheckWellformed(e.E1, options, locals, builder, etran);
              var w = e.Type.AsBitVectorType.Width;
              var upperDesc = new PODesc.ShiftUpperBound(w);
              if (e.E1.Type.IsBitVectorType) {
                // Known to be non-negative, so we don't need to check lower bound.
                // Check upper bound, that is, check "E1 <= w"
                var e1Width = e.E1.Type.AsBitVectorType.Width;
                if (w < (BigInteger.One << e1Width)) {
                  // w is a number that can be represented in the e.E1.Type, so do the comparison in that bitvector type.
                  var bound = BplBvLiteralExpr(e.tok, BaseTypes.BigNum.FromInt(w), e1Width);
                  var cmp = etran.TrToFunctionCall(expr.tok, "le_bv" + e1Width, Bpl.Type.Bool, etran.TrExpr(e.E1), bound, false);
                  builder.Add(Assert(GetToken(expr), cmp, upperDesc, options.AssertKv));
                } else {
                  // In the previous branch, we had:
                  //     w < 2^e1Width               (*)
                  // From the type of E1, we have:
                  //     E1 < 2^e1Width
                  // In this branch, (*) does not hold, so we therefore have the following:
                  //     E1 < 2^e1Width <= w
                  // In other words, the condition
                  //     E1 <= w
                  // already holds, so there is no reason to check it.
                }
              } else {
                var positiveDesc = new PODesc.ShiftLowerBound();
                builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.E1)), positiveDesc, options.AssertKv));
                builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(etran.TrExpr(e.E1), Bpl.Expr.Literal(w)), upperDesc, options.AssertKv));
              }
            }
            break;
          case BinaryExpr.ResolvedOpcode.EqCommon:
          case BinaryExpr.ResolvedOpcode.NeqCommon:
            CheckWellformed(e.E1, options, locals, builder, etran);
            if (e.InCompiledContext) {
              if (Resolver.CanCompareWith(e.E0) || Resolver.CanCompareWith(e.E1)) {
                // everything's fine
              } else {
                Contract.Assert(!e.E0.Type.SupportsEquality); // otherwise, CanCompareWith would have returned "true" above
                Contract.Assert(!e.E1.Type.SupportsEquality); // otherwise, CanCompareWith would have returned "true" above
                Contract.Assert(e.E0.Type.PartiallySupportsEquality); // otherwise, the code wouldn't have got passed the resolver
                Contract.Assert(e.E1.Type.PartiallySupportsEquality); // otherwise, the code wouldn't have got passed the resolver
                var dt = e.E0.Type.AsIndDatatype;
                Contract.Assert(dt != null); // only inductive datatypes support equality partially

                // to compare the datatype values for equality, there must not be any possibility that either of the datatype
                // variants is a ghost constructor
                var ghostConstructors = dt.Ctors.Where(ctor => ctor.IsGhost).ToList();
                Contract.Assert(ghostConstructors.Count != 0);

                void CheckOperand(Expression operand) {
                  var value = etran.TrExpr(operand);
                  var notGhostCtor = BplAnd(ghostConstructors.ConvertAll(
                    ctor => Bpl.Expr.Not(FunctionCall(expr.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, value))));
                  builder.Add(Assert(GetToken(expr), notGhostCtor,
                    new PODesc.NotGhostVariant("equality", ghostConstructors)));
                }

                CheckOperand(e.E0);
                CheckOperand(e.E1);
              }


            }
            break;
          default:
            CheckWellformed(e.E1, options, locals, builder, etran);
            break;
        }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        foreach (var ee in e.SubExpressions) {
          CheckWellformed(ee, options, locals, builder, etran);
        }
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            if (e.E0.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
              builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.E0)), new PODesc.PrefixEqualityLimit(), options.AssertKv));
            }
            break;
          default:
            Contract.Assert(false);  // unexpected ternary expression
            break;
        }

      } else if (expr is LetExpr) {
        CheckWellformedLetExprWithResult((LetExpr)expr, options, result, resultType, locals, builder, etran, true);
        result = null;

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var q = e as QuantifierExpr;
        var lam = e as LambdaExpr;
        var mc = e as MapComprehension;
        if (mc != null && !mc.IsGeneralMapComprehension) {
          mc = null;  // mc will be non-null when "e" is a general map comprehension
        }

        // This is a WF check, so we look at the original quantifier, not the split one.
        // This ensures that cases like forall x :: x != null && f(x.a) do not fail to verify.

        builder.Add(new Bpl.CommentCmd("Begin Comprehension WF check"));
        BplIfIf(e.tok, lam != null, null, builder, nextBuilder => {
          var comprehensionEtran = etran;
          if (lam != null) {
            // Havoc heap
            locals.Add(BplLocalVar(CurrentIdGenerator.FreshId((etran.UsesOldHeap ? "$Heap_at_" : "") + "$lambdaHeap#"), predef.HeapType, out var lambdaHeap));
            comprehensionEtran = new ExpressionTranslator(comprehensionEtran, lambdaHeap);
            nextBuilder.Add(new HavocCmd(expr.tok, Singleton((Bpl.IdentifierExpr)comprehensionEtran.HeapExpr)));
            nextBuilder.Add(new AssumeCmd(expr.tok, FunctionCall(expr.tok, BuiltinFunction.IsGoodHeap, null, comprehensionEtran.HeapExpr)));
            nextBuilder.Add(new AssumeCmd(expr.tok, HeapSameOrSucc(etran.HeapExpr, comprehensionEtran.HeapExpr)));
          }

          var substMap = SetupBoundVarsAsLocals(e.BoundVars, out var typeAntecedents, nextBuilder, locals, comprehensionEtran);
          BplIfIf(e.tok, true, typeAntecedents, nextBuilder, newBuilder => {
            var s = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
            var body = Substitute(e.Term, null, substMap);
            var bodyLeft = mc != null ? Substitute(mc.TermLeft, null, substMap) : null;
            var substMapPrime = mc != null ? SetupBoundVarsAsLocals(e.BoundVars, newBuilder, locals, comprehensionEtran, "#prime") : null;
            var bodyLeftPrime = mc != null ? Substitute(mc.TermLeft, null, substMapPrime) : null;
            var bodyPrime = mc != null ? Substitute(e.Term, null, substMapPrime) : null;
            List<FrameExpression> reads = null;

            var newOptions = options;
            if (lam != null) {
              // Set up a new frame
              var frameName = CurrentIdGenerator.FreshId("$_Frame#l");
              reads = lam.Reads.ConvertAll(s.SubstFrameExpr);
              DefineFrame(e.tok, reads, newBuilder, locals, frameName, comprehensionEtran);
              comprehensionEtran = new ExpressionTranslator(comprehensionEtran, frameName);

              // Check frame WF and that it read covers itself
              newOptions = new WFOptions(options.SelfCallsAllowance, true /* check reads clauses */, true /* delay reads checks */);
              CheckFrameWellFormed(newOptions, reads, locals, newBuilder, comprehensionEtran);
              // new options now contains the delayed reads checks
              newOptions.ProcessSavedReadsChecks(locals, builder, newBuilder);

              // continue doing reads checks, but don't delay them
              newOptions = new WFOptions(options.SelfCallsAllowance, true, false);
            }

            // check requires/range
            Bpl.Expr guard = null;
            if (e.Range != null) {
              var range = Substitute(e.Range, null, substMap);
              CheckWellformed(range, newOptions, locals, newBuilder, comprehensionEtran);
              guard = comprehensionEtran.TrExpr(range);
            }

            if (mc != null) {
              Contract.Assert(bodyLeft != null);
              BplIfIf(e.tok, guard != null, guard, newBuilder, b => { CheckWellformed(bodyLeft, newOptions, locals, b, comprehensionEtran); });
            }
            BplIfIf(e.tok, guard != null, guard, newBuilder, b => {
              Bpl.Expr resultIe = null;
              Type rangeType = null;
              if (lam != null) {
                var resultName = CurrentIdGenerator.FreshId("lambdaResult#");
                var resultVar = new Bpl.LocalVariable(body.tok, new Bpl.TypedIdent(body.tok, resultName, TrType(body.Type)));
                locals.Add(resultVar);
                resultIe = new Bpl.IdentifierExpr(body.tok, resultVar);
                rangeType = lam.Type.AsArrowType.Result;
              }
              CheckWellformedWithResult(body, newOptions, resultIe, rangeType, locals, b, comprehensionEtran);
            });

            if (mc != null) {
              Contract.Assert(substMapPrime != null);
              Contract.Assert(bodyLeftPrime != null);
              Contract.Assert(bodyPrime != null);
              Bpl.Expr guardPrime = null;
              if (guard != null) {
                Contract.Assert(e.Range != null);
                var rangePrime = Substitute(e.Range, null, substMapPrime);
                guardPrime = comprehensionEtran.TrExpr(rangePrime);
              }
              BplIfIf(e.tok, guard != null, BplAnd(guard, guardPrime), newBuilder, b => {
                var different = BplOr(
                  Bpl.Expr.Neq(comprehensionEtran.TrExpr(bodyLeft), comprehensionEtran.TrExpr(bodyLeftPrime)),
                  Bpl.Expr.Eq(comprehensionEtran.TrExpr(body), comprehensionEtran.TrExpr(bodyPrime)));
                b.Add(Assert(GetToken(mc.TermLeft), different, new PODesc.ComprehensionNoAlias()));
              });
            }
          });

          if (lam != null) {
            // assume false (heap was havoced inside an if)
            Contract.Assert(nextBuilder != builder);
            nextBuilder.Add(new AssumeCmd(e.tok, Bpl.Expr.False));
          }
        });
        builder.Add(new Bpl.CommentCmd("End Comprehension WF check"));

      } else if (expr is StmtExpr stmtExpr) {
        CheckWellformedStmtExpr(stmtExpr, options, result, resultType, locals, builder, etran);
        result = null;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        CheckWellformed(e.Test, options, locals, builder, etran);
        var bThen = new BoogieStmtListBuilder(this);
        var bElse = new BoogieStmtListBuilder(this);
        if (e.IsBindingGuard) {
          // if it is BindingGuard, e.Thn is a let-such-that created from the BindingGuard.
          // We don't need to do well-formedness check on the Rhs of the LetExpr since it
          // has already been checked in e.Test
          var letExpr = (LetExpr)e.Thn;
          Contract.Assert(letExpr != null);
          CheckWellformedLetExprWithResult(letExpr, options, result, resultType, locals, bThen, etran, false);
        } else {
          CheckWellformedWithResult(e.Thn, options, result, resultType, locals, bThen, etran);
        }
        CheckWellformedWithResult(e.Els, options, result, resultType, locals, bElse, etran);
        builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(e.Test), bThen.Collect(expr.tok), null, bElse.Collect(expr.tok)));
        result = null;
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        CheckWellformed(me.Source, options, locals, builder, etran);
        Bpl.Expr src = etran.TrExpr(me.Source);
        Bpl.IfCmd ifCmd = null;
        BoogieStmtListBuilder elsBldr = new BoogieStmtListBuilder(this);
        elsBldr.Add(TrAssumeCmd(expr.tok, Bpl.Expr.False));
        StmtList els = elsBldr.Collect(expr.tok);
        foreach (var missingCtor in me.MissingCases) {
          // havoc all bound variables
          var b = new BoogieStmtListBuilder(this);
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(me.tok, missingCtor, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Count != 0) {
            List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
            foreach (Variable local in newLocals) {
              havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
            }
            builder.Add(new Bpl.HavocCmd(me.tok, havocIds));
          }

          String missingStr = me.Context.FillHole(new IdCtx(missingCtor)).AbstractAllHoles().ToString();
          b.Add(Assert(GetToken(me), Bpl.Expr.False, new PODesc.MatchIsComplete("expression", missingStr)));

          Bpl.Expr guard = Bpl.Expr.Eq(src, r);
          ifCmd = new Bpl.IfCmd(me.tok, guard, b.Collect(me.tok), ifCmd, els);
          els = null;
        }
        for (int i = me.Cases.Count; 0 <= --i;) {
          MatchCaseExpr mc = me.Cases[i];
          BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
          Bpl.Expr ct = CtorInvocation(mc, me.Source.Type, etran, locals, b, NOALLOC, false);
          // generate:  if (src == ctor(args)) { assume args-is-well-typed; mc.Body is well-formed; assume Result == TrExpr(case); } else ...
          CheckWellformedWithResult(mc.Body, options, result, resultType, locals, b, etran);
          ifCmd = new Bpl.IfCmd(mc.tok, Bpl.Expr.Eq(src, ct), b.Collect(mc.tok), ifCmd, els);
          els = null;
        }
        builder.Add(ifCmd);
        result = null;

      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        // check that source expression is created from one of the legal source constructors, then proceed according to the .ResolvedExpression
        var correctConstructor = BplOr(e.LegalSourceConstructors.ConvertAll(
          ctor => FunctionCall(e.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Root))));
        if (e.LegalSourceConstructors.Count == e.Type.AsDatatype.Ctors.Count) {
          // Every constructor has this destructor; no need to check anything
        } else {
          builder.Add(Assert(GetToken(expr), correctConstructor,
            new PODesc.ValidConstructorNames(DatatypeDestructor.PrintableCtorNameList(e.LegalSourceConstructors, "or"))));
        }

        CheckNotGhostVariant(e.InCompiledContext, expr, e.Root, "update of", e.Members,
          e.LegalSourceConstructors, builder, etran);

        CheckWellformedWithResult(e.ResolvedExpression, options, result, resultType, locals, builder, etran);
        result = null;

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        CheckWellformedWithResult(e.ResolvedExpression, options, result, resultType, locals, builder, etran);
        result = null;
      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        CheckWellformedWithResult(nestedMatchExpr.Flattened, options, result, resultType, locals, builder, etran);
        result = null;
      } else if (expr is BoogieFunctionCall) {
        var e = (BoogieFunctionCall)expr;
        foreach (var arg in e.Args) {
          CheckWellformed(arg, options, locals, builder, etran);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (result != null) {
        Contract.Assert(resultType != null);
        var bResult = etran.TrExpr(expr);
        CheckSubrange(expr.tok, bResult, expr.Type, resultType, builder);
        builder.Add(TrAssumeCmd(expr.tok, Bpl.Expr.Eq(result, bResult)));
        builder.Add(TrAssumeCmd(expr.tok, CanCallAssumption(expr, etran)));
        builder.Add(new CommentCmd("CheckWellformedWithResult: any expression"));
        if (AlwaysUseHeap) {
          builder.Add(TrAssumeCmd(expr.tok, MkIsAlloc(result, resultType, etran.HeapExpr)));
        }
        builder.Add(TrAssumeCmd(expr.tok, MkIs(result, resultType)));
      }
    }

    private void CheckWellformedStmtExpr(StmtExpr stmtExpr, WFOptions options, Expr result, Type resultType, List<Variable> locals,
      BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      // If we're inside an "old" expression, then "etran" will know how to translate
      // expressions. However, here, we're also having to translate e.S, which is a
      // Statement. Since statement translation (in particular, translation of CallStmt's)
      // work directly on the global variable $Heap, we temporarily change its value here.
      if (etran.UsesOldHeap) {
        BuildWithHeapAs(stmtExpr.S.Tok, etran.HeapExpr, "StmtExpr#", locals, builder,
          () => TrStmt(stmtExpr.S, builder, locals, etran));
      } else {
        TrStmt(stmtExpr.S, builder, locals, etran);
      }

      CheckWellformedWithResult(stmtExpr.E, options, result, resultType, locals, builder, etran);
    }

    /// <summary>
    /// Temporarily set the heap to the value etran.HeapExpr and call build().
    ///
    /// The Boogie code generated by build() should have just one exit point, namely at the
    /// end of the code generated. (Any other exit would cause control flow to miss
    /// BuildWithHeapAs's assignment that restores the value of $Heap.)
    /// </summary>
    void BuildWithHeapAs(IToken token, Bpl.Expr temporaryHeap, string heapVarSuffix, List<Variable> locals,
      BoogieStmtListBuilder builder, System.Action build) {
      var suffix = CurrentIdGenerator.FreshId(heapVarSuffix);
      var tmpHeapVar = new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "Heap$" + suffix, predef.HeapType));
      locals.Add(tmpHeapVar);
      var tmpHeap = new Bpl.IdentifierExpr(token, tmpHeapVar);
      var generalEtran = new ExpressionTranslator(this, predef, token);
      var theHeap = generalEtran.HeapCastToIdentifierExpr;

      // tmpHeap := $Heap;
      builder.Add(Bpl.Cmd.SimpleAssign(token, tmpHeap, theHeap));
      // $Heap := etran.HeapExpr;
      builder.Add(Bpl.Cmd.SimpleAssign(token, theHeap, temporaryHeap));

      build();

      // $Heap := tmpHeap;
      builder.Add(Bpl.Cmd.SimpleAssign(token, theHeap, tmpHeap));
    }

    private void CheckNotGhostVariant(MemberSelectExpr expr, string whatKind, List<DatatypeCtor> candidateCtors,
      BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      CheckNotGhostVariant(expr.InCompiledContext, expr, expr.Obj, whatKind, new List<MemberDecl>() { expr.Member },
        candidateCtors, builder, etran);
    }

    private void CheckNotGhostVariant(bool inCompiledContext, Expression exprUsedForToken, Expression datatypeValue,
      string whatKind, List<MemberDecl> members, List<DatatypeCtor> candidateCtors, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      if (inCompiledContext) {
        // check that there is no possibility that the datatype variant is a ghost constructor
        var enclosingGhostConstructors = candidateCtors.Where(ctor => ctor.IsGhost).ToList();
        if (enclosingGhostConstructors.Count != 0) {
          var obj = etran.TrExpr(datatypeValue);
          var notGhostCtor = BplAnd(enclosingGhostConstructors.ConvertAll(
            ctor => Bpl.Expr.Not(FunctionCall(exprUsedForToken.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, obj))));
          builder.Add(Assert(GetToken(exprUsedForToken), notGhostCtor,
            new PODesc.NotGhostVariant(whatKind,
              Util.PrintableNameList(members.ConvertAll(member => member.Name), "and"),
              enclosingGhostConstructors)));
        }
      }
    }

    void CheckWellformedSpecialFunction(FunctionCallExpr expr, WFOptions options, Bpl.Expr result, Type resultType, List<Bpl.Variable> locals,
                               BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr.Function is SpecialFunction);

      string name = expr.Function.Name;
      CheckWellformed(expr.Receiver, options, locals, builder, etran);
      if (name == "RotateLeft" || name == "RotateRight") {
        var w = expr.Type.AsBitVectorType.Width;
        Expression arg = expr.Args[0];
        builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(arg)), new PODesc.ShiftLowerBound(), options.AssertKv));
        builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(etran.TrExpr(arg), Bpl.Expr.Literal(w)), new PODesc.ShiftUpperBound(w), options.AssertKv));
      }
    }

    void CheckWellformedLetExprWithResult(LetExpr e, WFOptions options, Bpl.Expr result, Type resultType, List<Bpl.Variable> locals,
      BoogieStmtListBuilder builder, ExpressionTranslator etran, bool checkRhs) {
      if (e.Exact) {
        var uniqueSuffix = "#Z" + defaultIdGenerator.FreshNumericId("#Z");
        var substMap = SetupBoundVarsAsLocals(e.BoundVars.ToList<BoundVar>(), builder, locals, etran, "#Z");
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("let#");
        for (int i = 0; i < e.LHSs.Count; i++) {
          var pat = e.LHSs[i];
          var rhs = e.RHSs[i];
          var nm = varNameGen.FreshId(string.Format("#{0}#", i));
          var r = new Bpl.LocalVariable(pat.tok, new Bpl.TypedIdent(pat.tok, nm, TrType(rhs.Type)));
          locals.Add(r);
          var rIe = new Bpl.IdentifierExpr(rhs.tok, r);
          CheckWellformedWithResult(e.RHSs[i], options, rIe, pat.Expr.Type, locals, builder, etran);
          CheckCasePatternShape(pat, rIe, rhs.tok, pat.Expr.Type, builder);
          builder.Add(TrAssumeCmd(pat.tok, Bpl.Expr.Eq(etran.TrExpr(Substitute(pat.Expr, null, substMap)), rIe)));
        }
        CheckWellformedWithResult(Substitute(e.Body, null, substMap), options, result, resultType, locals, builder, etran);

      } else {
        // CheckWellformed(var b :| RHS(b); Body(b)) =
        //   var b;
        //   if (typeAntecedent(b)) {
        //     CheckWellformed(RHS(b));
        //   }
        //   assert (exists b' :: typeAntecedent' && RHS(b'));
        //   assume typeAntecedent(b);
        //   assume RHS(b);
        //   CheckWellformed(Body(b));
        //   If non-ghost:  var b' where typeAntecedent; assume RHS(b'); assert Body(b) == Body(b');
        //   assume CanCall
        Contract.Assert(e.RHSs.Count == 1);  // this is true of all successfully resolved let-such-that expressions
        var lhsVars = e.BoundVars.ToList<BoundVar>();
        var substMap = SetupBoundVarsAsLocals(lhsVars, out var typeAntecedent, builder, locals, etran);
        var rhs = Substitute(e.RHSs[0], null, substMap);
        if (checkRhs) {
          var wellFormednessBuilder = new BoogieStmtListBuilder(this);
          CheckWellformed(rhs, options, locals, wellFormednessBuilder, etran);
          var ifCmd = new Bpl.IfCmd(e.tok, typeAntecedent, wellFormednessBuilder.Collect(e.tok), null, null);
          builder.Add(ifCmd);

          var bounds = lhsVars.ConvertAll(_ => (ComprehensionExpr.BoundedPool)new ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool());  // indicate "no alloc" (is this what we want?)
          GenerateAndCheckGuesses(e.tok, lhsVars, bounds, e.RHSs[0], TrTrigger(etran, e.Attributes, e.tok), builder, etran);
        }
        // assume typeAntecedent(b);
        builder.Add(TrAssumeCmd(e.tok, typeAntecedent));
        // assume RHS(b);
        builder.Add(TrAssumeCmd(e.tok, etran.TrExpr(rhs)));
        var letBody = Substitute(e.Body, null, substMap);
        CheckWellformed(letBody, options, locals, builder, etran);
        if (e.Constraint_Bounds != null) {
          var substMap_prime = SetupBoundVarsAsLocals(lhsVars, builder, locals, etran);
          var nonGhostMap_prime = new Dictionary<IVariable, Expression>();
          foreach (BoundVar bv in lhsVars) {
            nonGhostMap_prime.Add(bv, bv.IsGhost ? substMap[bv] : substMap_prime[bv]);
          }
          var rhs_prime = Substitute(e.RHSs[0], null, nonGhostMap_prime);
          var letBody_prime = Substitute(e.Body, null, nonGhostMap_prime);
          builder.Add(TrAssumeCmd(e.tok, CanCallAssumption(rhs_prime, etran)));
          builder.Add(TrAssumeCmd(e.tok, etran.TrExpr(rhs_prime)));
          builder.Add(TrAssumeCmd(e.tok, CanCallAssumption(letBody_prime, etran)));
          var eq = Expression.CreateEq(letBody, letBody_prime, e.Body.Type);
          builder.Add(Assert(GetToken(e), etran.TrExpr(eq), new PODesc.LetSuchThanUnique()));
        }
        // assume $let$canCall(g);
        LetDesugaring(e);  // call LetDesugaring to prepare the desugaring and populate letSuchThatExprInfo with something for e
        var info = letSuchThatExprInfo[e];
        builder.Add(new Bpl.AssumeCmd(e.tok, info.CanCallFunctionCall(this, etran)));
        // If we are supposed to assume "result" to equal this expression, then use the body of the let-such-that, not the generated $let#... function
        if (result != null) {
          Contract.Assert(resultType != null);
          var bResult = etran.TrExpr(letBody);
          CheckSubrange(letBody.tok, bResult, letBody.Type, resultType, builder);
          builder.Add(TrAssumeCmd(letBody.tok, Bpl.Expr.Eq(result, bResult)));
          builder.Add(TrAssumeCmd(letBody.tok, CanCallAssumption(letBody, etran)));
          builder.Add(new CommentCmd("CheckWellformedWithResult: Let expression"));
          if (AlwaysUseHeap) {
            builder.Add(TrAssumeCmd(letBody.tok, MkIsAlloc(result, resultType, etran.HeapExpr)));
          }
          builder.Add(TrAssumeCmd(letBody.tok, MkIs(result, resultType)));
        }
      }
    }

    void CheckFrameWellFormed(WFOptions wfo, List<FrameExpression> fes, List<Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(fes != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      foreach (var fe in fes) {
        CheckWellformed(fe.E, wfo, locals, builder, etran);
        if (fe.Field != null && fe.E.Type.IsRefType) {
          builder.Add(Assert(fe.tok, Bpl.Expr.Neq(etran.TrExpr(fe.E), predef.Null), new PODesc.FrameDereferenceNonNull()));
        }
      }
    }

  }
}
