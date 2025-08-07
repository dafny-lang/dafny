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
using DafnyCore.Verifier;
using DafnyCore.Verifier.Statements;
using Bpl = Microsoft.Boogie;
using Microsoft.Boogie;
using Std.Wrappers;
using static Microsoft.Dafny.Util;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {

  /// <summary>
  /// Instances of WFOptions are used as an argument to CheckWellformed, supplying options for the
  /// checks to be performed.
  /// If "SelfCallsAllowance" is non-null, termination checks will be omitted for calls that look
  /// like it.  This is useful in function postconditions, where the result of the function is
  /// syntactically given as what looks like a recursive call with the same arguments.
  /// "DoReadsChecks" indicates whether or not to perform reads checks.  If so, the generated code
  /// will make references to $_ReadsFrame.  If "saveReadsChecks" is true, then the reads checks will
  /// be recorded but postponed.  In particular, CheckWellformed will append to .Locals a list of
  /// fresh local variables and will append to .Assert assertions with appropriate error messages
  /// that can be used later.  As a convenience, the ProcessSavedReadsChecks will make use of .Locals
  /// and .Asserts (and AssignLocals) and update a given StmtListBuilder.
  /// "LValueContext" indicates that the expression checked for well-formedness is an L-value of
  /// some assignment.
  /// </summary>
  public class WFOptions {
    public readonly Function SelfCallsAllowance;
    public readonly bool DoReadsChecks;
    public readonly bool DoOnlyCoarseGrainedTerminationChecks; // termination checks don't look at decreases clause, but reports errors for any intra-SCC call (this is used in default-value expressions)
    public readonly Variables Locals;
    public readonly List<Func<Bpl.Cmd>> CreateAsserts;
    public readonly bool LValueContext;
    public readonly Bpl.QKeyValue AssertKv;

    public WFOptions() {
    }

    public WFOptions(Function selfCallsAllowance, bool doReadsChecks,
      bool saveReadsChecks = false, bool doOnlyCoarseGrainedTerminationChecks = false) {
      Contract.Requires(!saveReadsChecks || doReadsChecks);  // i.e., saveReadsChecks ==> doReadsChecks
      SelfCallsAllowance = selfCallsAllowance;
      DoReadsChecks = doReadsChecks;
      DoOnlyCoarseGrainedTerminationChecks = doOnlyCoarseGrainedTerminationChecks;
      if (saveReadsChecks) {
        Locals = new Variables();
        CreateAsserts = [];
      }
    }

    private WFOptions(Function selfCallsAllowance, bool doReadsChecks, bool doOnlyCoarseGrainedTerminationChecks,
      Variables locals, List<Func<Bpl.Cmd>> createAsserts, bool lValueContext, Bpl.QKeyValue assertKv) {
      SelfCallsAllowance = selfCallsAllowance;
      DoReadsChecks = doReadsChecks;
      DoOnlyCoarseGrainedTerminationChecks = doOnlyCoarseGrainedTerminationChecks;
      Locals = locals;
      CreateAsserts = createAsserts;
      LValueContext = lValueContext;
      AssertKv = assertKv;
    }

    public WFOptions(Bpl.QKeyValue kv) {
      AssertKv = kv;
    }

    /// <summary>
    /// Clones the given "options", but turns reads checks on or off.
    /// </summary>
    public WFOptions WithReadsChecks(bool doReadsChecks) {
      return new WFOptions(SelfCallsAllowance, doReadsChecks, DoOnlyCoarseGrainedTerminationChecks,
        Locals, CreateAsserts, LValueContext, AssertKv);
    }

    /// <summary>
    /// Clones the given "options", but sets "LValueContext" to "lValueContext".
    /// </summary>
    public WFOptions WithLValueContext(bool lValueContext) {
      return new WFOptions(SelfCallsAllowance, DoReadsChecks, DoOnlyCoarseGrainedTerminationChecks,
        Locals, CreateAsserts, lValueContext, AssertKv);
    }

    public Action<IOrigin, Bpl.Expr, ProofObligationDescription, Bpl.QKeyValue> AssertSink(BoogieGenerator tran, BoogieStmtListBuilder builder) {
      return (t, e, d, qk) => {
        if (Locals != null) {
          var b = BoogieGenerator.BplLocalVar(tran.CurrentIdGenerator.FreshId("b$reqreads#"), Bpl.Type.Bool, Locals);
          CreateAsserts.Add(() => tran.Assert(t, b, d, builder.Context, qk));
          builder.Add(Bpl.Cmd.SimpleAssign(e.tok, (Bpl.IdentifierExpr)b, e));
        } else {
          builder.Add(tran.Assert(t, e, d, builder.Context, qk));
        }
      };
    }

    public List<Bpl.AssignCmd> AssignLocals {
      get {
        return Map(Locals.Values, l =>
          Bpl.Cmd.SimpleAssign(l.tok,
            new Bpl.IdentifierExpr(Token.NoToken, l),
            Bpl.Expr.True)
          );
      }
    }

    public void ProcessSavedReadsChecks(Variables locals, BoogieStmtListBuilder builderInitializationArea, BoogieStmtListBuilder builder) {
      Contract.Requires(locals != null);
      Contract.Requires(builderInitializationArea != null);
      Contract.Requires(builder != null);
      Contract.Requires(Locals != null && CreateAsserts != null);  // ProcessSavedReadsChecks should be called only if the constructor was called with saveReadsChecks

      // var b$reads_guards#0 : bool  ...
      locals.AddRange(Locals.Values);
      // b$reads_guards#0 := true   ...
      foreach (var cmd in AssignLocals) {
        builderInitializationArea.Add(cmd);
      }
      // assert b$reads_guards#0;  ...
      foreach (var a in CreateAsserts) {
        builder.Add(a());
      }
    }
  }

  public partial class BoogieGenerator {

    public void CheckWellformedAndAssume(Expression expr, WFOptions wfOptions, Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran, string comment) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type != null && expr.Type.IsBoolType);
      Contract.Requires(wfOptions != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(Predef != null);
      if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
            // WF[e0]; assume e0; WF[e1]; assume e1;
            CheckWellformedAndAssume(e.E0, wfOptions, locals, builder, etran, comment);
            CheckWellformedAndAssume(e.E1, wfOptions, locals, builder, etran, comment);
            return;
          case BinaryExpr.ResolvedOpcode.Imp: {
              // if (*) {
              //   WF[e0]; assume e0; WF[e1]; assume e1;
              // } else {
              //   assume e0 ==> e1;
              // }
              var bAnd = new BoogieStmtListBuilder(this, options, builder.Context);
              CheckWellformedAndAssume(e.E0, wfOptions, locals, bAnd, etran, comment);
              CheckWellformedAndAssume(e.E1, wfOptions, locals, bAnd, etran, comment);
              var bImp = new BoogieStmtListBuilder(this, options, builder.Context);
              bImp.Add(TrAssumeCmd(expr.Origin, etran.CanCallAssumption(expr)));
              bImp.Add(TrAssumeCmdWithDependencies(etran, expr.Origin, expr, comment));
              builder.Add(new Bpl.IfCmd(expr.Origin, null, bAnd.Collect(expr.Origin), null, bImp.Collect(expr.Origin)));
            }
            return;
          case BinaryExpr.ResolvedOpcode.Or: {
              // if (*) {
              //   WF[e0]; assume e0;
              // } else {
              //   assume !e0;
              //   WF[e1]; assume e1;
              // }
              var b0 = new BoogieStmtListBuilder(this, options, builder.Context);
              CheckWellformedAndAssume(e.E0, wfOptions, locals, b0, etran, comment);
              var b1 = new BoogieStmtListBuilder(this, options, builder.Context);
              b1.Add(TrAssumeCmd(expr.Origin, etran.CanCallAssumption(e.E0)));
              b1.Add(TrAssumeCmdWithDependenciesAndExtend(etran, expr.Origin, e.E0, Expr.Not, comment));
              CheckWellformedAndAssume(e.E1, wfOptions, locals, b1, etran, comment);
              builder.Add(new Bpl.IfCmd(expr.Origin, null, b0.Collect(expr.Origin), null, b1.Collect(expr.Origin)));
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
        var bThen = new BoogieStmtListBuilder(this, options, builder.Context);
        CheckWellformedAndAssume(e.Test, wfOptions, locals, bThen, etran, comment);
        CheckWellformedAndAssume(e.Thn, wfOptions, locals, bThen, etran, comment);
        var bElse = new BoogieStmtListBuilder(this, options, builder.Context);
        bElse.Add(TrAssumeCmd(expr.Origin, etran.CanCallAssumption(e.Test)));
        bElse.Add(TrAssumeCmdWithDependenciesAndExtend(etran, expr.Origin, e.Test, Expr.Not, comment));
        CheckWellformedAndAssume(e.Els, wfOptions, locals, bElse, etran, comment);
        builder.Add(new Bpl.IfCmd(expr.Origin, null, bThen.Collect(expr.Origin), null, bElse.Collect(expr.Origin)));
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
        CheckWellformedAndAssume(body, wfOptions, locals, builder, etran, comment);

        if (e is ForallExpr) {
          // Although we do the WF check on the original quantifier, we assume the split one.
          // This ensures that cases like forall x :: x != null && f(x.a) do not fail to verify.
          builder.Add(TrAssumeCmdWithDependencies(etran, expr.Origin, e.SplitQuantifierExpression ?? e, comment));
        }
        return;
      }

      // resort to the behavior of simply checking well-formedness followed by assuming the translated expression
      CheckWellformed(expr, wfOptions, locals, builder, etran);

      // NOTE: If the CheckWellformed call above found a split quantifier, it ignored
      //       the splitting and proceeded to decompose the full quantifier as
      //       normal. This call to TrExpr, on the other hand, will indeed use the
      //       split quantifier.
      builder.Add(TrAssumeCmdWithDependencies(etran, expr.Origin, expr, comment));
    }

    // Helper object for ensuring delayed reads checks are always processed.
    // Also encapsulates the handling for the optimization to not declare a $_ReadsFrame field if the reads clause is *:
    // if etran.readsFrame is null, the block is called with a WFOption with DoReadsChecks set to false instead.
    private record ReadsCheckDelayer(ExpressionTranslator etran, Function selfCallsAllowance,
      Variables localVariables, BoogieStmtListBuilder builderInitializationArea, BoogieStmtListBuilder builder) {

      public void DoWithDelayedReadsChecks(bool doOnlyCoarseGrainedTerminationChecks, Action<WFOptions> action) {
        var doReadsChecks = etran.readsFrame != null;
        var options = new WFOptions(selfCallsAllowance, doReadsChecks, doReadsChecks, doOnlyCoarseGrainedTerminationChecks);
        action(options);
        if (doReadsChecks) {
          options.ProcessSavedReadsChecks(localVariables, builderInitializationArea, builder);
        }
      }
    }

    /// <summary>
    /// Check the well-formedness of "expr" (but don't leave hanging around any assumptions that affect control flow)
    /// </summary>
    public void CheckWellformed(Expression expr, WFOptions wfOptions, Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(wfOptions != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(Predef != null);
      CheckWellformedWithResult(expr, wfOptions, locals, builder, etran, null);
    }

    /// <summary>
    /// Adds to "builder" code that checks the well-formedness of "expr".  Any local variables introduced
    /// in this code are added to "locals".
    /// See class WFOptions for descriptions of the specified options.
    /// </summary>
    public void CheckWellformedWithResult(Expression expr, WFOptions wfOptions,
      Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      AddResultCommands addResultCommands) {

      var origOptions = wfOptions;
      if (wfOptions.LValueContext) {
        // Turn off LValueContext for any recursive call
        wfOptions = wfOptions.WithLValueContext(false);
      }

      var readFrames = GetContextReadsFrames();

      switch (expr) {
        case StaticReceiverExpr stexpr: {
            if (stexpr.ObjectToDiscard != null) {
              CheckWellformedWithResult(stexpr.ObjectToDiscard, wfOptions, locals, builder, etran, null);
            }

            break;
          }
        case LiteralExpr:
          CheckResultToBeInType(expr.Origin, expr, expr.Type, locals, builder, etran);
          if (expr is StringLiteralExpr stringLiteralExpr) {
            var ancestorSeqType = (SeqType)expr.Type.NormalizeToAncestorType();
            var elementType = ancestorSeqType.Arg;
            foreach (var ch in Util.UnescapedCharacters(options, (string)stringLiteralExpr.Value, stringLiteralExpr.IsVerbatim)) {
              var rawElement = FunctionCall(GetToken(stringLiteralExpr), BuiltinFunction.CharFromInt, null, Boogie.Expr.Literal(ch));
              CheckSubrange(expr.Origin, rawElement, Type.Char, elementType, expr, builder);
            }
          }
          break;
        case ThisExpr:
        case WildcardExpr:
        case BoogieWrapper:
          // always allowed
          break;
        case IdentifierExpr identifierExpr: {
            var e = identifierExpr;
            if (!origOptions.LValueContext) {
              CheckDefiniteAssignment(e, builder);
            }

            break;
          }
        case DisplayExpression expression: {
            DisplayExpression e = expression;
            var type = e.Type.NormalizeToAncestorType();
            Contract.Assert(type is CollectionType);
            var elementType = ((CollectionType)type).Arg;
            foreach (Expression el in e.Elements) {
              CheckWellformed(el, wfOptions, locals, builder, etran);
              CheckSubrange(el.Origin, etran.TrExpr(el), el.Type, elementType, el, builder);
            }
            CheckResultToBeInType(e.Origin, e, e.Type, locals, builder, etran);
            break;
          }
        case MapDisplayExpr displayExpr: {
            MapDisplayExpr e = displayExpr;
            var type = e.Type.NormalizeToAncestorType();
            Contract.Assert(type is MapType);
            var keyType = ((MapType)type).Domain;
            var valType = ((MapType)type).Range;
            foreach (MapDisplayEntry p in e.Elements) {
              CheckWellformed(p.A, wfOptions, locals, builder, etran);
              CheckSubrange(p.A.Origin, etran.TrExpr(p.A), p.A.Type, keyType, p.A, builder);
              CheckWellformed(p.B, wfOptions, locals, builder, etran);
              CheckSubrange(p.B.Origin, etran.TrExpr(p.B), p.B.Type, valType, p.B, builder);
            }
            CheckResultToBeInType(e.Origin, e, e.Type, locals, builder, etran);
            break;
          }
        case MemberSelectExpr selectExpr: {
            MemberSelectExpr e = selectExpr;
            CheckWellformed(e.Obj, wfOptions, locals, builder, etran);
            if (e.Obj.Type.IsRefType) {
              if (inBodyInitContext && Expression.AsThis(e.Obj) != null && !e.Member.IsInstanceIndependentConstant) {
                // this uses the surrogate local
                if (!origOptions.LValueContext) {
                  CheckDefiniteAssignmentSurrogate(selectExpr.Origin, (Field)e.Member, false, builder);
                }
              } else {
                CheckNonNull(selectExpr.Origin, e.Obj, builder, etran, wfOptions.AssertKv);
                // Check that the receiver is available in the state in which the dereference occurs
              }
            } else if (e.Member is DatatypeDestructor dtor) {
              var correctConstructor = BplOr(dtor.EnclosingCtors.ConvertAll(
                ctor => FunctionCall(e.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Obj))));
              if (dtor.EnclosingCtors.Count == dtor.EnclosingCtors[0].EnclosingDatatype.Ctors.Count) {
                // Every constructor has this destructor; might as well assume that here.
                builder.Add(TrAssumeCmd(selectExpr.Origin, correctConstructor));
              } else {
                builder.Add(Assert(GetToken(expr), correctConstructor,
                  new DestructorValid(dtor, e.Obj, dtor.EnclosingCtors), builder.Context));
              }
              CheckNotGhostVariant(e, "destructor", dtor.EnclosingCtors, builder, etran);
            } else if (e.Member is DatatypeDiscriminator discriminator) {
              CheckNotGhostVariant(e, "discriminator", ((DatatypeDecl)discriminator.EnclosingClass).Ctors, builder, etran);
            }
            if (!e.Member.IsStatic) {
              if (e.Member is TwoStateFunction) {
                Bpl.Expr wh = GetWhereClause(selectExpr.Origin, etran.TrExpr(e.Obj), e.Obj.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
                if (wh != null) {
                  var desc = new IsAllocated("receiver argument", "in the two-state function's previous state", e.Obj, e.AtLabel);
                  builder.Add(Assert(GetToken(expr), wh, desc, builder.Context));
                }
              } else if (etran.UsesOldHeap) {
                Bpl.Expr wh = GetWhereClause(selectExpr.Origin, etran.TrExpr(e.Obj), e.Obj.Type, etran, ISALLOC, true);
                if (wh != null) {
                  var desc = new IsAllocated("receiver",
                    $"in the state in which its {(e.Member is Field ? "fields" : "members")} are accessed", e.Obj, e.AtLabel);
                  builder.Add(Assert(GetToken(expr), wh, desc, builder.Context));
                }
              }
            }
            if (!origOptions.LValueContext && wfOptions.DoReadsChecks && e.Member is Field { IsMutable: true } f) {
              var requiredFrame = new FrameExpression(Token.NoToken, e.Obj, f.Name);
              var desc = new ReadFrameSubset("read field", requiredFrame, readFrames, selectExpr, etran.scope);
              wfOptions.AssertSink(this, builder)(selectExpr.Origin, Bpl.Expr.SelectTok(selectExpr.Origin, etran.ReadsFrame(selectExpr.Origin), etran.TrExpr(e.Obj), GetField(e)),
                desc, wfOptions.AssertKv);
            }

            builder.Add(TrAssumeCmd(e.Origin, etran.CanCallAssumption(e)));
            break;
          }
        case SeqSelectExpr selectExpr: {
            SeqSelectExpr e = selectExpr;
            var eSeqType = e.Seq.Type.NormalizeToAncestorType();
            bool isSequence = eSeqType is SeqType;
            CheckWellformed(e.Seq, wfOptions, locals, builder, etran);
            Bpl.Expr seq = etran.TrExpr(e.Seq);
            if (eSeqType.IsArrayType) {
              builder.Add(Assert(GetToken(e.Seq), Bpl.Expr.Neq(seq, Predef.Null),
                new NonNull("array", e.Seq), builder.Context));
              if (etran.UsesOldHeap) {
                builder.Add(Assert(GetToken(e.Seq), MkIsAlloc(seq, eSeqType, etran.HeapExpr),
                  new IsAllocated("array", null, e.Seq), builder.Context));
              }
            }
            Bpl.Expr e0 = null;
            if (eSeqType is MapType) {
              bool finite = ((MapType)eSeqType).Finite;
              e0 = etran.TrExpr(e.E0);
              CheckWellformed(e.E0, wfOptions, locals, builder, etran);
              var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
              Bpl.Expr inDomain = FunctionCall(selectExpr.Origin, f, finite ? Predef.MapType : Predef.IMapType, seq);
              inDomain = IsSetMember(GetToken(expr), inDomain, BoxIfNecessary(e.Origin, e0, e.E0.Type), finite);
              builder.Add(Assert(GetToken(expr), inDomain,
                new ElementInDomain(e.Seq, e.E0), builder.Context, wfOptions.AssertKv));
            } else if (eSeqType is MultiSetType) {
              // cool

            } else {
              if (e.E0 != null) {
                e0 = etran.TrExpr(e.E0);
                CheckWellformed(e.E0, wfOptions, locals, builder, etran);
                var desc = new InRange(e.Seq, e.E0, e.SelectOne, e.SelectOne ? "index" : "lower bound");
                builder.Add(Assert(GetToken(expr),
                  InSeqRange(selectExpr.Origin, e0, e.E0.Type, seq, isSequence, null, !e.SelectOne),
                  desc, builder.Context, wfOptions.AssertKv));
              }
              if (e.E1 != null) {
                CheckWellformed(e.E1, wfOptions, locals, builder, etran);
                Bpl.Expr lowerBound;
                if (e0 != null && e.E0.Type.IsBitVectorType) {
                  lowerBound = ConvertExpression(e.E0.Origin, e0, e.E0.Type, Type.Int);
                } else {
                  lowerBound = e0;
                }
                builder.Add(Assert(GetToken(expr),
                  InSeqRange(selectExpr.Origin, etran.TrExpr(e.E1), e.E1.Type, seq, isSequence, lowerBound, true),
                  new SequenceSelectRangeValid(e.Seq, e.E0, e.E1, isSequence ? "sequence" : "array"),
                  builder.Context, wfOptions.AssertKv));
              }
            }
            if (!origOptions.LValueContext && wfOptions.DoReadsChecks && eSeqType.IsArrayType) {
              if (e.SelectOne) {
                Contract.Assert(e.E0 != null);
                var i = etran.TrExpr(e.E0);
                i = ConvertExpression(selectExpr.Origin, i, e.E0.Type, Type.Int);
                Bpl.Expr fieldName = FunctionCall(selectExpr.Origin, BuiltinFunction.IndexField, null, i);
                var requiredFrame = new FrameExpression(Token.NoToken, e.Seq, null);
                var desc = new ReadFrameSubset("read array element", requiredFrame, readFrames, e, etran.scope);
                wfOptions.AssertSink(this, builder)(selectExpr.Origin, Bpl.Expr.SelectTok(selectExpr.Origin, etran.ReadsFrame(selectExpr.Origin), seq, fieldName),
                  desc, wfOptions.AssertKv);
              } else {
                Bpl.Expr lowerBound = e.E0 == null ? Bpl.Expr.Literal(0) : etran.TrExpr(e.E0);
                Contract.Assert(eSeqType.AsArrayType.Dims == 1);
                Bpl.Expr upperBound = e.E1 == null ? ArrayLength(e.Origin, seq, 1, 0) : etran.TrExpr(e.E1);
                // check that, for all i in lowerBound..upperBound, a[i] is in the frame
                Bpl.BoundVariable iVar = new Bpl.BoundVariable(e.Origin, new Bpl.TypedIdent(e.Origin, "$i", Bpl.Type.Int));
                Bpl.IdentifierExpr i = new Bpl.IdentifierExpr(e.Origin, iVar);
                var range = BplAnd(Bpl.Expr.Le(lowerBound, i), Bpl.Expr.Lt(i, upperBound));
                var fieldName = FunctionCall(e.Origin, BuiltinFunction.IndexField, null, i);
                var allowedToRead = Bpl.Expr.SelectTok(e.Origin, etran.ReadsFrame(e.Origin), seq, fieldName);
                var trigger = BplTrigger(allowedToRead); // Note, the assertion we're about to produce only seems useful in the check-only mode (that is, with subsumption 0), but if it were to be assumed, we'll use this entire RHS as the trigger
                var qq = new Bpl.ForallExpr(e.Origin, [iVar], trigger, BplImp(range, allowedToRead));
                var requiredFrame = new FrameExpression(Token.NoToken, e.Seq, null);
                var desc = new ReadFrameSubset("read the indicated range of array elements", requiredFrame, readFrames, e, etran.scope);
                wfOptions.AssertSink(this, builder)(selectExpr.Origin, qq, desc, wfOptions.AssertKv);
              }
            }

            if (!e.SelectOne) {
              CheckResultToBeInType(e.Origin, e, e.Type, locals, builder, etran);
            }
            break;
          }
        case MultiSelectExpr selectExpr: {
            MultiSelectExpr e = selectExpr;
            CheckWellformed(e.Array, wfOptions, locals, builder, etran);
            var array = CheckNonNullAndAllocated(builder, etran, e.Array);
            var indices = e.Indices;
            CheckWellFormednessOfIndexList(wfOptions, locals, builder, etran, indices, array, e.Array, e);
            if (wfOptions.DoReadsChecks) {
              Bpl.Expr fieldName = etran.GetArrayIndexFieldName(e.Origin, indices);
              var requiredFrame = new FrameExpression(Token.NoToken, e.Array, null);
              var desc = new ReadFrameSubset("read array element", requiredFrame, readFrames, selectExpr, etran.scope);
              wfOptions.AssertSink(this, builder)(selectExpr.Origin, Bpl.Expr.SelectTok(selectExpr.Origin, etran.ReadsFrame(selectExpr.Origin), array, fieldName),
                desc, wfOptions.AssertKv);
            }

            break;
          }
        case SeqUpdateExpr updateExpr: {
            var e = updateExpr;
            CheckWellformed(e.Seq, wfOptions, locals, builder, etran);
            Bpl.Expr seq = etran.TrExpr(e.Seq);
            Bpl.Expr index = etran.TrExpr(e.Index);
            Bpl.Expr value = etran.TrExpr(e.Value);
            var collectionType = (CollectionType)e.Seq.Type.NormalizeToAncestorType();
            // validate index
            CheckWellformed(e.Index, wfOptions, locals, builder, etran);
            if (collectionType is SeqType) {
              var desc = new InRange(e.Seq, e.Index, true, "index");
              builder.Add(Assert(GetToken(e.Index),
                InSeqRange(updateExpr.Origin, index, e.Index.Type, seq, true, null, false),
                desc, builder.Context, wfOptions.AssertKv));
            } else {
              CheckSubrange(e.Index.Origin, index, e.Index.Type, collectionType.Arg, e.Index, builder);
            }
            // validate value
            CheckWellformed(e.Value, wfOptions, locals, builder, etran);
            if (collectionType is SeqType) {
              CheckSubrange(e.Value.Origin, value, e.Value.Type, collectionType.Arg, e.Value, builder);
            } else if (collectionType is MapType mapType) {
              CheckSubrange(e.Value.Origin, value, e.Value.Type, mapType.Range, e.Value, builder);
            } else if (collectionType is MultiSetType) {
              var desc = new NonNegative("new number of occurrences", e.Value);
              builder.Add(Assert(GetToken(e.Value), Bpl.Expr.Le(Bpl.Expr.Literal(0), value),
                desc, builder.Context, wfOptions.AssertKv));
            } else {
              Contract.Assert(false);
            }

            break;
          }
        case ApplyExpr applyExpr: {
            var e = applyExpr;
            int arity = e.Args.Count;
            var tt = e.Function.Type.AsArrowType;
            Contract.Assert(tt != null);
            Contract.Assert(tt.Arity == arity);

            // check WF of receiver and arguments
            CheckWellformed(e.Function, wfOptions, locals, builder, etran);
            foreach (Expression arg in e.Args) {
              CheckWellformed(arg, wfOptions, locals, builder, etran);
            }

            // check subranges of arguments
            for (int i = 0; i < arity; ++i) {
              CheckSubrange(e.Args[i].Origin, etran.TrExpr(e.Args[i]), e.Args[i].Type, tt.Args[i], e.Args[i], builder);
            }

            // check parameter availability
            if (etran.UsesOldHeap) {
              Bpl.Expr wh = GetWhereClause(e.Function.Origin, etran.TrExpr(e.Function), e.Function.Type, etran, ISALLOC, true);
              if (wh != null) {
                var desc = new IsAllocated("function", "in the state in which the function is invoked", e.Function);
                builder.Add(Assert(GetToken(e.Function), wh, desc, builder.Context));
              }
              for (int i = 0; i < e.Args.Count; i++) {
                Expression ee = e.Args[i];
                wh = GetWhereClause(ee.Origin, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
                if (wh != null) {
                  var desc = new IsAllocated("argument", "in the state in which the function is invoked", ee);
                  builder.Add(Assert(GetToken(ee), wh, desc, builder.Context));
                }
              }
            }

            // translate arguments to requires and reads
            Func<Expression, Bpl.Expr> TrArg = arg => {
              Bpl.Expr inner = etran.TrExpr(arg);
              if (ModeledAsBoxType(arg.Type)) {
                return inner;
              } else {
                return FunctionCall(arg.Origin, BuiltinFunction.Box, null, inner);
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

            // unwrap renamed local lambdas
            var unwrappedFunc = e.Function;
            while (unwrappedFunc is ConcreteSyntaxExpression { ResolvedExpression: not null } cse) {
              unwrappedFunc = cse.ResolvedExpression;
            }
            if (unwrappedFunc is IdentifierExpr { Origin: var origin, DafnyName: var dafnyName }) {
              unwrappedFunc = new IdentifierExpr(origin, dafnyName);
            }

            if (!fnCoreType.IsArrowTypeWithoutPreconditions) {
              var dPrecond = new ApplyExpr(
                Token.NoToken,
                new ExprDotName(Token.NoToken, unwrappedFunc, new Name("requires"), null),
                e.Args,
                Token.NoToken);

              // check precond
              var bPrecond = FunctionCall(e.Origin, Requires(arity), Bpl.Type.Bool, args);
              builder.Add(Assert(GetToken(expr), bPrecond,
                new PreconditionSatisfied(dPrecond, null, null), builder.Context));
            }

            if (wfOptions.DoReadsChecks && !fnCoreType.IsArrowTypeWithoutReadEffects) {
              // check read effects
              Type objset = program.SystemModuleManager.ObjectSetType();
              Expression wrap = new BoogieWrapper(
                FunctionCall(e.Origin, Reads(arity), TrType(objset), args),
                objset);
              var wrappedReads = new FrameExpression(e.Origin, wrap, null);

              var readsCall = new ApplyExpr(
                Token.NoToken,
                new ExprDotName(Token.NoToken, unwrappedFunc, new Name("reads"), null),
                e.Args,
                Token.NoToken
              );
              readsCall.Type = objset;
              var requiredFrame = new FrameExpression(Token.NoToken, readsCall, null);
              var desc = new ReadFrameSubset("invoke function", requiredFrame, readFrames);

              CheckFrameSubset(applyExpr.Origin, [wrappedReads], null, null,
                etran, etran.ReadsFrame(applyExpr.Origin), wfOptions.AssertSink(this, builder), (ta, qa) => builder.Add(new Bpl.AssumeCmd(ta, qa)), desc, wfOptions.AssertKv);
            }

            break;
          }
        case DatatypeValue value: {
            DatatypeValue dtv = value;
            for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
              var formal = dtv.Ctor.Formals[i];
              var arg = dtv.Arguments[i];
              if (arg is not DefaultValueExpression) {
                CheckWellformed(arg, wfOptions, locals, builder, etran);
              }
              // Cannot use the datatype's formals, so we substitute the inferred type args:
              var su = new Dictionary<TypeParameter, Type>();
              foreach (var p in Enumerable.Zip(dtv.Ctor.EnclosingDatatype.TypeArgs, dtv.InferredTypeArgs)) {
                su[p.Item1] = p.Item2;
              }
              Type ty = formal.Type.Subst(su);
              CheckSubrange(arg.Origin, etran.TrExpr(arg), arg.Type, ty, arg, builder);
            }

            break;
          }
        case FunctionCallExpr callExpr: {
            FunctionCallExpr e = callExpr;
            Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
            if (e.Function is SpecialFunction) {
              CheckWellformedSpecialFunction(e, wfOptions, null, null, locals, builder, etran);
            } else {
              // check well-formedness of receiver
              CheckWellformed(e.Receiver, wfOptions, locals, builder, etran);
              if (!e.Function.IsStatic && !(e.Receiver is ThisExpr) && !e.Receiver.Type.IsArrowType) {
                CheckNonNull(callExpr.Origin, e.Receiver, builder, etran, wfOptions.AssertKv);
              }
              if (!e.Function.IsStatic && !etran.UsesOldHeap) {
                // the argument can't be assumed to be allocated for the old heap
                Type et = UserDefinedType.FromTopLevelDecl(e.Origin, e.Function.EnclosingClass).Subst(e.GetTypeArgumentSubstitutions());
                builder.Add(new Bpl.CommentCmd("assume allocatedness for receiver argument to function"));
                builder.Add(TrAssumeCmd(e.Receiver.Origin, MkIsAllocBox(BoxIfNecessary(e.Receiver.Origin, etran.TrExpr(e.Receiver), e.Receiver.Type), et, etran.HeapExpr)));
              }
              // create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
              Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
              Dictionary<IVariable, Expression> directSubstMap = new Dictionary<IVariable, Expression>();
              for (int i = 0; i < e.Function.Ins.Count; i++) {
                Formal p = e.Function.Ins[i];
                // Note, in the following, the "##" makes the variable invisible in BVD.  An alternative would be to communicate
                // to BVD what this variable stands for and display it as such to the user.
                Type et = p.Type.Subst(e.GetTypeArgumentSubstitutions());
                LocalVariable local = new LocalVariable(p.Origin, "##" + p.Name, et, p.IsGhost);
                local.type = local.SafeSyntacticType;  // resolve local here
                var ie = new IdentifierExpr(local.Origin, local.AssignUniqueName(CurrentDeclaration.IdGenerator)) {
                  Var = local
                };
                ie.Type = ie.Var.Type;  // resolve ie here
                substMap.Add(p, ie);
                locals.GetOrAdd(new Bpl.LocalVariable(local.Origin, new Bpl.TypedIdent(local.Origin, local.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(local.Type))));
                Bpl.IdentifierExpr lhs = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
                Expression ee = e.Args[i];
                directSubstMap.Add(p, ee);

                if (!(ee is DefaultValueExpression)) {
                  CheckWellformedWithResult(ee, wfOptions, locals, builder, etran, (returnBuilder, result) => {
                    CheckSubrange(result.Origin, etran.TrExpr(result), ee.Type, et, ee, returnBuilder);
                  });
                }
                Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(p.Origin, lhs, AdaptBoxing(p.Origin, etran.TrExpr(ee), Cce.NonNull(ee.Type), et));
                builder.Add(cmd);
                if (!etran.UsesOldHeap) {
                  // the argument can't be assumed to be allocated for the old heap
                  builder.Add(new Bpl.CommentCmd("assume allocatedness for argument to function"));
                  builder.Add(TrAssumeCmd(e.Args[i].Origin, MkIsAlloc(lhs, et, etran.HeapExpr)));
                }
              }

              // Check that every parameter is available in the state in which the function is invoked; this means checking that it has
              // the right type and is allocated.  These checks usually hold trivially, on account of that the Dafny language only gives
              // access to expressions of the appropriate type and that are allocated in the current state.  However, if the function is
              // invoked in the 'old' state or if the function invoked is a two-state function with a non-new parameter, then we need to
              // check that its arguments were all available at that time as well.
              if (etran.UsesOldHeap) {
                if (!e.Function.IsStatic) {
                  Bpl.Expr wh = GetWhereClause(e.Receiver.Origin, etran.TrExpr(e.Receiver), e.Receiver.Type, etran, ISALLOC, true);
                  if (wh != null) {
                    var desc = new IsAllocated("receiver argument", "in the state in which the function is invoked", e.Receiver, e.AtLabel);
                    builder.Add(Assert(GetToken(e.Receiver), wh, desc, builder.Context));
                  }
                }
                for (int i = 0; i < e.Args.Count; i++) {
                  Expression ee = e.Args[i];
                  Bpl.Expr wh = GetWhereClause(ee.Origin, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
                  if (wh != null) {
                    var desc = new IsAllocated("argument", "in the state in which the function is invoked", ee, e.AtLabel);
                    builder.Add(Assert(GetToken(ee), wh, desc, builder.Context));
                  }
                }
              } else if (e.Function is TwoStateFunction) {
                if (!e.Function.IsStatic) {
                  Bpl.Expr wh = GetWhereClause(e.Receiver.Origin, etran.TrExpr(e.Receiver), e.Receiver.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
                  if (wh != null) {
                    var desc = new IsAllocated("receiver argument", "in the two-state function's previous state", e.Receiver, e.AtLabel);
                    builder.Add(Assert(GetToken(e.Receiver), wh, desc, builder.Context));
                  }
                }
                Contract.Assert(e.Function.Ins.Count == e.Args.Count);
                for (int i = 0; i < e.Args.Count; i++) {
                  var formal = e.Function.Ins[i];
                  if (formal.IsOld) {
                    Expression ee = e.Args[i];
                    Bpl.Expr wh = GetWhereClause(ee.Origin, etran.TrExpr(ee), ee.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
                    if (wh != null) {
                      var pIdx = e.Args.Count == 1 ? "" : " at index " + i;
                      var desc = new IsAllocated(
                        $"argument{pIdx} for parameter '{formal.Name}'",
                        "in the two-state function's previous state" + IsAllocated.HelperFormal(formal),
                        ee,
                        e.AtLabel
                      );
                      builder.Add(Assert(GetToken(ee), wh, desc, builder.Context));
                    }
                  }
                }
              }
              // check that the preconditions for the call hold
              // the check for .reads function must be translated explicitly: their declaration lacks
              // an explicit precondition, which is added as an axiom in Translator.cs
              if (e.Function.Name == "reads" && !e.Receiver.Type.IsArrowTypeWithoutReadEffects) {
                var arguments = etran.FunctionInvocationArguments(e, null, null);
                var precondition = FunctionCall(e.Origin, Requires(e.Args.Count), Bpl.Type.Bool, arguments);
                builder.Add(Assert(GetToken(expr), precondition, new PreconditionSatisfied(null, null, null), builder.Context));

                if (wfOptions.DoReadsChecks) {
                  // check that the callee reads only what the caller is already allowed to read
                  Type objset = program.SystemModuleManager.ObjectSetType();
                  Expression wrap = new BoogieWrapper(
                    FunctionCall(expr.Origin, Reads(e.Args.Count()), TrType(objset), arguments),
                    objset);
                  var reads = new FrameExpression(expr.Origin, wrap, null);
                  List<FrameExpression> requiredFrames;
                  switch (e.Receiver.Resolved) {
                    case MemberSelectExpr { Member: MethodOrFunction readsReceiver }: {
                        var receiverReplacement = readsReceiver.IsStatic
                          ? null
                          : new ThisExpr(readsReceiver);
                        var receiverSubstMap = readsReceiver.Ins.Zip(e.Args)
                          .ToDictionary(fa => fa.First as IVariable, fa => fa.Second);
                        var subst = new Substituter(receiverReplacement, receiverSubstMap, e.GetTypeArgumentSubstitutions());
                        requiredFrames = readsReceiver.Reads.Expressions.ConvertAll(subst.SubstFrameExpr);
                        break;
                      }
                    default:
                      var readsCall = new ApplyExpr(
                        Token.NoToken,
                        new ExprDotName(Token.NoToken, e.Receiver.Resolved, new Name("reads"), null),
                        e.Args,
                        Token.NoToken
                      );
                      readsCall.Type = objset;
                      requiredFrames = [new FrameExpression(Token.NoToken, readsCall, null)];
                      break;
                  }
                  var desc = new ReadFrameSubset("invoke function", requiredFrames, readFrames);
                  CheckFrameSubset(expr.Origin, [reads], null, null,
                    etran, etran.ReadsFrame(expr.Origin), wfOptions.AssertSink(this, builder), (ta, qa) => builder.Add(new Bpl.AssumeCmd(ta, qa)), desc, wfOptions.AssertKv);
                }

              } else {
                // Directly substitutes arguments for formals, to be displayed to the user
                var argSubstMap = e.Function.Ins.Zip(e.Args).ToDictionary(fa => fa.First as IVariable, fa => fa.Second);
                var directSub = new Substituter(e.Receiver, argSubstMap, e.GetTypeArgumentSubstitutions());

                foreach (AttributedExpression p in ConjunctsOf(e.Function.Req)) {
                  var directPrecond = directSub.Substitute(p.E);

                  Expression precond = Substitute(p.E, e.Receiver, substMap, e.GetTypeArgumentSubstitutions());
                  builder.Add(TrAssumeCmd(precond.Origin, etran.CanCallAssumption(precond)));
                  var (errorMessage, successMessage) = CustomErrorMessage(p.Attributes);
                  foreach (var ss in TrSplitExpr(builder.Context, precond, etran, true, out _)) {
                    if (ss.IsChecked) {
                      var tok = new NestedOrigin(GetToken(expr), ss.Tok, "this proposition could not be proved");
                      var desc = new PreconditionSatisfied(directPrecond, errorMessage, successMessage);
                      if (wfOptions.AssertKv != null) {
                        // use the given assert attribute only
                        builder.Add(Assert(tok, ss.E, desc, builder.Context, wfOptions.AssertKv));
                      } else {
                        builder.Add(AssertAndForget(builder.Context, tok, ss.E, desc));
                      }
                    }
                  }
                  if (wfOptions.AssertKv == null) {
                    // assume only if no given assert attribute is given
                    builder.Add(TrAssumeCmd(callExpr.Origin, etran.TrExpr(precond)));
                  }
                }
                if (wfOptions.DoReadsChecks) {
                  // check that the callee reads only what the caller is already allowed to read

                  // substitute actual args for parameters in description expression frames...
                  var requiredFrames = e.Function.Reads.Expressions.ConvertAll(directSub.SubstFrameExpr);
                  var desc = new ReadFrameSubset("invoke function", requiredFrames, readFrames);

                  // ... but that substitution isn't needed for frames passed to CheckFrameSubset
                  var readsSubst = new Substituter(null, new Dictionary<IVariable, Expression>(), e.GetTypeArgumentSubstitutions());
                  CheckFrameSubset(callExpr.Origin,
                    e.Function.Reads.Expressions.ConvertAll(readsSubst.SubstFrameExpr),
                    e.Receiver, substMap, etran, etran.ReadsFrame(callExpr.Origin), wfOptions.AssertSink(this, builder), (ta, qa) => builder.Add(new Bpl.AssumeCmd(ta, qa)), desc, wfOptions.AssertKv);
                }
              }
              Expression allowance = null;
              if (codeContext != null && e.CoCall != FunctionCallExpr.CoCallResolution.Yes && !(e.Function is ExtremePredicate)) {
                // check that the decreases measure goes down
                var calleeSCCLookup = e.IsByMethodCall ? (ICallable)e.Function.ByMethodDecl : e.Function;
                Contract.Assert(calleeSCCLookup != null);
                if (ModuleDefinition.InSameSCC(calleeSCCLookup, codeContext)) {
                  if (wfOptions.DoOnlyCoarseGrainedTerminationChecks) {
                    builder.Add(Assert(GetToken(expr), Bpl.Expr.False, new IsNonRecursive(), builder.Context));
                  } else {
                    if (e.Function == wfOptions.SelfCallsAllowance) {
                      allowance = Expression.CreateBoolLiteral(e.Origin, true);
                      if (!e.Function.IsStatic) {
                        allowance = Expression.CreateAnd(allowance, Expression.CreateEq(e.Receiver, new ThisExpr(e.Function), e.Receiver.Type));
                      }
                      for (int i = 0; i < e.Args.Count; i++) {
                        Expression ee = e.Args[i];
                        Formal ff = e.Function.Ins[i];
                        allowance = Expression.CreateAnd(allowance, Expression.CreateEq(ee, Expression.CreateIdentExpr(ff), ff.Type));
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

                    if (e.Function == wfOptions.SelfCallsAllowance) {
                      allowance = etran.MakeAllowance(e);
                    }
                    if (e.CoCallHint != null) {
                      hint = hint == null ? e.CoCallHint : string.Format("{0}; {1}", hint, e.CoCallHint);
                    }
                    List<Expression> contextDecreases = codeContext.Decreases.Expressions;
                    List<Expression> calleeDecreases = e.Function.Decreases.Expressions;
                    CheckCallTermination(callExpr.Origin, contextDecreases, calleeDecreases, allowance, e.Receiver, substMap, directSubstMap, e.GetTypeArgumentSubstitutions(),
                      etran, false, builder, codeContext.InferredDecreases, hint);
                  }
                }
              }
              // all is okay, so allow this function application access to the function's axiom, except if it was okay because of the self-call allowance.
              Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(callExpr.Origin, e.Function.FullSanitizedName + "#canCall", Bpl.Type.Bool);
              List<Bpl.Expr> args = etran.FunctionInvocationArguments(e, null, null);
              Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(GetToken(expr), new Bpl.FunctionCall(canCallFuncID), args);
              builder.Add(TrAssumeCmd(callExpr.Origin, allowance == null ? canCallFuncAppl : BplOr(etran.TrExpr(allowance), canCallFuncAppl)));

              var returnType = e.Type.AsDatatype;
              if (returnType != null && returnType.Ctors.Count == 1) {
                var correctConstructor = FunctionCall(e.Origin, returnType.Ctors[0].QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e));
                // There is only one constructor, so the value must be been constructed by it; might as well assume that here.
                builder.Add(TrAssumeCmd(callExpr.Origin, correctConstructor));
              }
            }

            break;
          }
        case SeqConstructionExpr constructionExpr: {
            var e = constructionExpr;
            CheckWellformed(e.N, wfOptions, locals, builder, etran);
            var desc = new NonNegative("sequence size", e.N);
            builder.Add(Assert(GetToken(e.N), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.N)), desc, builder.Context));

            CheckWellformed(e.Initializer, wfOptions, locals, builder, etran);
            var eType = e.Type.NormalizeToAncestorType().AsSeqType.Arg;
            CheckElementInit(e.Origin, false, [e.N], eType, e.Initializer, null, builder, etran, wfOptions);
            break;
          }
        case MultiSetFormingExpr formingExpr: {
            MultiSetFormingExpr e = formingExpr;
            CheckWellformed(e.E, wfOptions, locals, builder, etran);
            CheckResultToBeInType(e.Origin, e, e.Type, locals, builder, etran);
            break;
          }
        case OldExpr oldExpr: {
            var e = oldExpr;
            // Anything read inside the 'old' expressions depends only on the old heap, which isn't included in the
            // frame axiom.  In other words, 'old' expressions have no dependencies on the current heap.  Therefore,
            // we turn off any reads checks for "e.E".
            CheckWellformed(e.Expr, wfOptions.WithReadsChecks(false), locals, builder, etran.OldAt(e.AtLabel));
            break;
          }
        case UnchangedExpr unchangedExpr: {
            var e = unchangedExpr;
            var contextReadsFrames = GetContextReadsFrames();
            foreach (var fe in e.Frame) {
              CheckWellformed(fe.E, wfOptions, locals, builder, etran);

              EachReferenceInFrameExpression(fe.E, locals, builder, etran, out var description, out var ty, out var r, out var ante);
              Bpl.Expr nonNull;
              if (ty.IsNonNullRefType) {
                nonNull = Bpl.Expr.True;
              } else {
                Contract.Assert(ty.IsRefType);
                nonNull = Bpl.Expr.Neq(r, Predef.Null);
                builder.Add(Assert(GetToken(fe.E), BplImp(ante, nonNull),
                  new NonNull(description, fe.E, description != "object"), builder.Context));
              }
              // check that "r" was allocated in the "e.AtLabel" state
              Bpl.Expr wh = GetWhereClause(fe.E.Origin, r, ty, etran.OldAt(e.AtLabel), ISALLOC, true);
              if (wh != null) {
                var desc = new IsAllocated(description, "in the old-state of the 'unchanged' predicate",
                  fe.E, e.AtLabel, description != "object");
                builder.Add(Assert(GetToken(fe.E), BplImp(BplAnd(ante, nonNull), wh), desc, builder.Context));
              }
              // check that the 'unchanged' argument reads only what the context is allowed to read
              if (wfOptions.DoReadsChecks) {
                var desc = new ReadFrameSubset($"read state of 'unchanged' {description}", fe, contextReadsFrames);
                CheckFrameSubset(fe.E.Origin,
                  [fe],
                  null, new Dictionary<IVariable, Expression>(), etran, etran.ReadsFrame(fe.E.Origin), wfOptions.AssertSink(this, builder),
                  (ta, qa) => builder.Add(new Bpl.AssumeCmd(ta, qa)),
                  desc, wfOptions.AssertKv);
              }
            }

            break;
          }
        case UnaryExpr unaryExpr: {
            UnaryExpr e = unaryExpr;
            if (e is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Assigned }) {
              CheckWellformed(e.E.Resolved, wfOptions.WithLValueContext(true), locals, builder, etran);
            } else {
              CheckWellformed(e.E, wfOptions, locals, builder, etran);
            }

            if (e is ConversionExpr ee) {
              CheckResultToBeInType(unaryExpr.Origin, ee.E, ee.ToType, locals, builder, etran, ee.messagePrefix);
            }

            CheckResultToBeInType(expr.Origin, expr, expr.Type, locals, builder, etran);
            break;
          }
        case BinaryExpr binaryExpr: {
            BinaryExpr e = binaryExpr;
            CheckWellformed(e.E0, wfOptions, locals, builder, etran);
            switch (e.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.And:
              case BinaryExpr.ResolvedOpcode.Imp: {
                  BoogieStmtListBuilder b = new BoogieStmtListBuilder(this, options, builder.Context);
                  CheckWellformed(e.E1, wfOptions, locals, b, etran);
                  builder.Add(new Bpl.IfCmd(binaryExpr.Origin, etran.TrExpr(e.E0), b.Collect(binaryExpr.Origin), null, null));
                }
                break;
              case BinaryExpr.ResolvedOpcode.Or: {
                  BoogieStmtListBuilder b = new BoogieStmtListBuilder(this, options, builder.Context);
                  CheckWellformed(e.E1, wfOptions, locals, b, etran);
                  builder.Add(new Bpl.IfCmd(binaryExpr.Origin, Bpl.Expr.Not(etran.TrExpr(e.E0)), b.Collect(binaryExpr.Origin), null, null));
                }
                break;
              case BinaryExpr.ResolvedOpcode.Add:
              case BinaryExpr.ResolvedOpcode.Sub:
              case BinaryExpr.ResolvedOpcode.Mul:
                CheckWellformed(e.E1, wfOptions, locals, builder, etran);
                if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub && e.E0.Type.IsBigOrdinalType) {
                  var rhsIsNat = FunctionCall(binaryExpr.Origin, "ORD#IsNat", Bpl.Type.Bool, etran.TrExpr(e.E1));
                  builder.Add(Assert(GetToken(expr), rhsIsNat,
                    new OrdinalSubtractionIsNatural(e.E1), builder.Context));
                  var offset0 = FunctionCall(binaryExpr.Origin, "ORD#Offset", Bpl.Type.Int, etran.TrExpr(e.E0));
                  var offset1 = FunctionCall(binaryExpr.Origin, "ORD#Offset", Bpl.Type.Int, etran.TrExpr(e.E1));
                  builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(offset1, offset0),
                    new OrdinalSubtractionUnderflow(e.E0, e.E1), builder.Context));
                } else if (e.Type.NormalizeToAncestorType().IsCharType) {
                  var e0 = FunctionCall(binaryExpr.Origin, "char#ToInt", Bpl.Type.Int, etran.TrExpr(e.E0));
                  var e1 = FunctionCall(binaryExpr.Origin, "char#ToInt", Bpl.Type.Int, etran.TrExpr(e.E1));
                  if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
                    builder.Add(Assert(GetToken(expr),
                      FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null,
                        Bpl.Expr.Binary(BinaryOperator.Opcode.Add, e0, e1)),
                      new CharOverflow(e.E0, e.E1), builder.Context));
                  } else {
                    Contract.Assert(e.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub);  // .Mul is not supported for char
                    builder.Add(Assert(GetToken(expr),
                      FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null,
                        Bpl.Expr.Binary(BinaryOperator.Opcode.Sub, e0, e1)),
                      new CharUnderflow(e.E0, e.E1), builder.Context));
                  }
                }
                break;
              case BinaryExpr.ResolvedOpcode.Div:
              case BinaryExpr.ResolvedOpcode.Mod: {
                  Bpl.Expr zero;
                  if (e.E1.Type.NormalizeToAncestorType() is BitvectorType bitvectorType) {
                    zero = BplBvLiteralExpr(e.Origin, BaseTypes.BigNum.ZERO, bitvectorType);
                  } else if (e.E1.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
                    zero = Bpl.Expr.Literal(BaseTypes.BigDec.ZERO);
                  } else {
                    zero = Bpl.Expr.Literal(0);
                  }
                  CheckWellformed(e.E1, wfOptions, locals, builder, etran);
                  builder.Add(Assert(GetToken(expr), Bpl.Expr.Neq(etran.TrExpr(e.E1), zero),
                    new DivisorNonZero(e.E1), builder.Context, wfOptions.AssertKv));
                }
                break;
              case BinaryExpr.ResolvedOpcode.LeftShift:
              case BinaryExpr.ResolvedOpcode.RightShift: {
                  CheckWellformed(e.E1, wfOptions, locals, builder, etran);
                  var w = e.Type.NormalizeToAncestorType().AsBitVectorType.Width;
                  var upperDesc = new ShiftUpperBound(w, true, e.E1);
                  if (e.E1.Type.NormalizeToAncestorType().AsBitVectorType is { } bitvectorType) {
                    // Known to be non-negative, so we don't need to check lower bound.
                    // Check upper bound, that is, check "E1 <= w"
                    var e1Width = bitvectorType.Width;
                    if (w < (BigInteger.One << e1Width)) {
                      // w is a number that can be represented in the e.E1.Type, so do the comparison in that bitvector type.
                      var bound = BplBvLiteralExpr(e.Origin, BaseTypes.BigNum.FromInt(w), e1Width);
                      var cmp = etran.TrToFunctionCall(binaryExpr.Origin, "le_bv" + e1Width, Bpl.Type.Bool, etran.TrExpr(e.E1), bound, false);
                      builder.Add(Assert(GetToken(expr), cmp, upperDesc, builder.Context, wfOptions.AssertKv));
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
                    var positiveDesc = new ShiftLowerBound(true, e.E1);
                    builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.E1)),
                      positiveDesc, builder.Context, wfOptions.AssertKv));
                    builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(etran.TrExpr(e.E1), Bpl.Expr.Literal(w)),
                      upperDesc, builder.Context, wfOptions.AssertKv));
                  }
                }
                break;
              case BinaryExpr.ResolvedOpcode.EqCommon:
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                CheckWellformed(e.E1, wfOptions, locals, builder, etran);
                if (e.InCompiledContext) {
                  if (CheckTypeCharacteristicsVisitor.CanCompareWith(e.E0) || CheckTypeCharacteristicsVisitor.CanCompareWith(e.E1)) {
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
                        ctor => Bpl.Expr.Not(FunctionCall(expr.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, value))));
                      builder.Add(Assert(GetToken(expr), notGhostCtor,
                        new NotGhostVariant("equality", operand, ghostConstructors), builder.Context));
                    }

                    CheckOperand(e.E0);
                    CheckOperand(e.E1);
                  }
                }
                break;
              default:
                CheckWellformed(e.E1, wfOptions, locals, builder, etran);
                break;
            }

            CheckResultToBeInType(expr.Origin, expr, expr.Type, locals, builder, etran);
            break;
          }
        case TernaryExpr ternaryExpr: {
            var e = ternaryExpr;
            foreach (var ee in e.SubExpressions) {
              CheckWellformed(ee, wfOptions, locals, builder, etran);
            }
            switch (e.Op) {
              case TernaryExpr.Opcode.PrefixEqOp:
              case TernaryExpr.Opcode.PrefixNeqOp:
                if (e.E0.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
                  builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.E0)),
                    new PrefixEqualityLimit(e.E0), builder.Context, wfOptions.AssertKv));
                }
                break;
              default:
                Contract.Assert(false);  // unexpected ternary expression
                break;
            }

            CheckResultToBeInType(expr.Origin, expr, expr.Type, locals, builder, etran);
            break;
          }
        case LetExpr letExpr:
          CheckWellformedLetExprWithResult(letExpr, wfOptions, locals, builder, etran, true, addResultCommands);
          addResultCommands = null;
          break;
        case ComprehensionExpr comprehensionExpr: {
            var e = comprehensionExpr;
            var lam = e as LambdaExpr;
            var mc = e as MapComprehension;
            if (mc is { IsGeneralMapComprehension: false }) {
              mc = null;  // mc will be non-null when "e" is a general map comprehension
            }

            // This is a WF check, so we look at the original quantifier, not the split one.
            // This ensures that cases like forall x :: x != null && f(x.a) do not fail to verify.

            builder.Add(new Bpl.CommentCmd("Begin Comprehension WF check"));
            BplIfIf(e.Origin, lam != null, null, builder, nextBuilder => {
              var comprehensionEtran = etran;
              if (lam != null) {
                // Havoc heap
                locals.GetOrAdd(BplLocalVar(CurrentIdGenerator.FreshId((etran.UsesOldHeap ? "$Heap_at_" : "") + "$lambdaHeap#"), Predef.HeapType, out var lambdaHeap));
                comprehensionEtran = new ExpressionTranslator(comprehensionEtran, lambdaHeap);
                nextBuilder.Add(new HavocCmd(e.Origin, Singleton((Bpl.IdentifierExpr)comprehensionEtran.HeapExpr)));
                nextBuilder.Add(new AssumeCmd(e.Origin, FunctionCall(e.Origin, BuiltinFunction.IsGoodHeap, null, comprehensionEtran.HeapExpr)));
                nextBuilder.Add(new AssumeCmd(e.Origin, HeapSameOrSucc(etran.HeapExpr, comprehensionEtran.HeapExpr)));
              }

              var substMap = SetupBoundVarsAsLocals(e.BoundVars, out var typeAntecedents, nextBuilder, locals, comprehensionEtran);
              BplIfIf(e.Origin, true, typeAntecedents, nextBuilder, newBuilder => {
                var s = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
                var body = Substitute(e.Term, null, substMap);
                var bodyLeft = mc != null ? Substitute(mc.TermLeft, null, substMap) : null;
                var substMapPrime = mc != null ? SetupBoundVarsAsLocals(e.BoundVars, newBuilder, locals, comprehensionEtran, "#prime") : null;
                var bodyLeftPrime = mc != null ? Substitute(mc.TermLeft, null, substMapPrime) : null;
                var bodyPrime = mc != null ? Substitute(e.Term, null, substMapPrime) : null;
                List<FrameExpression> reads = null;

                var newOptions = wfOptions;
                if (lam != null) {
                  // Set up a new frame
                  var frameName = CurrentIdGenerator.FreshId("$_Frame#l");
                  reads = lam.Reads.Expressions.ConvertAll(s.SubstFrameExpr);
                  comprehensionEtran = comprehensionEtran.WithReadsFrame(frameName, lam);
                  DefineFrame(e.Origin, comprehensionEtran.ReadsFrame(e.Origin), reads, newBuilder, locals, frameName, comprehensionEtran);

                  // Check frame WF and that it read covers itself
                  var delayer = new ReadsCheckDelayer(comprehensionEtran, wfOptions.SelfCallsAllowance, locals, builder, newBuilder);
                  delayer.DoWithDelayedReadsChecks(false, wfo => {
                    CheckFrameWellFormed(wfo, reads, locals, newBuilder, comprehensionEtran);
                  });

                  // continue doing reads checks, but don't delay them
                  newOptions = new WFOptions(wfOptions.SelfCallsAllowance, true, false);
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
                  BplIfIf(e.Origin, guard != null, guard, newBuilder, b => { CheckWellformed(bodyLeft, newOptions, locals, b, comprehensionEtran); });
                }
                BplIfIf(e.Origin, guard != null, guard, newBuilder, b => {
                  Bpl.Expr resultIe = null;
                  Type rangeType = null;
                  if (lam != null) {
                    var resultName = CurrentIdGenerator.FreshId("lambdaResult#");
                    var resultVar = new Bpl.LocalVariable(body.Origin, new Bpl.TypedIdent(body.Origin, resultName, TrType(body.Type)));
                    locals.GetOrAdd(resultVar);
                    resultIe = new Bpl.IdentifierExpr(body.Origin, resultVar);
                    rangeType = lam.Type.AsArrowType.Result;
                  }

                  void AddResultCommands(BoogieStmtListBuilder returnBuilder, Expression result) {
                    if (rangeType != null) {
                      CheckSubsetType(etran, result, resultIe, rangeType, returnBuilder, "lambda expression");
                    }
                  }

                  CheckWellformedWithResult(body, newOptions, locals, b, comprehensionEtran, AddResultCommands);
                });

                if (mc != null) {
                  Contract.Assert(substMapPrime != null);
                  Contract.Assert(bodyLeftPrime != null);
                  Contract.Assert(bodyPrime != null);
                  Bpl.Expr guardPrimeCanCall = null;
                  Bpl.Expr guardPrime = null;
                  if (guard != null) {
                    Contract.Assert(e.Range != null);
                    var rangePrime = Substitute(e.Range, null, substMapPrime);
                    guardPrimeCanCall = comprehensionEtran.CanCallAssumption(rangePrime);
                    guardPrime = comprehensionEtran.TrExpr(rangePrime);
                  }
                  BplIfIf(e.Origin, guard != null, BplAnd(guard, guardPrime), newBuilder, b => {
                    var canCalls = guardPrimeCanCall ?? Bpl.Expr.True;
                    canCalls = BplAnd(canCalls, comprehensionEtran.CanCallAssumption(bodyLeft));
                    canCalls = BplAnd(canCalls, comprehensionEtran.CanCallAssumption(bodyLeftPrime));
                    canCalls = BplAnd(canCalls, comprehensionEtran.CanCallAssumption(body));
                    canCalls = BplAnd(canCalls, comprehensionEtran.CanCallAssumption(bodyPrime));
                    var different = BplOr(
                      Bpl.Expr.Neq(comprehensionEtran.TrExpr(bodyLeft), comprehensionEtran.TrExpr(bodyLeftPrime)),
                      Bpl.Expr.Eq(comprehensionEtran.TrExpr(body), comprehensionEtran.TrExpr(bodyPrime)));
                    b.Add(new AssumeCmd(mc.TermLeft.Origin, canCalls));
                    b.Add(Assert(GetToken(mc.TermLeft), different,
                      new ComprehensionNoAlias(mc.BoundVars, mc.Range, mc.TermLeft, mc.Term), builder.Context));
                  });
                }
              });

              if (lam != null) {
                // assume false (heap was havoced inside an if)
                Contract.Assert(nextBuilder != builder);
                nextBuilder.Add(new AssumeCmd(e.Origin, Bpl.Expr.False));
              }
            });

            bool needTypeConstraintCheck;
            if (lam == null) {
              needTypeConstraintCheck = true;
            } else {
              // omit constraint check if the type is according to the syntax of the expression
              var arrowType = (UserDefinedType)e.Type.NormalizeExpandKeepConstraints();
              if (ArrowType.IsPartialArrowTypeName(arrowType.Name)) {
                needTypeConstraintCheck = lam.Reads.Expressions.Count != 0;
              } else if (ArrowType.IsTotalArrowTypeName(arrowType.Name)) {
                needTypeConstraintCheck = lam.Reads.Expressions.Count != 0 || lam.Range != null;
              } else {
                needTypeConstraintCheck = true;
              }
            }
            if (needTypeConstraintCheck) {
              CheckResultToBeInType(e.Origin, e, e.Type, locals, builder, etran);
            }

            builder.Add(new Bpl.CommentCmd("End Comprehension WF check"));
            builder.Add(TrAssumeCmd(expr.Origin, etran.CanCallAssumption(expr)));
            break;
          }
        case StmtExpr stmtExpr:
          CheckWellformedStmtExpr(stmtExpr, wfOptions, locals, builder, etran, addResultCommands);
          addResultCommands = null;
          break;
        case ITEExpr iteExpr: {
            ITEExpr e = iteExpr;
            CheckWellformed(e.Test, wfOptions, locals, builder, etran);
            var bThen = new BoogieStmtListBuilder(this, options, builder.Context);
            var bElse = new BoogieStmtListBuilder(this, options, builder.Context);
            if (e.IsBindingGuard) {
              // if it is BindingGuard, e.Thn is a let-such-that created from the BindingGuard.
              // We don't need to do well-formedness check on the Rhs of the LetExpr since it
              // has already been checked in e.Test
              var letExpr = (LetExpr)e.Thn;
              Contract.Assert(letExpr != null);
              CheckWellformedLetExprWithResult(letExpr, wfOptions, locals, bThen, etran, false, addResultCommands);
            } else {
              CheckWellformedWithResult(e.Thn, wfOptions, locals, bThen, etran, addResultCommands);
            }
            CheckWellformedWithResult(e.Els, wfOptions, locals, bElse, etran, addResultCommands);
            builder.Add(new Bpl.IfCmd(iteExpr.Origin, etran.TrExpr(e.Test), bThen.Collect(iteExpr.Origin), null, bElse.Collect(iteExpr.Origin)));
            addResultCommands = null;
            break;
          }
        case MatchExpr matchExpr:
          MatchStmtVerifier.TrMatchExpr(this, matchExpr, wfOptions, locals, builder, etran, addResultCommands);
          addResultCommands = null;
          break;
        case DatatypeUpdateExpr updateExpr: {
            var e = updateExpr;
            // check that source expression is created from one of the legal source constructors, then proceed according to the .ResolvedExpression
            var correctConstructor = BplOr(e.LegalSourceConstructors.ConvertAll(
              ctor => FunctionCall(e.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Root))));
            if (e.LegalSourceConstructors.Count == e.Type.AsDatatype.Ctors.Count) {
              // Every constructor has this destructor; no need to check anything
            } else {
              builder.Add(Assert(GetToken(expr), correctConstructor,
                new ValidConstructorNames(updateExpr.Root, e.LegalSourceConstructors), builder.Context));
            }

            CheckNotGhostVariant(e.InCompiledContext, updateExpr, e.Root, "update of", e.Members,
              e.LegalSourceConstructors, builder, etran);

            CheckWellformedWithResult(e.ResolvedExpression, wfOptions, locals, builder, etran, addResultCommands);
            addResultCommands = null;
            break;
          }
        case ConcreteSyntaxExpression expression: {
            var e = expression;
            CheckWellformedWithResult(e.ResolvedExpression, wfOptions, locals, builder, etran, addResultCommands);
            addResultCommands = null;
            break;
          }
        case NestedMatchExpr nestedMatchExpr:
          CheckWellformedWithResult(nestedMatchExpr.Flattened, wfOptions, locals, builder, etran, addResultCommands);
          addResultCommands = null;
          break;
        case BoogieFunctionCall call: {
            var e = call;
            foreach (var arg in e.Args) {
              CheckWellformed(arg, wfOptions, locals, builder, etran);
            }

            break;
          }
        case DecreasesToExpr decreasesToExpr: {
            foreach (var subexpr in decreasesToExpr.SubExpressions) {
              CheckWellformed(subexpr, wfOptions, locals, builder, etran);
            }
            break;
          }
        case FieldLocation: {
            // Nothing to verify
            break;
          }
        case LocalsObjectExpression: {
            // Nothing to verify
            break;
          }
        case IndexFieldLocation ifl: {
            // Verify similar to MultiSelectExpr, except we don't actually read the location
            // The well-formedness of the array should already have been established.
            // However, we also need the array to be non-null and allocated
            var array = CheckNonNullAndAllocated(builder, etran, ifl.ResolvedArrayCopy);
            CheckWellFormednessOfIndexList(wfOptions, locals, builder, etran,
              ifl.Indices, array, ifl.ResolvedArrayCopy, ifl);
            // We don't do reads checks as we are not reading the heap
            break;
          }
        default:
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected expression
      }

      addResultCommands?.Invoke(builder, expr);
    }

    private void CheckWellFormednessOfIndexList(WFOptions wfOptions, Variables locals, BoogieStmtListBuilder builder,
      ExpressionTranslator etran, List<Expression> indices, Expr array, Expression arrayExpression, Expression e) {
      for (int idxId = 0; idxId < indices.Count; idxId++) {
        var idx = indices[idxId];
        CheckWellformed(idx, wfOptions, locals, builder, etran);

        var index = etran.TrExpr(idx);
        index = ConvertExpression(idx.Origin, index, idx.Type, Type.Int);
        var lower = Bpl.Expr.Le(Bpl.Expr.Literal(0), index);
        var length = ArrayLength(idx.Origin, array, indices.Count, idxId);
        var upper = Bpl.Expr.Lt(index, length);
        var tok = idx is IdentifierExpr ? e.Origin : idx.Origin; // TODO: Reusing the token of an identifier expression would underline its definition. but this is still not perfect.

        var desc = new InRange(arrayExpression, indices[idxId], true, $"index {idxId}", idxId);
        builder.Add(Assert(tok, BplAnd(lower, upper), desc, builder.Context, wfOptions.AssertKv));
      }
    }

    private Expr CheckNonNullAndAllocated(BoogieStmtListBuilder builder, ExpressionTranslator etran, Expression obj) {
      Bpl.Expr array = etran.TrExpr(obj);
      builder.Add(Assert(GetToken(obj), Bpl.Expr.Neq(array, Predef.Null),
        new NonNull("array", obj), builder.Context));

      if (etran.UsesOldHeap) {
        builder.Add(Assert(GetToken(obj), MkIsAlloc(array, obj.Type, etran.HeapExpr),
          new IsAllocated("array", null, obj), builder.Context));
      }
      return array;
    }

    public void CheckSubsetType(ExpressionTranslator etran, Expression expr, Bpl.Expr selfCall, Type resultType,
      BoogieStmtListBuilder builder, string comment) {

      Contract.Assert(resultType != null);
      builder.Add(TrAssumeCmd(expr.Origin, etran.CanCallAssumption(expr)));
      var bResult = etran.TrExpr(expr);
      CheckSubrange(expr.Origin, bResult, expr.Type, resultType, expr, builder);
      builder.Add(TrAssumeCmdWithDependenciesAndExtend(etran, expr.Origin, expr,
        e => Bpl.Expr.Eq(selfCall, AdaptBoxing(expr.Origin, e, expr.Type, resultType)), comment));
      builder.Add(new CommentCmd("CheckWellformedWithResult: any expression"));
      builder.Add(TrAssumeCmd(expr.Origin, MkIs(selfCall, resultType)));
    }

    private void CheckWellformedStmtExpr(StmtExpr stmtExpr, WFOptions wfOptions, Variables locals,
      BoogieStmtListBuilder builder, ExpressionTranslator etran, AddResultCommands addResultCommands) {

      var statements = new List<Statement>() { stmtExpr.S };
      Expression expression = stmtExpr.E;
      while (expression is StmtExpr nestedStmtExpr) {
        statements.Add(nestedStmtExpr.S);
        expression = nestedStmtExpr.E;
      }

      // If we're inside an "old" expression, then "etran" will know how to translate
      // expressions. However, here, we're also having to translate e.S, which is a
      // Statement. Since statement translation (in particular, translation of CallStmt's)
      // work directly on the global variable $Heap, we temporarily change its value here.
      if (etran.UsesOldHeap) {
        BuildWithHeapAs(stmtExpr.S.Origin, etran.HeapExpr, "StmtExpr#", locals, builder,
          () => {
            foreach (var statement in statements) {
              TrStmt(statement, builder, locals, etran);
            }
          });
      } else {
        foreach (var statement in statements) {
          TrStmt(statement, builder, locals, etran);
        }
      }

      CheckWellformedWithResult(expression, wfOptions, locals, builder, etran, addResultCommands);
    }

    /// <summary>
    /// Temporarily set the heap to the value etran.HeapExpr and call build().
    ///
    /// The Boogie code generated by build() should have just one exit point, namely at the
    /// end of the code generated. (Any other exit would cause control flow to miss
    /// BuildWithHeapAs's assignment that restores the value of $Heap.)
    /// </summary>
    void BuildWithHeapAs(IOrigin token, Bpl.Expr temporaryHeap, string heapVarSuffix, Variables locals,
      BoogieStmtListBuilder builder, System.Action build) {
      var suffix = CurrentIdGenerator.FreshId(heapVarSuffix);
      var tmpHeapVar = locals.GetOrAdd(new Bpl.LocalVariable(token, new Bpl.TypedIdent(token, "Heap$" + suffix, Predef.HeapType)));
      var tmpHeap = new Bpl.IdentifierExpr(token, tmpHeapVar);
      var generalEtran = new ExpressionTranslator(this, Predef, token, null);
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
      CheckNotGhostVariant(expr.InCompiledContext, expr, expr.Obj, whatKind, [expr.Member],
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
            ctor => Bpl.Expr.Not(FunctionCall(exprUsedForToken.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, obj))));
          builder.Add(Assert(GetToken(exprUsedForToken), notGhostCtor,
            new NotGhostVariant(whatKind,
              Util.PrintableNameList(members.ConvertAll(member => member.Name), "and"),
              datatypeValue,
              enclosingGhostConstructors), builder.Context));
        }
      }
    }

    void CheckWellformedSpecialFunction(FunctionCallExpr expr, WFOptions options, Bpl.Expr result, Type resultType,
      Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr.Function is SpecialFunction);

      CheckWellformed(expr.Receiver, options, locals, builder, etran);
      foreach (var arg in expr.Args.Where(arg => arg is not DefaultValueExpression)) {
        CheckWellformed(arg, options, locals, builder, etran);
      }
      if (expr.Function.Name is "RotateLeft" or "RotateRight") {
        var w = expr.Type.AsBitVectorType.Width;
        var arg = expr.Args[0];
        builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(arg)),
          new ShiftLowerBound(false, arg), builder.Context, options.AssertKv));
        builder.Add(Assert(GetToken(expr), Bpl.Expr.Le(etran.TrExpr(arg), Bpl.Expr.Literal(w)),
          new ShiftUpperBound(w, false, arg), builder.Context, options.AssertKv));
      }
    }

    public delegate void AddResultCommands(BoogieStmtListBuilder builder, Expression result);

    void CheckWellformedLetExprWithResult(LetExpr e, WFOptions wfOptions, Variables locals,
      BoogieStmtListBuilder builder, ExpressionTranslator etran, bool checkRhs, AddResultCommands addResultCommands) {
      if (e.Exact) {
        // Note, in the following line, we do NOT add an assumption about the type antecedent, because we don't yet know that a value even
        // exists; rather, we ignore the type antecedent.
        var substMap = SetupBoundVarsAsLocals(e.BoundVars.ToList<BoundVar>(), out _, builder, locals, etran, "#Z");
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("let#");
        for (int i = 0; i < e.LHSs.Count; i++) {
          var pat = e.LHSs[i];
          var rhs = e.RHSs[i];
          var nm = varNameGen.FreshId($"#{i}#");
          var r = locals.GetOrAdd(new Bpl.LocalVariable(pat.Origin, new Bpl.TypedIdent(pat.Origin, nm, TrType(pat.Expr.Type))));
          var rIe = new Bpl.IdentifierExpr(rhs.Origin, r);

          void CheckPostconditionForRhs(BoogieStmtListBuilder innerBuilder, Expression body) {
            CheckSubsetType(etran, body, rIe, pat.Expr.Type, innerBuilder, "let expression binding RHS well-formed");
          }

          CheckWellformedWithResult(e.RHSs[i], wfOptions, locals, builder, etran, CheckPostconditionForRhs);
          CheckCasePatternShape(pat, rhs, rIe, rhs.Origin, pat.Expr.Type, builder);
          var substExpr = Substitute(pat.Expr, null, substMap);
          builder.Add(TrAssumeCmdWithDependenciesAndExtend(etran, e.Origin, substExpr, e => Bpl.Expr.Eq(e, rIe), "let expression binding"));
        }
        CheckWellformedWithResult(Substitute(e.Body, null, substMap), wfOptions, locals, builder, etran, addResultCommands);

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
          var wellFormednessBuilder = new BoogieStmtListBuilder(this, this.options, builder.Context);
          CheckWellformed(rhs, wfOptions, locals, wellFormednessBuilder, etran);
          var ifCmd = new Bpl.IfCmd(e.Origin, typeAntecedent, wellFormednessBuilder.Collect(e.Origin), null, null);
          builder.Add(ifCmd);

          var bounds = lhsVars.ConvertAll(_ => (BoundedPool)new SpecialAllocIndependenceAllocatedBoundedPool());  // indicate "no alloc" (is this what we want?)
          GenerateAndCheckGuesses(e.Origin, lhsVars, bounds, e.RHSs[0], e.Attributes, Attributes.Contains(e.Attributes, "_noAutoTriggerFound"),
            builder, etran);
        }
        // assume typeAntecedent(b);
        builder.Add(TrAssumeCmd(e.Origin, typeAntecedent));
        // assume RHS(b);
        builder.Add(TrAssumeCmd(e.Origin, etran.TrExpr(rhs)));
        var letBody = Substitute(e.Body, null, substMap);
        CheckWellformed(letBody, wfOptions, locals, builder, etran);
        if (e.Constraint_Bounds != null) {
          var substMap2 = SetupBoundVarsAsLocals(lhsVars, builder, locals, etran);
          var nonGhostMapPrime = new Dictionary<IVariable, Expression>();
          foreach (BoundVar bv in lhsVars) {
            nonGhostMapPrime.Add(bv, bv.IsGhost ? substMap[bv] : substMap2[bv]);
          }
          var rhsPrime = Substitute(e.RHSs[0], null, nonGhostMapPrime);
          var letBodyPrime = Substitute(e.Body, null, nonGhostMapPrime);
          builder.Add(TrAssumeCmd(e.Origin, etran.CanCallAssumption(rhsPrime)));
          builder.Add(TrAssumeCmdWithDependencies(etran, e.Origin, rhsPrime, "assign-such-that constraint"));
          builder.Add(TrAssumeCmd(e.Origin, etran.CanCallAssumption(letBodyPrime)));
          var eq = Expression.CreateEq(letBody, letBodyPrime, e.Body.Type);
          builder.Add(Assert(GetToken(e), etran.TrExpr(eq),
            new LetSuchThatUnique(e.RHSs[0], e.BoundVars.ToList()), builder.Context));
        }
        // assume $let$canCall(g);
        etran.LetDesugaring(e);  // call LetDesugaring to prepare the desugaring and populate letSuchThatExprInfo with something for e
        var info = letSuchThatExprInfo[e];
        builder.Add(new Bpl.AssumeCmd(e.Origin, info.CanCallFunctionCall(this, etran)));
        // If we are supposed to assume "result" to equal this expression, then use the body of the let-such-that, not the generated $let#... function
        addResultCommands?.Invoke(builder, letBody);
      }
    }

    void CheckFrameWellFormed(WFOptions wfo, List<FrameExpression> fes, Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(fes != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      foreach (var fe in fes) {
        CheckWellformed(fe.E, wfo, locals, builder, etran);
        if (fe.Field != null && fe.E.Type.IsRefType) {
          builder.Add(Assert(fe.Origin, Bpl.Expr.Neq(etran.TrExpr(fe.E), Predef.Null), new FrameDereferenceNonNull(fe.E), builder.Context));
        }
      }
    }


    /// <summary>
    /// Check that all indices are in the domain of the given function.  That is, for an array ("forArray"):
    ///     assert (forall i0,i1,i2,... :: 0 <= i0 < dims[0] && ... ==> init.requires(i0,i1,i2,...));
    /// and for a sequence ("!forArray"):
    ///     assert (forall i0 :: 0 <= i0 < dims[0] && ... ==> init.requires(i0));
    /// </summary>
    private void CheckElementInit(IOrigin tok, bool forArray, List<Expression> dims, Type elementType, Expression init,
      Bpl.IdentifierExpr/*?*/ nw, BoogieStmtListBuilder builder, ExpressionTranslator etran, WFOptions options) {
      Contract.Requires(tok != null);
      Contract.Requires(dims != null && dims.Count != 0);
      Contract.Requires(elementType != null);
      Contract.Requires(init != null);
      Contract.Requires(!forArray || nw != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);

      Bpl.Expr ante = Bpl.Expr.True;
      var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator(forArray ? "arrayinit#" : "seqinit#");
      var bvs = new List<Bpl.Variable>();
      var indices = new List<Bpl.Expr>();
      for (var i = 0; i < dims.Count; i++) {
        var nm = varNameGen.FreshId(string.Format("#i{0}#", i));
        var bv = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, nm, Bpl.Type.Int));
        bvs.Add(bv);
        var ie = new Bpl.IdentifierExpr(tok, bv);
        indices.Add(ie);
        ante = BplAnd(ante, BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), ie), Bpl.Expr.Lt(ie, etran.TrExpr(dims[i]))));
      }

      var sourceType = init.Type.AsArrowType;
      Contract.Assert(sourceType.Args.Count == dims.Count);
      var args = Concat(
        Map(Enumerable.Range(0, dims.Count), ii => TypeToTy(sourceType.Args[ii])),
        Cons(TypeToTy(sourceType.Result),
          Cons(etran.HeapExpr,
            Cons(etran.TrExpr(init),
              indices.ConvertAll(idx => (Bpl.Expr)FunctionCall(tok, BuiltinFunction.Box, null, idx))))));
      // check precond
      var pre = FunctionCall(tok, Requires(dims.Count), Bpl.Type.Bool, args);
      var q = new Bpl.ForallExpr(tok, bvs, BplImp(ante, pre));
      var indicesDesc = new IndicesInDomain(forArray ? "array" : "sequence", dims, init);
      builder.Add(AssertAndForget(builder.Context, tok, q, indicesDesc));
      if (!forArray && options.DoReadsChecks) {
        // unwrap renamed local lambdas
        var unwrappedFunc = init;
        while (unwrappedFunc is ConcreteSyntaxExpression { ResolvedExpression: not null } cse) {
          unwrappedFunc = cse.ResolvedExpression;
        }
        if (unwrappedFunc is IdentifierExpr { Origin: var origin, DafnyName: var dafnyName }) {
          unwrappedFunc = new IdentifierExpr(origin, dafnyName);
        }
        // check read effects
        Type objset = program.SystemModuleManager.ObjectSetType();
        Expression wrap = new BoogieWrapper(
          FunctionCall(tok, Reads(1), TrType(objset), args),
          objset);
        var reads = new FrameExpression(tok, wrap, null);
        Action<IOrigin, Bpl.Expr, ProofObligationDescription, Bpl.QKeyValue> maker = (t, e, d, qk) => {
          var qe = new Bpl.ForallExpr(t, bvs, BplImp(ante, e));
          options.AssertSink(this, builder)(t, qe, d, qk);
        };

        Utils.MakeQuantifierVarsForDims(dims, out var indexVars, out var indexVarExprs, out var indicesRange);
        var readsCall = new ApplyExpr(
          Token.NoToken,
          new ExprDotName(Token.NoToken, unwrappedFunc, new Name("reads"), null),
          indexVarExprs,
          Token.NoToken
        );
        readsCall.Type = objset;
        var contextReads = GetContextReadsFrames();
        var readsDescExpr = new ForallExpr(
          Token.NoToken,
          indexVars,
          indicesRange,
          Utils.MakeDafnyFrameCheck(contextReads, readsCall, null),
          null
        );
        var readsDesc = new ReadFrameSubset("invoke the function passed as an argument to the sequence constructor", readsDescExpr);
        CheckFrameSubset(tok, [reads], null, null,
          etran, etran.ReadsFrame(tok), maker, (ta, qa) => builder.Add(new Bpl.AssumeCmd(ta, qa)), readsDesc, options.AssertKv);
      }
      // Check that the values coming out of the function satisfy any appropriate subset-type constraints
      var apply = UnboxUnlessInherentlyBoxed(FunctionCall(tok, Apply(dims.Count), TrType(elementType), args), elementType);

      CheckElementInitReturnSubrangeCheck(dims, init, out var dafnySource, out var checkContext);
      var cre = GetSubrangeCheck(apply.tok, apply, sourceType.Result, elementType, dafnySource, checkContext, out var subrangeDesc);
      if (cre != null) {
        // assert (forall i0,i1,i2,... ::
        //            0 <= i0 < ... && ... ==> init.requires(i0,i1,i2,...) is Subtype);
        q = new Bpl.ForallExpr(tok, bvs, BplImp(ante, cre));
        builder.Add(AssertAndForget(builder.Context, init.Origin, q, subrangeDesc));
      }

      if (forArray) {
        // Assume that array elements have initial values according to the given initialization function.  That is:
        // assume (forall i0,i1,i2,... :: { nw[i0,i1,i2,...] }
        //            0 <= i0 < ... && ... ==>
        //                CanCallAssumptions[[ init(i0,i1,i2,...) ]] &&
        //                nw[i0,i1,i2,...] == init.requires(i0,i1,i2,...));
        var dafnyInitApplication = new ApplyExpr(tok, init,
          bvs.ConvertAll(indexBv => (Expression)new BoogieWrapper(new Bpl.IdentifierExpr(indexBv.tok, indexBv), Type.Int)).ToList(),
          Token.NoToken) {
          Type = sourceType.Result
        };
        var canCall = etran.CanCallAssumption(dafnyInitApplication);

        var ai = ReadHeap(tok, etran.HeapExpr, nw, GetArrayIndexFieldName(tok, indices));
        var ai_prime = UnboxUnlessBoxType(tok, ai, elementType);
        var tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { ai });
        q = new Bpl.ForallExpr(tok, bvs, tr, BplImp(ante, BplAnd(canCall, Bpl.Expr.Eq(ai_prime, apply))));
        builder.Add(new Bpl.AssumeCmd(tok, q));
      }
    }

    private static void CheckElementInitReturnSubrangeCheck(List<Expression> dims, Expression init, out Expression dafnySource, out SubrangeCheckContext checkContext) {
      var quantifiedVars =
        Enumerable.Range(0, dims.Count)
          .Select(i => {
            var name = $"i{i}";
            var ident = new IdentifierExpr(Token.NoToken, name);
            var range = new BinaryExpr(
              Token.NoToken,
              BinaryExpr.Opcode.And,
              new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Le, new LiteralExpr(Token.NoToken, 0), ident),
              new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Lt, ident, dims[i])
            );
            return new QuantifiedVar(Token.NoToken, $"i{i}", Type.Int, null, range);
          })
          .ToList();
      dafnySource = new ApplyExpr(
        Token.NoToken,
        init,
        quantifiedVars
          .Select(ident => new IdentifierExpr(ident.Origin, ident) as Expression)
          .ToList(),
        Token.NoToken
      );
      QuantifiedVar.ExtractSingleRange(quantifiedVars, out var boundVars, out var singleRange);
      checkContext = check => new ForallExpr(Token.NoToken, boundVars, singleRange, check, null);
    }
  }
}
