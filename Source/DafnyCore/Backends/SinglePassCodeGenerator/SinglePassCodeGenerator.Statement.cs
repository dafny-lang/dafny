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
    private VarDeclStmt enclosingVarDecl = null;
    private int innerExtractIndex = -1;

    private bool IsExtractStatement(Statement stmt, string expectedLeftName) {
      return stmt is AssignStatement updateStmt
             && updateStmt.Rhss.Count() == 1
             && updateStmt.Lhss.Count() == 1
             && updateStmt.Lhss[0] is IdentifierExpr { Name: var leftName }
             && leftName == expectedLeftName
             && updateStmt.Rhss[0] is ExprRhs { Expr: ApplySuffix { Lhs: ExprDotName { SuffixName: "Extract" } } };
    }

    private int FindExtractStatement(List<Statement> stmts, string expectedLeftName) {
      return stmts.FindIndex((stmt) => IsExtractStatement(stmt, expectedLeftName));
    }

    protected void TrStmt(Statement stmt, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts = null) {
      Contract.Requires(stmt != null);
      Contract.Requires(wr != null);

      wStmts ??= wr.Fork();

      if (stmt.IsGhost) {
        return;
      }

      stmt = Statement.StripByBlocks(stmt);
      switch (stmt) {
        case PrintStmt printStmt: {
            var s = printStmt;
            foreach (var arg in s.Args) {
              EmitPrintStmt(wr, arg);
            }

            break;
          }
        case BreakOrContinueStmt breakStmt: {
            var s = breakStmt;
            var label = s.TargetStmt.Labels.First().AssignUniqueId(idGenerator);
            if (s.IsContinue) {
              EmitContinue(label, wr);
            } else {
              EmitBreak(label, wr);
            }

            break;
          }
        case ProduceStmt produceStmt: {
            var s = produceStmt;
            var isTailRecursiveResult = false;
            if (s.HiddenUpdate != null) {
              TrStmt(s.HiddenUpdate, wr);
              var ss = s.HiddenUpdate.ResolvedStatements;
              if (ss.Count == 1 && ss[0] is SingleAssignStmt assign && assign.Rhs is ExprRhs eRhs && eRhs.Expr.Resolved is FunctionCallExpr fce && IsTailRecursiveByMethodCall(fce)) {
                isTailRecursiveResult = true;
              }
            }
            if (s is YieldStmt) {
              EmitYield(wr);
            } else if (!isTailRecursiveResult) {
              EmitReturn(this.enclosingMethod.Outs, wr);
            }

            break;
          }
        case AssignStatement updateStmt: {
            var s = updateStmt;
            var resolved = s.ResolvedStatements;
            if (resolved.Count == 1) {
              TrStmt(resolved[0], wr);
            } else {
              var assignStmts = resolved.Cast<SingleAssignStmt>().Where(assignStmt => !assignStmt.IsGhost).ToList();
              var lhss = new List<Expression>();
              var rhss = new List<AssignmentRhs>();

              // multi-assignment
              Contract.Assert(s.Lhss.Count == resolved.Count);
              Contract.Assert(s.Rhss.Count == resolved.Count);
              var lhsTypes = new List<Type>();
              var rhsTypes = new List<Type>();
              foreach (var assignStmt in assignStmts) {
                var rhs = assignStmt.Rhs;
                if (rhs is not HavocRhs) {
                  var lhs = assignStmt.Lhs;
                  rhss.Add(rhs);
                  lhss.Add(lhs);
                  lhsTypes.Add(lhs.Type);
                  rhsTypes.Add(TypeOfRhs(rhs));
                }
              }

              var wStmtsPre = wStmts.Fork();
              var lvalues = new List<ILvalue>();
              foreach (Expression lhs in lhss) {
                lvalues.Add(CreateLvalue(lhs, wStmts, wStmtsPre));
              }

              EmitMultiAssignment(lhss, lvalues, lhsTypes, out var wRhss, rhsTypes, wr);
              for (int i = 0; i < wRhss.Count; i++) {
                TrRhs(rhss[i], wRhss[i], wStmts);
              }
            }

            break;
          }
        case SingleAssignStmt assignStmt: {
            var s = assignStmt;
            Contract.Assert(s.Lhs is not SeqSelectExpr expr || expr.SelectOne);  // multi-element array assignments are not allowed
            if (s.Rhs is HavocRhs) {
            } else if (s.Rhs is TypeRhs typeRhs) {
              var lvalue = CreateLvalue(s.Lhs, wr, wStmts);
              wStmts = wr.Fork();
              var wRhs = EmitAssignment(lvalue, TypeOfLhs(s.Lhs), TypeOfRhs(typeRhs), wr, assignStmt.Origin);
              TrRhs(typeRhs, wRhs, wStmts);
            } else {
              var eRhs = (ExprRhs)s.Rhs;
              if (eRhs.Expr.Resolved is FunctionCallExpr fce && IsTailRecursiveByMethodCall(fce)) {
                TrTailCallStmt(s.Origin, fce.Function.ByMethodDecl, fce.Receiver, fce.Args, wr);
              } else {
                var lvalue = CreateLvalue(s.Lhs, wr, wStmts);
                var doAssignment = (Expression e, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wrAssignment) => {
                  var wStmtsBeforeAssignment = wrAssignment.Fork();
                  var wRhs = EmitAssignment(lvalue, resultType, e.Type, wrAssignment, assignStmt.Origin);
                  EmitExpr(e, false, wRhs, wStmtsBeforeAssignment);
                };
                var continuation = new OptimizedExpressionContinuation(doAssignment, true);
                TrExprOpt(eRhs.Expr, TypeOfLhs(s.Lhs), wr, wStmts, false, null, continuation);
              }
            }

            break;
          }
        case AssignSuchThatStmt thatStmt: {
            var s = thatStmt;
            var lhss = s.Lhss.ConvertAll(lhs => ((IdentifierExpr)lhs.Resolved).Var);  // the resolver allows only IdentifierExpr left-hand sides
            var missingBounds = BoundedPool.MissingBounds(lhss, s.Bounds, BoundedPool.PoolVirtues.Enumerable);
            if (missingBounds.Count != 0) {
              foreach (var bv in missingBounds) {
                Error(ErrorId.c_assign_such_that_is_too_complex, s.Origin, wr,
                  "this assign-such-that statement is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}'", bv.Name);
              }
            } else {
              Contract.Assert(s.Bounds != null);
              TrAssignSuchThat(lhss, s.Expr, s.Bounds, wr, false);
            }

            break;
          }
        case AssignOrReturnStmt assignOrReturnStmt: {
            var s = assignOrReturnStmt;
            var stmts = s.ResolvedStatements.ToList();
            if (innerExtractIndex != -1 &&
                enclosingVarDecl is { Assign: var stmtUpdate, Locals: { Count: > 0 } locals }
                && stmtUpdate == assignOrReturnStmt) {
              // Wrap this UpdateStmt with a VarDecl containing this Local that we haven't emitted yet.
              stmts[innerExtractIndex] =
                new VarDeclStmt(enclosingVarDecl.Origin,
                  [locals[0]],
                  (AssignStatement)stmts[innerExtractIndex]);
            }
            TrStmtList(stmts, wr);

            break;
          }
        case ExpectStmt expectStmt: {
            // TODO there's potential here to use target-language specific features such as exceptions
            // to make it more target-language idiomatic and improve performance
            // For now, this code prints nicely only in the Rust code generator until we make it work for every code generator
            var specialExpectEqualHandling = Options.Backend.TargetId == "rs";
            if (
              specialExpectEqualHandling &&
              expectStmt.Expr is BinaryExpr { Op: BinaryExpr.Opcode.Eq, ResolvedOp: var resolvedOp, E0: var e0, E1: var e1 }) {
              // If it finds "expect a == b", it will rewrite the code to
              // var _e0 = a;
              // var _e1 = b;
              // if _e0 != _e1 {
              //   print "\nLeft:\n"
              //   print _e0;
              //   print "\nRight:\n"
              //   print _e1;
              //   <Halt statement>
              // }
              var e0Name = ProtectedFreshId("_e0");
              var e1Name = ProtectedFreshId("_e1");
              var e0Var = new LocalVariable(new SourceOrigin(Token.NoToken, Token.NoToken), e0Name, e0.Type, false);
              var e1Var = new LocalVariable(new SourceOrigin(Token.NoToken, Token.NoToken), e1Name, e0.Type, false);
              DeclareLocalVar(IdName(e0Var), null, e0.Origin, e0, false, wr);
              DeclareLocalVar(IdName(e1Var), null, e1.Origin, e1, false, wr);
              var e0Ident = new IdentifierExpr(e0.Origin, e0Name) {
                Type = e0.Type,
                Var = e0Var
              };
              var e1Ident = new IdentifierExpr(e1.Origin, e0Name) {
                Type = e1.Type,
                Var = e1Var
              };

              ConcreteSyntaxTree bodyWriter = EmitIf(out var guardWriter, false, wr);
              var negated = new UnaryOpExpr(expectStmt.Origin, UnaryOpExpr.Opcode.Not,
                new BinaryExpr(expectStmt.Expr.Origin, BinaryExpr.Opcode.Eq,
                  e0Ident,
                  e1Ident) {
                  ResolvedOp = resolvedOp,
                  Type = Type.Bool
                }) {
                Type = Type.Bool
              };
              EmitExpr(negated, false, guardWriter, wStmts);
              EmitPrintStmt(bodyWriter, new StringLiteralExpr(e0.Origin, @"\nLeft:\n", false) {
                Type = new SeqType(new CharType())
              });
              EmitPrintStmt(bodyWriter, e0Ident);
              EmitPrintStmt(bodyWriter, new StringLiteralExpr(e1.Origin, @"\nRight:\n", false) {
                Type = new SeqType(new CharType())
              });
              EmitPrintStmt(bodyWriter, e1Ident);

              EmitHalt(expectStmt.Origin, expectStmt.Message, bodyWriter);
            } else {
              ConcreteSyntaxTree bodyWriter = EmitIf(out var guardWriter, false, wr);
              var negated = new UnaryOpExpr(expectStmt.Origin, UnaryOpExpr.Opcode.Not, expectStmt.Expr) { Type = Type.Bool };
              EmitExpr(negated, false, guardWriter, wStmts);

              EmitHalt(expectStmt.Origin, expectStmt.Message, bodyWriter);
            }

            break;
          }
        case CallStmt callStmt: {
            var s = callStmt;
            var wrBefore = wr.Fork();
            var wrCall = wr.Fork();
            var wrAfter = wr;
            TrCallStmt(s, null, wrCall, wrBefore, wrAfter);
            break;
          }
        case BlockStmt blockStmt: {
            var w = EmitBlock(wr);
            TrStmtList(blockStmt.Body, w);
            break;
          }
        case IfStmt ifStmt: {
            IfStmt s = ifStmt;
            if (s.Guard == null) {
              // we can compile the branch of our choice
              ConcreteSyntaxTree guardWriter;
              if (s.Els == null) {
                // let's compile the "else" branch, since that involves no work
                // (still, let's leave a marker in the source code to indicate that this is what we did)
                Coverage.UnusedInstrumentationPoint(s.Thn.Origin, "then branch");
                var notFalse = (UnaryOpExpr)Expression.CreateNot(s.Thn.Origin, Expression.CreateBoolLiteral(s.Thn.Origin, false));
                var thenWriter = EmitIf(out guardWriter, false, wr);
                EmitUnaryExpr(ResolvedUnaryOp.BoolNot, notFalse.E, false, guardWriter, wStmts);
                Coverage.Instrument(s.Origin, "implicit else branch", wr);
                thenWriter = EmitIf(out guardWriter, false, thenWriter);
                EmitUnaryExpr(ResolvedUnaryOp.BoolNot, notFalse.E, false, guardWriter, wStmts);
                TrStmtList([], thenWriter);
              } else {
                // let's compile the "then" branch
                wr = EmitIf(out guardWriter, false, wr);
                EmitExpr(Expression.CreateBoolLiteral(s.Thn.Origin, true), false, guardWriter, wStmts);
                Coverage.Instrument(s.Thn.Origin, "then branch", wr);
                TrStmtList(s.Thn.Body, wr);
                Coverage.UnusedInstrumentationPoint(s.Els.Origin, "else branch");
              }
            } else {
              var coverageForElse = Coverage.IsRecording && !(s.Els is IfStmt);
              var thenWriter = EmitIf(out var guardWriter, s.Els != null || coverageForElse, wr);
              EmitExpr(s.IsBindingGuard ? ((ExistsExpr)s.Guard).AlphaRename("eg_d") : s.Guard, false, guardWriter, wStmts);
              // We'd like to do "TrStmt(s.Thn, indent)", except we want the scope of any existential variables to come inside the block
              if (s.IsBindingGuard) {
                IntroduceAndAssignBoundVars((ExistsExpr)s.Guard, thenWriter);
              }
              Coverage.Instrument(s.Thn.Origin, "then branch", thenWriter);
              TrStmtList(s.Thn.Body, thenWriter);

              if (coverageForElse) {
                wr = EmitBlock(wr);
                if (s.Els == null) {
                  Coverage.Instrument(s.Origin, "implicit else branch", wr);
                } else {
                  Coverage.Instrument(s.Els.Origin, "else branch", wr);
                }
              }
              if (s.Els != null) {
                TrStmtNonempty(s.Els, wr, wStmts);
              }
            }

            break;
          }
        case AlternativeStmt alternativeStmt: {
            var s = alternativeStmt;
            foreach (var alternative in s.Alternatives) {
              var thn = EmitIf(out var guardWriter, true, wr);
              EmitExpr(alternative.IsBindingGuard ? ((ExistsExpr)alternative.Guard).AlphaRename("eg_d") : alternative.Guard, false, guardWriter, wStmts);
              if (alternative.IsBindingGuard) {
                IntroduceAndAssignBoundVars((ExistsExpr)alternative.Guard, thn);
              }
              Coverage.Instrument(alternative.Origin, "if-case branch", thn);
              TrStmtList(alternative.Body, thn);
            }
            var wElse = EmitBlock(wr);
            EmitAbsurd("unreachable alternative", wElse);
            break;
          }
        case WhileStmt whileStmt: {
            WhileStmt s = whileStmt;
            if (s.Body == null) {
              return;
            }
            if (s.Guard == null) {
              // This loop is allowed to stop iterating at any time. We choose to never iterate, but we still
              // emit a loop structure. The structure "while (false) { }" comes to mind, but that results in
              // an "unreachable code" error from Java, so we instead use "while (true) { break; }".
              var wBody = CreateWhileLoop(out var guardWriter, wr);
              EmitExpr(Expression.CreateBoolLiteral(s.Body.Origin, true), false, guardWriter, wStmts);
              EmitBreak(null, wBody);
              Coverage.UnusedInstrumentationPoint(s.Body.Origin, "while body");
            } else {
              var guardWriter = EmitWhile(s.Body.Origin, s.Body.Body, s.Labels, wr);
              EmitExpr(s.Guard, false, guardWriter, wStmts);
            }

            break;
          }
        case AlternativeLoopStmt loopStmt: {
            if (loopStmt.Alternatives.Count != 0) {
              var w = CreateWhileLoop(out var whileGuardWriter, wr);
              EmitExpr(Expression.CreateBoolLiteral(loopStmt.Origin, true), false, whileGuardWriter, wStmts);
              w = EmitContinueLabel(loopStmt.Labels, w);
              foreach (var alternative in loopStmt.Alternatives) {
                var thn = EmitIf(out var guardWriter, true, w);
                EmitExpr(alternative.Guard, false, guardWriter, wStmts);
                Coverage.Instrument(alternative.Origin, "while-case branch", thn);
                TrStmtList(alternative.Body, thn);
              }
              var wElse = EmitBlock(w);
              {
                EmitBreak(null, wElse);
              }
            }

            break;
          }
        case ForLoopStmt loopStmt: {
            var s = loopStmt;
            if (s.Body == null) {
              return;
            }
            string endVarName = null;
            if (s.End != null) {
              // introduce a variable to hold the value of the end-expression
              endVarName = ProtectedFreshId(s.GoingUp ? "_hi" : "_lo");
              wStmts = wr.Fork();
              EmitExpr(s.End, false, DeclareLocalVar(endVarName, s.End.Type, s.End.Origin, wr), wStmts);
            }
            var startExprWriter = EmitForStmt(s.Origin, s.LoopIndex, s.GoingUp, endVarName, s.Body.Body, s.Labels, wr);
            EmitExpr(s.Start, false, startExprWriter, wStmts);
            break;
          }
        case ForallStmt forallStmt: {
            var s = forallStmt;
            if (s.Kind != ForallStmt.BodyKind.Assign) {
              // Call and Proof have no side effects, so they can simply be optimized away.
              return;
            } else if (s.BoundVars.Count == 0) {
              // the bound variables just spell out a single point, so the forall statement is equivalent to one execution of the body
              TrStmt(s.Body, wr);
              return;
            }
            var s0 = (SingleAssignStmt)s.S0;
            if (s0.Rhs is HavocRhs) {
              // The forall statement says to havoc a bunch of things.  This can be efficiently compiled
              // into doing nothing.
              return;
            }
            var rhs = ((ExprRhs)s0.Rhs).Expr;

            if (CanSequentializeForall(s.BoundVars, s.Bounds, s.Range, s0.Lhs, rhs)) {
              // Just put the statement inside the loops
              var wLoop = CompileGuardedLoops(s.BoundVars, s.Bounds, s.Range, wr);
              TrStmt(s0, wLoop);
            } else {
              // Compile:
              //   forall (w,x,y,z | Range(w,x,y,z)) {
              //     LHS(w,x,y,z) := RHS(w,x,y,z);
              //   }
              // where w,x,y,z have types seq<W>,set<X>,int,bool and LHS has L-1 top-level subexpressions
              // (that is, L denotes the number of top-level subexpressions of LHS plus 1),
              // into:
              //   var ingredients = new List< L-Tuple >();
              //   foreach (W w in sq.UniqueElements) {
              //     foreach (X x in st.Elements) {
              //       for (BigInteger y = Lo; j < Hi; j++) {
              //         for (bool z in Helper.AllBooleans) {
              //           if (Range(w,x,y,z)) {
              //             ingredients.Add(new L-Tuple( LHS0(w,x,y,z), LHS1(w,x,y,z), ..., RHS(w,x,y,z) ));
              //           }
              //         }
              //       }
              //     }
              //   }
              //   foreach (L-Tuple l in ingredients) {
              //     LHS[ l0, l1, l2, ..., l(L-2) ] = l(L-1);
              //   }
              //
              // Note, because the .NET Tuple class only supports up to 8 components, the compiler implementation
              // here supports arrays only up to 6 dimensions.  This does not seem like a serious practical limitation.
              // However, it may be more noticeable if the forall statement supported forall assignments in its
              // body.  To support cases where tuples would need more than 8 components, .NET Tuple's would have to
              // be nested.

              // Temporary names
              var c = ProtectedFreshNumericId("_ingredients+_tup");
              string ingredients = "_ingredients" + c;
              string tup = "_tup" + c;

              // Compute L
              int L;
              string tupleTypeArgs;
              List<Type> tupleTypeArgsList;
              if (s0.Lhs is MemberSelectExpr) {
                var lhs = (MemberSelectExpr)s0.Lhs;
                L = 2;
                tupleTypeArgs = TypeArgumentName(lhs.Obj.Type, wr, lhs.Origin);
                tupleTypeArgsList = [lhs.Obj.Type];
              } else if (s0.Lhs is SeqSelectExpr) {
                var lhs = (SeqSelectExpr)s0.Lhs;
                L = 3;
                // note, we might as well do the BigInteger-to-int cast for array indices here, before putting things into the Tuple rather than when they are extracted from the Tuple
                tupleTypeArgs = TypeArgumentName(lhs.Seq.Type, wr, lhs.Origin) + IntSelect;
                tupleTypeArgsList = [lhs.Seq.Type, null];
              } else {
                var lhs = (MultiSelectExpr)s0.Lhs;
                L = 2 + lhs.Indices.Count;
                if (8 < L) {
                  Error(ErrorId.c_no_assignments_to_seven_d_arrays, lhs.Origin, wr, "compiler currently does not support assignments to more-than-6-dimensional arrays in forall statements");
                  return;
                }
                tupleTypeArgs = TypeArgumentName(lhs.Array.Type, wr, lhs.Origin);
                tupleTypeArgsList = [lhs.Array.Type];
                for (int i = 0; i < lhs.Indices.Count; i++) {
                  // note, we might as well do the BigInteger-to-int cast for array indices here, before putting things into the Tuple rather than when they are extracted from the Tuple
                  tupleTypeArgs += IntSelect;
                  tupleTypeArgsList.Add(null);
                }

              }
              tupleTypeArgs += "," + TypeArgumentName(rhs.Type, wr, rhs.Origin);
              tupleTypeArgsList.Add(rhs.Type);

              // declare and construct "ingredients"
              var wrOuter = EmitIngredients(wr, ingredients, L, tupleTypeArgs, s, s0, rhs);

              //   foreach (L-Tuple l in ingredients) {
              //     LHS[ l0, l1, l2, ..., l(L-2) ] = l(L-1);
              //   }
              TargetTupleSize = L;
              wr = CreateForeachIngredientLoop(tup, L, tupleTypeArgs, out var collWriter, wrOuter);
              collWriter.Write(ingredients);
              {
                var wTup = new ConcreteSyntaxTree(wr.RelativeIndentLevel);
                var wCoerceTup = EmitCoercionToArbitraryTuple(wTup);
                wCoerceTup.Write(tup);
                tup = wTup.ToString();
              }
              if (s0.Lhs is MemberSelectExpr) {
                EmitMemberSelect(s0, tupleTypeArgsList, wr, tup);
              } else if (s0.Lhs is SeqSelectExpr) {
                EmitSeqSelect(s0, tupleTypeArgsList, wr, tup);
              } else {
                EmitMultiSelect(s0, tupleTypeArgsList, wr, tup, L);
              }
            }

            break;
          }
        case NestedMatchStmt nestedMatchStmt:
          EmitNestedMatchStmt(nestedMatchStmt, wr);
          break;
        case MatchStmt matchStmt:
          EmitMatchStmt(wr, matchStmt);
          break;
        case VarDeclStmt declStmt: {
            var s = declStmt;
            var i = 0;
            // Optimization (especially useful for Rust) so that if we have
            // var o :- B;
            // We won't declare o until we assign it with o := tmp.Extract();
            var indexExtract = -1;
            if (s.Assign is AssignOrReturnStmt { ResolvedStatements: var stmts }
                && s.Locals.Count > 0) {
              indexExtract = FindExtractStatement(stmts, s.Locals[0].Name);
            }

            foreach (var local in s.Locals) {
              bool hasRhs = s.Assign is AssignSuchThatStmt || s.Assign is AssignOrReturnStmt;
              if (!hasRhs && s.Assign is AssignStatement u) {
                if (i < u.Rhss.Count && u.Rhss[i] is HavocRhs) {
                  // there's no specific initial value
                } else {
                  hasRhs = true;
                }
              }

              // The head variable of an elephant assignment will be declared by its desugaring
              if (i != 0 || indexExtract == -1) {
                TrLocalVar(local, !hasRhs, wr);
              }

              i++;
            }

            enclosingVarDecl = s;
            innerExtractIndex = indexExtract;
            if (s.Assign != null) {
              TrStmt(s.Assign, wr);
            }
            enclosingVarDecl = null;
            innerExtractIndex = -1;

            break;
          }
        case VarDeclPattern pattern: {
            var s = pattern;
            if (Contract.Exists(s.LHS.Vars, bv => !bv.IsGhost)) {
              TrCasePatternOpt(s.LHS, s.RHS, wr, false);
            }

            break;
          }
        case ModifyStmt modifyStmt: {
            var s = modifyStmt;
            if (s.Body != null) {
              TrStmt(s.Body, wr);
            }

            break;
          }
        case TryRecoverStatement h:
          EmitHaltRecoveryStmt(h.TryBody, IdName(h.HaltMessageVar), h.RecoverBody, wr);
          break;
        case BlockByProofStmt blockByProofStmt:
          TrStmt(blockByProofStmt.Body, wr, wStmts);
          break;
        case LabeledStatement:
          // content already handled
          break;
        default:
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected statement
      }
    }

    private void EmitMatchStmt(ConcreteSyntaxTree wr, MatchStmt s) {
      // Type source = e;
      // if (source.is_Ctor0) {
      //   FormalType f0 = ((Dt_Ctor0)source._D).a0;
      //   ...
      //   Body0;
      // } else if (...) {
      //   ...
      // } else if (true) {
      //   ...
      // }
      if (s.Cases.Count != 0) {
        string source = ProtectedFreshId("_source");
        DeclareLocalVar(source, s.Source.Type, s.Source.Origin, s.Source, false, wr);

        int i = 0;
        var sourceType = (UserDefinedType)s.Source.Type.NormalizeExpand();
        foreach (MatchCaseStmt mc in s.Cases) {
          var w = MatchCasePrelude(source, sourceType, Cce.NonNull(mc.Ctor), mc.Arguments, i, s.Cases.Count, wr);
          TrStmtList(mc.Body, w);
          i++;
        }
      }
    }

    protected virtual void EmitNestedMatchStmt(NestedMatchStmt match, ConcreteSyntaxTree writer) {
      EmitNestedMatchGeneric(match, true, (caseIndex, caseBody) => {
        TrStmtList(match.Cases[caseIndex].Body, caseBody);
      }, false, writer);
    }

    /// <summary>
    /// Given
    /// 
    ///   match a
    ///   case X(Y(b),Z(W(c)) => body1
    ///   case r => body2
    /// 
    /// If there are no cases, then emit:
    ///
    ///   throw ABSURD;
    ///
    /// Else, emit:
    /// 
    ///   BLOCK {
    ///     {  // this defines the scope for any new local variables in the case
    ///       if (a is X) {
    ///         var x0 = ((X)a).0;
    ///         if (x0 is Y) {
    ///           var b = ((Y)x0).0;
    /// 
    ///           var x1 = ((X)a).1; 
    ///           if (x1 is Z) {
    ///             var xz0 = ((Z)x1).0;
    ///             if (xz0 is W) {
    ///               var c = ((W)xz0).0;
    /// 
    ///               body1;
    ///               break BLOCK;
    ///           }
    ///         }
    ///       }
    ///     }
    /// 
    ///     {
    ///       var r = a;
    ///       body2;
    ///     }
    ///   }
    /// 
    /// </summary>
    private void EmitNestedMatchGeneric(INestedMatch match, bool preventCaseFallThrough, Action<int, ConcreteSyntaxTree> emitBody,
      bool inLetExprBody, ConcreteSyntaxTree output) {
      if (match.Cases.Count == 0) {
        // the verifier would have proved we never get here; still, we need some code that will compile
        EmitAbsurd(null, output);
      } else {
        string sourceName = ProtectedFreshId("_source");
        DeclareLocalVar(sourceName, match.Source.Type, match.Source.Origin, match.Source, inLetExprBody, output);

        var label = preventCaseFallThrough ? ProtectedFreshId("match") : null;
        if (label != null) {
          output = CreateLabeledCode(label, false, output);
        }

        var sourceType = match.Source.Type.NormalizeExpand();
        for (var index = 0; index < match.Cases.Count; index++) {
          var myCase = match.Cases[index];
          var lastCase = index == match.Cases.Count - 1;

          var caseBlock = EmitBlock(output);
          var innerWriter = EmitNestedMatchCaseConditions(sourceName, sourceType, myCase.Pat, caseBlock, lastCase);
          Coverage.Instrument(myCase.Origin, "case body", innerWriter);

          emitBody(index, innerWriter);
          if (label != null && !lastCase) {
            EmitBreak(label, innerWriter);
          }
        }
      }
    }

    private ConcreteSyntaxTree EmitNestedMatchCaseConditions(string sourceName, Type sourceType,
      ExtendedPattern pattern, ConcreteSyntaxTree writer, bool lastCase) {

      var litExpression = MatchFlattener.GetLiteralExpressionFromPattern(pattern);
      if (litExpression != null) {
        if (lastCase) {
          return writer;
        }

        var thenWriter = EmitIf(out var guardWriter, false, writer);
        CompileBinOp(BinaryExpr.ResolvedOpcode.EqCommon, sourceType, litExpression.Type, pattern.Origin, Type.Bool,
          out var opString, out var preOpString, out var postOpString, out var callString, out var staticCallString,
          out _, out _, out _, out _,
          writer);
        var right = new ConcreteSyntaxTree();
        EmitExpr(litExpression, false, right, writer);
        EmitBinaryExprUsingConcreteSyntax(guardWriter, Type.Bool, preOpString, opString, new LineSegment(sourceName), right, callString, staticCallString, postOpString);
        return thenWriter;

      } else if (pattern is IdPattern idPattern) {
        if (idPattern.BoundVar == null) {
          return EmitNestedMatchStmtCaseConstructor(sourceName, sourceType, idPattern, writer, lastCase);
        }

        var boundVar = idPattern.BoundVar;
        if (!boundVar.Name.StartsWith(IdPattern.WildcardString)) {
          var valueWriter = DeclareLocalVar(IdName(boundVar), boundVar.Type, idPattern.Origin, writer);
          valueWriter.Write(sourceName);
        }
        return writer;

      } else if (pattern is DisjunctivePattern disjunctivePattern) {
        if (lastCase) {
          return writer;
        }

        string disjunctiveMatch = ProtectedFreshId("disjunctiveMatch");
        DeclareLocalVar(disjunctiveMatch, Type.Bool, disjunctivePattern.Origin, Expression.CreateBoolLiteral(disjunctivePattern.Origin, false), false, writer);
        foreach (var alternative in disjunctivePattern.Alternatives) {
          var alternativeWriter = EmitNestedMatchCaseConditions(sourceName, sourceType, alternative, writer, lastCase);
          EmitAssignment(disjunctiveMatch, Type.Bool, True, Type.Bool, alternativeWriter);
        }
        writer = EmitIf(out var guardWriter, false, writer);
        guardWriter.Write(disjunctiveMatch);
        return writer;

      } else {
        throw new Exception();
      }
    }

    private ConcreteSyntaxTree EmitNestedMatchStmtCaseConstructor(string sourceName, Type sourceType,
      IdPattern idPattern,
      ConcreteSyntaxTree result, bool lastCase) {
      var ctor = idPattern.Ctor;

      if (!lastCase && ctor.EnclosingDatatype.Ctors.Count != 1) {
        result = EmitIf(out var guardWriter, false, result);
        EmitConstructorCheck(sourceName, ctor, guardWriter);
      }

      var userDefinedType = (UserDefinedType)sourceType.NormalizeExpand();

      var typeSubstMap =
        TypeParameter.SubstitutionMap(userDefinedType.ResolvedClass.TypeArgs, userDefinedType.TypeArgs);
      int nonGhostIndex = 0; // number of processed non-ghost arguments
      for (int index = 0; index < ctor.Formals.Count; index++) {
        var arg = ctor.Formals[index];

        if (arg.IsGhost) {
          continue;
        }

        var type = arg.Type.Subst(typeSubstMap);
        // ((Dt_Ctor0)source._D).a0;
        var destructor = new ConcreteSyntaxTree();
        EmitDestructor(wr => EmitIdentifier(sourceName, wr), arg, nonGhostIndex, ctor,
          () => SelectNonGhost(userDefinedType.ResolvedClass, userDefinedType.TypeArgs), type, destructor);

        if (idPattern.Arguments != null) {
          string newSourceName;
          var childPattern = idPattern.Arguments[index];
          if (childPattern is IdPattern { BoundVar: not null } childIdPattern) {
            var boundVar = childIdPattern.BoundVar;
            if (!childIdPattern.BoundVar.Name.StartsWith(IdPattern.WildcardString)) {
              newSourceName = IdName(boundVar);
              var valueWriter = DeclareLocalVar(newSourceName, boundVar.Type, idPattern.Origin, result);
              valueWriter.Append(destructor);
            }
          } else {
            newSourceName = ProtectedFreshId(arg.GetOrCreateCompileName(currentIdGenerator));
            var valueWriter = DeclareLocalVar(newSourceName, type, idPattern.Origin, result);
            valueWriter.Append(destructor);
            result = EmitNestedMatchCaseConditions(newSourceName, type, childPattern, result, lastCase);
          }
        }
        nonGhostIndex++;
      }

      return result;
    }
  }
}
