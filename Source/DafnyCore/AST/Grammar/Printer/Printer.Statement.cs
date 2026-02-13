//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.IO;
using System.Collections.Generic;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using DafnyCore;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  interface ICanPrint {
    void Render(TextWriter wr, Printer printer, int indent);
  }

  public partial class Printer {

    /// <summary>
    /// Prints from the current position of the current line.
    /// If the statement requires several lines, subsequent lines are indented at "indent".
    /// No newline is printed after the statement.
    /// </summary>
    public void PrintStatement(Statement stmt, int indent, bool includeSemicolon = true) {
      Contract.Requires(stmt != null);

      if (stmt.IsGhost && printMode == PrintModes.NoGhostOrIncludes) {
        return;
      }

      if (stmt is LabeledStatement labelledStatement) {
        for (var index = 0; index < labelledStatement.Labels.Count; index++) {
          var label = labelledStatement.Labels[index];
          if (label.Name != null) {
            wr.Write("label {0}:", label.Name);
            if (labelledStatement.GetType() != typeof(LabeledStatement) || index != labelledStatement.Labels.Count - 1) {
              wr.WriteLine();
              Indent(indent);
            }
          }
        }
      }

      if (stmt is ICanPrint canPrint) {
        canPrint.Render(wr, this, indent);
        return;
      }

      switch (stmt) {
        case PredicateStmt:
          PrintPredicateStmt(stmt, includeSemicolon);
          break;
        case PrintStmt printStmt: {
            PrintStmt s = printStmt;
            wr.Write("print");
            PrintAttributeArgs(s.Args, true);
            wr.Write(";");
            break;
          }
        case HideRevealStmt revealStmt:
          PrintHideReveal(revealStmt);
          break;
        case BreakOrContinueStmt continueStmt: {
            var s = continueStmt;
            if (s.TargetLabel != null) {
              wr.Write($"{s.Kind} {s.TargetLabel.Value};");
            } else {
              for (int i = 0; i < s.BreakAndContinueCount - 1; i++) {
                wr.Write("break ");
              }
              wr.Write($"{s.Kind};");
            }

            break;
          }
        case ProduceStmt produceStmt: {
            var s = produceStmt;
            wr.Write(s is YieldStmt ? "yield" : "return");
            if (s.Rhss != null) {
              var sep = " ";
              foreach (var rhs in s.Rhss) {
                wr.Write(sep);
                PrintRhs(rhs);
                sep = ", ";
              }
            }
            wr.Write(";");
            break;
          }
        case SingleAssignStmt assignStmt: {
            SingleAssignStmt s = assignStmt;
            PrintExpression(s.Lhs, true);
            wr.Write(" := ");
            PrintRhs(s.Rhs);
            wr.Write(";");
            break;
          }
        case DividedBlockStmt blockStmt: {
            var sbs = blockStmt;
            wr.WriteLine("{");
            int ind = indent + IndentAmount;
            foreach (Statement s in sbs.BodyInit) {
              Indent(ind);
              PrintStatement(s, ind);
              wr.WriteLine();
            }
            if (sbs.BodyProper.Count != 0 || sbs.SeparatorTok != null) {
              Indent(indent + IndentAmount);
              wr.WriteLine("new;");
              foreach (Statement s in sbs.BodyProper) {
                Indent(ind);
                PrintStatement(s, ind);
                wr.WriteLine();
              }
            }
            Indent(indent);
            wr.Write("}");
            break;
          }
        case BlockStmt blockStmt:
          PrintBlockStmt(blockStmt, indent);
          break;
        case IfStmt ifStmt: {
            IfStmt s = ifStmt;
            PrintIfStatement(indent, s, false);
            break;
          }
        case AlternativeStmt alternativeStmt: {
            var s = alternativeStmt;
            PrintAttributes(s.Attributes, indent, () => {
              wr.Write("if");
            });
            if (s.UsesOptionalBraces) {
              wr.Write(" {");
            }
            PrintAlternatives(indent + (s.UsesOptionalBraces ? IndentAmount : 0), s.Alternatives);
            if (s.UsesOptionalBraces) {
              wr.WriteLine();
              Indent(indent);
              wr.Write("}");
            }

            break;
          }
        case WhileStmt whileStmt: {
            var s = whileStmt;
            PrintWhileStatement(indent, s, false, false);
            break;
          }
        case AlternativeLoopStmt loopStmt: {
            var s = loopStmt;
            PrintAttributes(s.Attributes, indent, () => {
              wr.Write("while");
            });
            PrintSpec("invariant", s.Invariants, indent + IndentAmount);
            PrintDecreasesSpec(s.Decreases, indent + IndentAmount);
            PrintFrameSpecLine("modifies", s.Mod, indent + IndentAmount);
            bool hasSpecs = s.Invariants.Count != 0 ||
                            (s.Decreases.Expressions != null && s.Decreases.Expressions.Count != 0) ||
                            s.Mod.Expressions != null;
            if (s.UsesOptionalBraces) {
              if (hasSpecs) {
                wr.WriteLine();
                Indent(indent);
              } else {
                wr.Write(" ");
              }
              wr.Write("{");
            }
            Contract.Assert(s.Alternatives.Count != 0);
            PrintAlternatives(indent + (s.UsesOptionalBraces ? IndentAmount : 0), s.Alternatives);
            if (s.UsesOptionalBraces) {
              wr.WriteLine();
              Indent(indent);
              wr.Write("}");
            }

            break;
          }
        case ForLoopStmt loopStmt: {
            var s = loopStmt;
            PrintForLoopStatement(indent, s);
            break;
          }
        case ForallStmt forallStmt: {
            var s = forallStmt;
            if (options.DafnyPrintResolvedFile != null && s.EffectiveEnsuresClauses != null) {
              foreach (var expr in s.EffectiveEnsuresClauses) {
                PrintExpression(expr, false, new string(' ', indent + IndentAmount) + "ensures ");
              }
              if (s.Body != null) {
                wr.WriteLine();
                Indent(indent);
              }
            } else {
              wr.Write("forall");
              if (s.BoundVars.Count != 0) {
                wr.Write(" ");
                PrintQuantifierDomain(s.BoundVars, s.Attributes, s.Range);
              }
              PrintSpec("ensures", s.Ens, indent + IndentAmount);
              if (s.Body != null) {
                if (s.Ens.Count == 0) {
                  wr.Write(" ");
                } else {
                  wr.WriteLine();
                  Indent(indent);
                }
              }
            }
            if (s.Body != null) {
              PrintStatement(s.Body, indent);
            }

            break;
          }
        case ModifyStmt modifyStmt: {
            var s = modifyStmt;
            PrintModifyStmt(indent, s, false);
            break;
          }
        case CalcStmt calcStmt: {
            CalcStmt s = calcStmt;
            if (printMode == PrintModes.NoGhostOrIncludes) { return; }   // Calcs don't get a "ghost" attribute, but they are.
            PrintAttributes(calcStmt.Attributes, indent, () => {
              wr.Write("calc");
            });
            wr.Write(" ");
            if (s.UserSuppliedOp != null) {
              PrintCalcOp(s.UserSuppliedOp);
              wr.Write(" ");
            } else if (options.DafnyPrintResolvedFile != null && s.Op != null) {
              PrintCalcOp(s.Op);
              wr.Write(" ");
            }
            wr.WriteLine("{");
            int lineInd = indent + IndentAmount;
            int lineCount = s.Lines.Count == 0 ? 0 : s.Lines.Count - 1;  // if nonempty, .Lines always contains a duplicated last line
                                                                         // The number of op/hints is commonly one less than the number of lines, but
                                                                         // it can also equal the number of lines for empty calc's and for calc's with
                                                                         // a dangling hint.
            int hintCount = s.Lines.Count != 0 && s.Hints.Last().Body.Count == 0 ? lineCount - 1 : lineCount;
            for (var i = 0; i < lineCount; i++) {
              var e = s.Lines[i];
              var op = s.StepOps[i];
              var h = s.Hints[i];
              // print the line
              Indent(lineInd);
              PrintExpression(e, true, lineInd);
              wr.WriteLine(";");
              if (i == hintCount) {
                break;
              }
              // print the operator, if any
              if (op != null || (options.DafnyPrintResolvedFile != null && s.Op != null)) {
                Indent(indent); // this lines up with the "calc"
                PrintCalcOp(op ?? s.Op);
                wr.WriteLine();
              }
              // print the hints
              foreach (var st in h.Body) {
                Indent(lineInd);
                PrintStatement(st, lineInd);
                wr.WriteLine();
              }
            }
            Indent(indent);
            wr.Write("}");
            break;
          }
        case NestedMatchStmt matchStmt: {
            // Print ResolvedStatement, if present, as comment
            var s = matchStmt;

            if (s.Flattened != null && options.DafnyPrintResolvedFile != null) {
              wr.WriteLine();
              if (!printingDesugared) {
                Indent(indent); wr.WriteLine("/*---------- flattened ----------");
              }

              var savedDesugarMode = printingDesugared;
              printingDesugared = true;
              Indent(indent); PrintStatement(s.Flattened, indent);
              wr.WriteLine();
              printingDesugared = savedDesugarMode;

              if (!printingDesugared) {
                Indent(indent); wr.WriteLine("---------- end flattened ----------*/");
              }
              Indent(indent);
            }

            if (!printingDesugared) {
              PrintAttributes(s.Attributes, indent, () => {
                wr.Write("match");
              });
              wr.Write(" ");
              PrintExpression(s.Source, false);
              if (s.UsesOptionalBraces) {
                wr.Write(" {");
              }
              int caseInd = indent + (s.UsesOptionalBraces ? IndentAmount : 0);
              foreach (NestedMatchCaseStmt mc in s.Cases) {
                wr.WriteLine();
                Indent(caseInd);
                PrintAttributes(mc.Attributes, indent, () => {
                  wr.Write("case");
                });
                wr.Write(" ");
                PrintExtendedPattern(mc.Pat);
                wr.Write(" =>");
                foreach (Statement bs in mc.Body) {
                  wr.WriteLine();
                  Indent(caseInd + IndentAmount);
                  PrintStatement(bs, caseInd + IndentAmount);
                }
              }
              if (s.UsesOptionalBraces) {
                wr.WriteLine();
                Indent(indent);
                wr.Write("}");
              }
            }

            break;
          }
        case MatchStmt matchStmt: {
            var s = matchStmt;
            PrintAttributes(s.Attributes, indent, () => {
              wr.Write("match");
            });
            wr.Write(" ");
            PrintExpression(s.Source, false);
            if (s.UsesOptionalBraces) {
              wr.Write(" {");
            }

            int caseInd = indent + (s.UsesOptionalBraces ? IndentAmount : 0);
            foreach (MatchCaseStmt mc in s.Cases) {
              wr.WriteLine();
              Indent(caseInd);
              PrintAttributes(mc.Attributes, indent, () => {
                wr.Write("case");
              });
              wr.Write(" ");
              if (!mc.Ctor.Name.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix)) {
                wr.Write(mc.Ctor.Name);
              }

              PrintMatchCaseArgument(mc);
              wr.Write(" =>");
              foreach (Statement bs in mc.Body) {
                wr.WriteLine();
                Indent(caseInd + IndentAmount);
                PrintStatement(bs, caseInd + IndentAmount);
              }
            }

            if (s.UsesOptionalBraces) {
              wr.WriteLine();
              Indent(indent);
              wr.Write("}");
            }

            break;
          }
        case ConcreteAssignStatement concreteAssignStatement:
          PrintConcreteUpdateStatement(concreteAssignStatement, indent, includeSemicolon);
          break;
        case CallStmt callStmt: {
            // Most calls are printed from their concrete syntax given in the input. However, recursive calls to
            // prefix lemmas end up as CallStmt's by the end of resolution and they may need to be printed here.
            var s = callStmt;
            PrintExpression(s.MethodSelect, false);
            PrintActualArguments(s.Bindings, s.Method.Name, null);
            break;
          }
        case VarDeclStmt declStmt: {
            var s = declStmt;
            if (s.Locals.Exists(v => v.IsGhost) && printMode == PrintModes.NoGhostOrIncludes) { return; }
            if (s.Locals.TrueForAll((v => v.IsGhost))) {
              // Emit the "ghost" modifier if all of the variables are ghost. If some are ghost, but not others,
              // then some of these ghosts are auto-converted to ghost, so we should not emit the "ghost" keyword.
              wr.Write("ghost ");
            }
            wr.Write("var");
            string sep = "";
            foreach (var local in s.Locals) {
              wr.Write(sep);
              if (local.Attributes != null) {
                PrintAttributes(local.Attributes, AtAttributesOnSameLineIndent, () => { });
              }
              wr.Write(" {0}", local.DisplayName);
              PrintType(": ", local.SafeSyntacticType);
              sep = ",";
            }
            if (s.Assign != null) {
              wr.Write(" ");
              PrintUpdateRHS(s.Assign, indent);
            }

            if (includeSemicolon) {
              wr.Write(";");
            }

            break;
          }
        case VarDeclPattern pattern: {
            var s = pattern;
            if (s.Origin is AutoGeneratedOrigin) {
              wr.Write("/* ");
            }
            if (s.HasGhostModifier) {
              wr.Write("ghost ");
            }
            wr.Write("var ");
            PrintCasePattern(s.LHS);
            wr.Write(" := ");
            PrintExpression(s.RHS, true);
            wr.Write(";");
            if (s.Origin is AutoGeneratedOrigin) {
              wr.Write(" */");
            }

            break;
          }
        case SkeletonStatement statement: {
            var s = statement;
            if (s.S == null) {
              wr.Write("...;");
            } else if (s.S is AssertStmt) {
              Contract.Assert(s.ConditionOmitted);
              wr.Write("assert ...;");
            } else if (s.S is ExpectStmt) {
              Contract.Assert(s.ConditionOmitted);
              wr.Write("expect ...;");
            } else if (s.S is AssumeStmt) {
              Contract.Assert(s.ConditionOmitted);
              wr.Write("assume ...;");
            } else if (s.S is IfStmt) {
              PrintIfStatement(indent, (IfStmt)s.S, s.ConditionOmitted);
            } else if (s.S is WhileStmt) {
              PrintWhileStatement(indent, (WhileStmt)s.S, s.ConditionOmitted, s.BodyOmitted);
            } else if (s.S is ModifyStmt) {
              PrintModifyStmt(indent, (ModifyStmt)s.S, true);
            } else {
              Contract.Assert(false);
              throw new Cce.UnreachableException(); // unexpected skeleton statement
            }

            break;
          }
        case TryRecoverStatement haltRecoveryStatement: {
            // These have no actual syntax for Dafny user code, so emit something
            // clearly not parsable.
            int ind = indent + IndentAmount;

            Indent(indent);
            wr.WriteLine("[[ try { ]]");
            PrintStatement(haltRecoveryStatement.TryBody, ind);
            wr.WriteLine();

            Indent(indent);
            wr.WriteLine($"[[ }} recover ({haltRecoveryStatement.HaltMessageVar.Name}) {{ ]]");
            PrintStatement(haltRecoveryStatement.RecoverBody, ind);
            wr.Write("[[ } ]]");
            break;
          }
        case LabeledStatement labeledStatement:
          // content already handled earlier
          break;
        default:
          Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected statement
      }
    }

    public void PrintConcreteUpdateStatement(ConcreteAssignStatement stmt, int indent, bool includeSemicolon = true) {
      string sep = "";
      foreach (var lhs in stmt.Lhss) {
        wr.Write(sep);
        PrintExpression(lhs, true);
        sep = ", ";
      }
      if (stmt.Lhss.Count > 0) {
        wr.Write(" ");
      }
      PrintUpdateRHS(stmt, indent);
      if (includeSemicolon) {
        wr.Write(";");
      }
    }

    public void PrintBlockStmt(BlockStmt stmt, int indent) {
      wr.WriteLine("{");
      int ind = indent + IndentAmount;
      foreach (Statement s in stmt.Body) {
        Indent(ind);
        PrintStatement(s, ind);
        wr.WriteLine();
      }
      Indent(indent);
      wr.Write("}");
    }

    public void PrintPredicateStmt(Statement stmt, bool includeSemicolon = true) {
      if (printMode == PrintModes.NoGhostOrIncludes) {
        return;
      }
      Expression expr = ((PredicateStmt)stmt).Expr;
      var assertStmt = stmt as AssertStmt;
      var expectStmt = stmt as ExpectStmt;
      var keyword = assertStmt != null ? "assert" :
        expectStmt != null ? "expect" :
        "assume";
      PrintAttributes(stmt.Attributes, AtAttributesOnSameLineIndent, () => {
        wr.Write(keyword);
      });
      wr.Write(" ");
      if (assertStmt != null && assertStmt.Label != null) {
        wr.Write("{0}: ", assertStmt.Label.Name);
      }
      PrintExpression(expr, true);
      if (expectStmt is { Message: not null }) {
        wr.Write(", ");
        PrintExpression(expectStmt.Message, true);
      }

      if (includeSemicolon) {
        wr.Write(";");
      }
    }

    private void PrintHideReveal(HideRevealStmt revealStmt) {
      wr.Write(revealStmt.Mode == Bpl.HideRevealCmd.Modes.Hide ? "hide " : "reveal ");
      if (revealStmt.Wildcard) {
        wr.Write("*");
      } else {
        var sep = "";
        foreach (var e in revealStmt.Exprs) {
          wr.Write(sep);
          sep = ", ";
          if (HideRevealStmt.SingleName(e) != null) {
            // this will do the printing correctly for labels (or label-lookalikes) like 00_023 (which by PrintExpression below would be printed as 23)
            wr.Write(HideRevealStmt.SingleName(e));
          } else {
            PrintExpression(e, true);
          }
        }
      }
      wr.Write(";");
    }

    private void PrintModifyStmt(int indent, ModifyStmt s, bool omitFrame) {
      Contract.Requires(0 <= indent);
      Contract.Requires(s != null);
      Contract.Requires(!omitFrame || s.Mod.Expressions.Count == 0);

      PrintAttributes(s.Mod.Attributes, indent, () => {
        wr.Write("modify");
      });
      wr.Write(" ");
      if (omitFrame) {
        wr.Write("...");
      } else {
        PrintFrameExpressionList(s.Mod.Expressions);
      }
      if (s.Body != null) {
        // There's a possible syntactic ambiguity, namely if the frame is empty (more precisely,
        // if s.Mod.Expressions.Count is 0).  Since the statement was parsed at some point, this
        // situation can occur only if the modify statement inherited its frame by refinement
        // and we're printing the post-resolve AST.  In this special case, print an explicit
        // empty set as the frame.
        if (s.Mod.Expressions.Count == 0) {
          wr.Write(" {}");
        }
        wr.Write(" ");
        PrintStatement(s.Body, indent);
      } else {
        wr.Write(";");
      }
    }

    /// <summary>
    /// Does not print LHS, nor the space one might want between LHS and RHS,
    /// because if there's no LHS, we don't want to start with a space
    /// </summary>
    void PrintUpdateRHS(ConcreteAssignStatement s, int indent) {
      Contract.Requires(s != null);
      if (s is AssignStatement) {
        var update = (AssignStatement)s;
        if (update.Lhss.Count != 0) {
          wr.Write(":= ");
        }
        var sep = "";
        foreach (var rhs in update.Rhss) {
          wr.Write(sep);
          PrintRhs(rhs);
          sep = ", ";
        }
      } else if (s is AssignSuchThatStmt) {
        var update = (AssignSuchThatStmt)s;
        wr.Write(":| ");
        if (update.AssumeToken != null) {
          PrintAttributes(update.AssumeToken.Attrs, indent, () => {
            wr.Write("assume");
          });
          wr.Write(" ");
        }
        PrintExpression(update.Expr, true);
      } else if (s is AssignOrReturnStmt) {
        var stmt = (AssignOrReturnStmt)s;
        wr.Write(":-");
        if (stmt.KeywordToken != null) {
          wr.Write(" ");
          PrintAttributes(stmt.KeywordToken.Attrs, indent, () => {
            wr.Write(stmt.KeywordToken.Token.val);
          });
        }
        wr.Write(" ");
        PrintRhs(stmt.Rhs);
        foreach (var rhs in stmt.Rhss) {
          wr.Write(", ");
          PrintRhs(rhs);
        }
        if (options.DafnyPrintResolvedFile != null && stmt.ResolvedStatements.Count > 0) {
          wr.WriteLine();
          Indent(indent); wr.WriteLine("/*---------- desugared ----------");
          foreach (Statement r in stmt.ResolvedStatements) {
            Indent(indent);
            PrintStatement(r, indent);
            wr.WriteLine();
          }
          Indent(indent); wr.Write("---------- end desugared ----------*/");
        }

      } else {
        Contract.Assert(false);  // otherwise, unknown type
      }
    }

    void PrintIfStatement(int indent, IfStmt s, bool omitGuard) {
      PrintAttributes(s.Attributes, indent, () => {
        wr.Write("if");
      });
      wr.Write(" ");
      if (omitGuard) {
        wr.Write("... ");
      } else {
        PrintGuard(s.IsBindingGuard, s.Guard);
        wr.Write(" ");
      }
      PrintStatement(s.Thn, indent);
      if (s.Els != null) {
        wr.Write(" ");
        if (!(s.Els is IfStmt) && s.Els.Attributes != null) {
          PrintAttributes(s.Els.Attributes, indent, () => {
            wr.Write("else");
          });
        } else {
          wr.Write("else");
        }
        wr.Write(" ");
        PrintStatement(s.Els, indent);
      }
    }

    void PrintWhileStatement(int indent, WhileStmt s, bool omitGuard, bool omitBody) {
      Contract.Requires(0 <= indent);
      PrintAttributes(s.Attributes, indent, () => {
        wr.Write("while");
      });
      wr.Write(" ");
      if (omitGuard) {
        wr.Write("...");
      } else {
        PrintGuard(false, s.Guard);
      }

      PrintSpec("invariant", s.Invariants, indent + IndentAmount);
      PrintDecreasesSpec(s.Decreases, indent + IndentAmount);
      PrintFrameSpecLine("modifies", s.Mod, indent + IndentAmount);
      if (omitBody) {
        wr.WriteLine();
        Indent(indent + IndentAmount);
        wr.Write("...;");
      } else if (s.Body != null) {
        if (s.Invariants.Count == 0 && s.Decreases.Expressions.Count == 0 && (s.Mod.Expressions == null || s.Mod.Expressions.Count == 0)) {
          wr.Write(" ");
        } else {
          wr.WriteLine();
          Indent(indent);
        }
        PrintStatement(s.Body, indent);
      }
    }

    void PrintAlternatives(int indent, List<GuardedAlternative> alternatives) {
      var startWithLine = true;
      foreach (var alternative in alternatives) {
        if (startWithLine) {
          wr.WriteLine();
        } else {
          startWithLine = true;
        }
        Indent(indent);
        PrintAttributes(alternative.Attributes, indent, () => {
          wr.Write("case");
        });
        wr.Write(" ");
        if (alternative.IsBindingGuard) {
          var exists = (ExistsExpr)alternative.Guard;
          PrintBindingGuard(exists);
        } else {
          PrintExpression(alternative.Guard, false);
        }
        wr.Write(" =>");
        foreach (Statement s in alternative.Body) {
          wr.WriteLine();
          Indent(indent + IndentAmount);
          PrintStatement(s, indent + IndentAmount);
        }
      }
    }

    void PrintForLoopStatement(int indent, ForLoopStmt s) {
      Contract.Requires(0 <= indent);
      Contract.Requires(s != null);
      PrintAttributes(s.Attributes, indent, () => {
        wr.Write("for");
      });
      wr.Write($" {s.LoopIndex.Name}");
      PrintType(": ", s.LoopIndex.Type);
      wr.Write(" := ");
      PrintExpression(s.Start, false);
      wr.Write(s.GoingUp ? " to " : " downto ");
      if (s.End == null) {
        wr.Write("*");
      } else {
        PrintExpression(s.End, false);
      }

      PrintSpec("invariant", s.Invariants, indent + IndentAmount);
      PrintDecreasesSpec(s.Decreases, indent + IndentAmount);
      if (s.Mod.Expressions != null) {
        PrintFrameSpecLine("modifies", s.Mod, indent + IndentAmount);
      }
      if (s.Body != null) {
        if (s.Invariants.Count == 0 && s.Decreases.Expressions.Count == 0 && (s.Mod.Expressions == null || s.Mod.Expressions.Count == 0)) {
          wr.Write(" ");
        } else {
          wr.WriteLine();
          Indent(indent);
        }
        PrintStatement(s.Body, indent);
      }
    }

    void PrintRhs(AssignmentRhs rhs) {
      Contract.Requires(rhs != null);
      if (rhs is ExprRhs) {
        PrintExpression(((ExprRhs)rhs).Expr, true);
      } else if (rhs is HavocRhs) {
        wr.Write("*");
      } else if (rhs is TypeRhs) {
        TypeRhs t = (TypeRhs)rhs;
        wr.Write("new ");
        if (t is AllocateArray allocateArray) {
          if (ShowType(allocateArray.ElementType)) {
            PrintType(allocateArray.ElementType);
          }
          if (options.DafnyPrintResolvedFile == null &&
              allocateArray.InitDisplay != null && allocateArray.ArrayDimensions.Count == 1 &&
            AutoGeneratedOrigin.Is(allocateArray.ArrayDimensions[0].Origin)) {
            // elide the size
            wr.Write("[]");
          } else {
            string s = "[";
            foreach (Expression dim in allocateArray.ArrayDimensions) {
              Contract.Assume(dim != null);
              wr.Write(s);
              PrintExpression(dim, false);
              s = ", ";
            }
            wr.Write("]");
          }
          if (allocateArray.ElementInit != null) {
            wr.Write(" (");
            PrintExpression(allocateArray.ElementInit, false);
            wr.Write(")");
          } else if (allocateArray.InitDisplay != null) {
            wr.Write(" [");
            PrintExpressionList(allocateArray.InitDisplay, false);
            wr.Write("]");
          }
        } else if (t is AllocateClass allocateClass) {
          if (allocateClass.Bindings == null) {
            PrintType(allocateClass.Path);
          } else {
            PrintType(allocateClass.Path);
            wr.Write("(");
            PrintBindings(allocateClass.Bindings, false);
            wr.Write(")");

          }
        }
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected RHS
      }

      if (rhs.HasAttributes()) {
        PrintAttributes(rhs.Attributes, AtAttributesOnSameLineIndent, () => { });
      }
    }

    void PrintGuard(bool isBindingGuard, Expression guard) {
      Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
      if (guard == null) {
        wr.Write("*");
      } else if (isBindingGuard) {
        var exists = (ExistsExpr)guard;
        PrintBindingGuard(exists);
      } else {
        PrintExpression(guard, false);
      }
    }

    void PrintBindingGuard(ExistsExpr guard) {
      Contract.Requires(guard != null);
      Contract.Requires(guard.Range == null);
      PrintQuantifierDomain(guard.BoundVars, guard.Attributes, null);
      wr.Write(" :| ");
      PrintExpression(guard.Term, false);
    }

    void PrintCalcOp(CalcStmt.CalcOp op) {
      Contract.Requires(op != null);
      wr.Write(op.ToString());
      if (op is CalcStmt.TernaryCalcOp) {
        wr.Write("[");
        PrintExpression(((CalcStmt.TernaryCalcOp)op).Index, false);
        wr.Write("]");
      }
    }
  }
}
