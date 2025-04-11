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

  public partial class Printer {
    /// <summary>
    /// PrintExtendedExpr prints an expression, but formats top-level if-then-else and match expressions across several lines.
    /// Its intended use is thus to print the body of a function.
    /// </summary>
    public void PrintExtendedExpr(Expression expr, int indent, bool isRightmost, bool endWithCloseParen) {
      Contract.Requires(expr != null);
      if (expr is ITEExpr) {
        Indent(indent);
        while (true) {
          var ite = (ITEExpr)expr;
          wr.Write("if ");
          if (options.DafnyPrintResolvedFile == null) {
            PrintGuard(ite.IsBindingGuard, ite.Test);
          } else {
            PrintExpression(ite.Test, false);
          }
          wr.WriteLine(" then");
          var thenBranch = options.DafnyPrintResolvedFile == null && ite.IsBindingGuard ? ((LetExpr)ite.Thn).Body : ite.Thn;
          PrintExtendedExpr(thenBranch, indent + IndentAmount, true, false);
          expr = ite.Els;
          if (expr is ITEExpr) {
            Indent(indent); wr.Write("else ");
          } else {
            Indent(indent); wr.WriteLine("else");
            Indent(indent + IndentAmount);
            PrintExpression(expr, isRightmost, false);
            wr.WriteLine(endWithCloseParen ? ")" : "");
            return;
          }
        }

      } else if (expr is NestedMatchExpr) {
        var e = (NestedMatchExpr)expr;
        if (e.Flattened != null && options.DafnyPrintResolvedFile != null) {
          wr.WriteLine();
          if (!printingDesugared) {
            Indent(indent); wr.WriteLine("/*---------- flattened ----------");
          }

          var savedDesugarMode = printingDesugared;
          printingDesugared = true;
          PrintExtendedExpr(e.Flattened, indent, isRightmost, endWithCloseParen);
          printingDesugared = savedDesugarMode;

          if (!printingDesugared) {
            Indent(indent); wr.WriteLine("---------- end flattened ----------*/");
          }
        }
        if (!printingDesugared) {
          Indent(indent);
          var parensNeeded = !isRightmost && !e.UsesOptionalBraces;
          if (parensNeeded) { wr.Write("("); }
          wr.Write("match ");
          PrintExpression(e.Source, isRightmost && e.Cases.Count == 0, false);
          if (e.UsesOptionalBraces) {
            wr.WriteLine(" {");
          } else if (parensNeeded && e.Cases.Count == 0) {
            wr.WriteLine(")");
          } else {
            wr.WriteLine();
          }
          int i = 0;
          int ind = indent + (e.UsesOptionalBraces ? IndentAmount : 0);
          foreach (var mc in e.Cases) {
            bool isLastCase = i == e.Cases.Count - 1;
            Indent(ind);
            PrintAttributes(mc.Attributes, indent, () => {
              wr.Write("case");
            });
            wr.Write(" ");
            PrintExtendedPattern(mc.Pat);
            wr.WriteLine(" =>");
            PrintExtendedExpr(mc.Body, ind + IndentAmount, isLastCase, isLastCase && (parensNeeded || endWithCloseParen));
            i++;
          }
          if (e.UsesOptionalBraces) {
            Indent(indent);
            wr.WriteLine("}");
          }
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        if (options.DafnyPrintResolvedFile == null && e.OrigUnresolved != null) {
          PrintExtendedExpr(e.OrigUnresolved, indent, isRightmost, endWithCloseParen);
        } else {
          Indent(indent);
          var parensNeeded = !isRightmost && !e.UsesOptionalBraces;
          if (parensNeeded) { wr.Write("("); }
          wr.Write("match ");
          PrintExpression(e.Source, isRightmost && e.Cases.Count == 0, false);
          if (e.UsesOptionalBraces) { wr.WriteLine(" {"); } else if (parensNeeded && e.Cases.Count == 0) { wr.WriteLine(")"); } else { wr.WriteLine(); }
          int i = 0;
          int ind = indent + (e.UsesOptionalBraces ? IndentAmount : 0);
          foreach (var mc in e.Cases) {
            bool isLastCase = i == e.Cases.Count - 1;
            Indent(ind);
            PrintAttributes(mc.Attributes, ind, () => {
              wr.Write("case");
            });
            wr.Write(" ");
            wr.Write(mc.Ctor.Name);
            PrintMatchCaseArgument(mc);
            wr.WriteLine(" =>");
            PrintExtendedExpr(mc.Body, ind + IndentAmount, isLastCase, isLastCase && (parensNeeded || endWithCloseParen));
            i++;
          }
          if (e.UsesOptionalBraces) {
            Indent(indent);
            wr.WriteLine("}");
          }
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        Indent(indent);
        if (e.Origin is AutoGeneratedOrigin) {
          wr.Write("/* ");
        }
        if (e.LHSs.Exists(lhs => lhs != null && lhs.Var != null && lhs.Var.IsGhost)) { wr.Write("ghost "); }
        wr.Write("var ");
        string sep = "";
        foreach (var lhs in e.LHSs) {
          wr.Write(sep);
          PrintCasePattern(lhs);
          sep = ", ";
        }
        if (e.Exact) {
          wr.Write(" := ");
        } else {
          PrintAttributes(e.Attributes, AtAttributesOnSameLineIndent, () => { });
          wr.Write(" :| ");
        }
        PrintExpressionList(e.RHSs, true);
        wr.Write(";");
        if (e.Origin is AutoGeneratedOrigin) {
          wr.Write(" */");
        }
        wr.WriteLine();
        PrintExtendedExpr(e.Body, indent, isRightmost, endWithCloseParen);
      } else if (expr is StmtExpr && isRightmost) {
        var e = (StmtExpr)expr;
        Indent(indent);
        PrintStatement(e.S, indent);
        wr.WriteLine();
        PrintExtendedExpr(e.E, indent, isRightmost, endWithCloseParen);

      } else if (expr is ParensExpression) {
        PrintExtendedExpr(((ParensExpression)expr).E, indent, isRightmost, endWithCloseParen);
      } else {
        Indent(indent);
        PrintExpression(expr, false, indent);
        wr.WriteLine(endWithCloseParen ? ")" : "");
      }
    }

    public void PrintMatchCaseArgument(MatchCase mc) {
      Contract.Assert(mc.Arguments != null);
      if (mc.Arguments.Count != 0) {
        string sep = "(";
        foreach (BoundVar bv in mc.Arguments) {
          wr.Write("{0}{1}", sep, bv.DisplayName);
          string typeName = bv.Type.TypeName(options, null, true);
          if (bv.Type is NonProxyType && !typeName.StartsWith("_")) {
            wr.Write(": {0}", typeName);
          }
          sep = ", ";
        }
        wr.Write(")");
      }
    }

    public void PrintExpression(Expression expr, bool isFollowedBySemicolon) {
      Contract.Requires(expr != null);
      PrintExpr(expr, 0, false, true, isFollowedBySemicolon, -1);
    }

    public void PrintExpression(Expression expr, bool isRightmost, bool isFollowedBySemicolon) {
      Contract.Requires(expr != null);
      PrintExpr(expr, 0, false, isRightmost, isFollowedBySemicolon, -1);
    }

    /// <summary>
    /// An indent of -1 means print the entire expression on one line.
    /// </summary>
    public void PrintExpression(Expression expr, bool isFollowedBySemicolon, int indent) {
      Contract.Requires(expr != null);
      PrintExpr(expr, 0, false, true, isFollowedBySemicolon, indent);
    }

    public void PrintExpression(Expression expr, bool isFollowedBySemicolon, string keyword) {
      Contract.Requires(expr != null);
      PrintExpr(expr, 0, false, true, isFollowedBySemicolon, -1, keyword);
    }

    private const int BindingGroup = 0xF0;

    private const int BindingStrengthDecreasesTo = 0x10; // decreases to, nonincreases to

    private const int BindingStrengthEquiv = 0x20; // <==>

    private const int BindingStrengthImplies = 0x30; // ==>
    private const int BindingStrengthExplies = 0x31; // <==

    private const int BindingStrengthAnd = 0x40; // &&
    private const int BindingStrengthOr = 0x41; // ||

    private const int BindingStrengthCompare = 0x50; // == != ==#[...] !=#[...] < <= >= >

    private const int BindingStrengthAdd = 0x60; // + -

    private const int BindingStrengthShift = 0x70; // << >>

    private const int BindingStrengthMul = 0x80; // * / %

    private const int BindingStrengthBitwiseAnd = 0x90; // &
    private const int BindingStrengthBitwiseOr = 0x91; // |
    private const int BindingStrengthBitwiseXor = 0x92; // ^

    private const int BindingStrengthUnarySuffix = 0xA0; // as is

    private const int BindingStrengthUnaryPrefix = 0xB0; // ! -

    private const int BindingStrengthSuffix = 0xC0; // X.name X.(name := ...) X(...) X[...]

    private bool ParensNeeded(int opBindingStrength, int contextBindingStrength, bool fragileContext) {
      int opGroupStrength = opBindingStrength & BindingGroup;
      int contextGroupStrength = contextBindingStrength & BindingGroup;
      var parensNeeded = opGroupStrength < contextGroupStrength ||
                         (opGroupStrength == contextGroupStrength && (opBindingStrength != contextBindingStrength || fragileContext));
      return parensNeeded;
    }


    bool ParensMayMatter(Expression expr) {
      Contract.Requires(expr != null);
      int parenPairs = 0;
      for (; expr is ParensExpression; parenPairs++) {
        expr = ((ParensExpression)expr).E;
      }
      // If the program were resolved, we could be more precise than the following (in particular, looking
      // to see if expr denotes a MemberSelectExpr of a member that is a Function.
      return parenPairs != 0 && (expr is NameSegment || expr is ExprDotName);
    }

    void PrintCasePattern<VT>(CasePattern<VT> pat)
      where VT : class, IVariable {
      Contract.Requires(pat != null);
      var v = pat.Var;
      if (v != null) {
        wr.Write(v.DisplayName);
        if (v.OptionalType is NonProxyType || options.DafnyPrintResolvedFile != null) {
          PrintType(": ", v.OptionalType);
        }
      } else {
        if (pat.Id.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix)) {
          Contract.Assert(pat.Arguments != null);
        } else {
          wr.Write(pat.Id);
        }
        if (pat.Arguments != null) {
          wr.Write("(");
          var sep = "";
          foreach (var arg in pat.Arguments) {
            wr.Write(sep);
            PrintCasePattern(arg);
            sep = ", ";
          }
          wr.Write(")");
        }
      }
    }

    // Main difference with .ToString is that tuple constructors are not printed.
    void PrintExtendedPattern(ExtendedPattern pat) {
      Contract.Requires(pat != null);
      switch (pat) {
        case IdPattern idPat:
          if (idPat.Id.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix)) {
          } else if (idPat.IsWildcardPattern) {
            // In case of the universal match pattern, print '_' instead of
            // its node identifier, otherwise the printed program becomes
            // syntactically incorrect.
            wr.Write("_");
            if (!idPat.IsWildcardExact) {
              wr.Write($" /* {idPat.Id} */");
            }
          } else {
            wr.Write(idPat.Id);
          }
          if (idPat.Arguments != null) {
            wr.Write("(");
            var sep = "";
            foreach (var arg in idPat.Arguments) {
              wr.Write(sep);
              PrintExtendedPattern(arg);
              sep = ", ";
            }
            wr.Write(")");
          } else if (options.DafnyPrintResolvedFile != null && idPat.ResolvedLit != null) {
            Contract.Assert(idPat.BoundVar == null && idPat.Ctor == null);
            wr.Write(" /*== ");
            PrintExpression(idPat.ResolvedLit, false);
            wr.Write("*/");
          } else if (ShowType(idPat.Type)) {
            wr.Write(": ");
            PrintType(idPat.Type);
          }
          break;
        case DisjunctivePattern dPat:
          var patSep = "";
          foreach (var arg in dPat.Alternatives) {
            wr.Write(patSep);
            PrintExtendedPattern(arg);
            patSep = " | ";
          }
          break;
        case LitPattern litPat:
          wr.Write(litPat.ToString());
          break;
      }
    }

    private void PrintQuantifierDomain(List<BoundVar> boundVars, Attributes attrs, Expression range) {
      Contract.Requires(boundVars != null);
      string sep = "";
      foreach (BoundVar bv in boundVars) {
        wr.Write("{0}", sep);
        if (printFlags.UseOriginalDafnyNames) {
          wr.Write(bv.DafnyName);
        } else {
          wr.Write(bv.DisplayName);
        }

        PrintType(": ", bv.Type);
        sep = ", ";
      }
      PrintAttributes(attrs, AtAttributesOnSameLineIndent, () => { });
      if (range != null) {
        wr.Write(" | ");
        PrintExpression(range, false);
      }
    }

    void PrintActualArguments(ActualBindings bindings, string/*?*/ name, Bpl.IToken/*?*/ atLabel) {
      Contract.Requires(bindings != null);
      var i = 0;
      if (name != null && name.EndsWith("#")) {
        Contract.Assert(atLabel == null);
        Contract.Assert(1 <= bindings.ArgumentBindings.Count);
        Contract.Assert(bindings.ArgumentBindings[0].FormalParameterName == null);
        wr.Write("[");
        PrintExpression(bindings.ArgumentBindings[0].Actual, false);
        wr.Write("]");
        i++;
      } else if (atLabel != null) {
        wr.Write($"@{atLabel.val}");
      }
      wr.Write("(");
      string sep = "";
      if (options.DafnyPrintResolvedFile == null || !bindings.WasResolved) {
        for (; i < bindings.ArgumentBindings.Count; i++) {
          var binding = bindings.ArgumentBindings[i];
          wr.Write(sep);
          sep = ", ";
          if (binding.IsGhost) {
            wr.Write("ghost ");
          }
          if (binding.FormalParameterName != null) {
            wr.Write($"{binding.FormalParameterName.val} := ");
          }
          PrintExpression(binding.Actual, false);
        }
      } else {
        // print arguments after incorporating default parameters
        for (; i < bindings.Arguments.Count; i++) {
          var arg = bindings.Arguments[i];
          if (arg is DefaultValueExpression { Resolved: null }) {
            // An error was detected during resolution, so this argument was not filled in. Omit printing it.
            continue;
          }
          wr.Write(sep);
          sep = ", ";
          PrintExpression(arg, false);
        }
      }
      wr.Write(")");
    }

    void PrintBindings(ActualBindings bindings, bool isFollowedBySemicolon) {
      Contract.Requires(bindings != null);
      string sep = "";
      foreach (var binding in bindings.ArgumentBindings) {
        wr.Write(sep);
        sep = ", ";
        if (binding.FormalParameterName != null) {
          wr.Write($"{binding.FormalParameterName.val} := ");
        }
        PrintExpression(binding.Actual, isFollowedBySemicolon);
      }
    }

    void PrintExpressionList(List<Expression> exprs, bool isFollowedBySemicolon) {
      Contract.Requires(exprs != null);
      string sep = "";
      foreach (Expression e in exprs) {
        Contract.Assert(e != null);
        wr.Write(sep);
        sep = ", ";
        PrintExpression(e, isFollowedBySemicolon);
      }
    }
    void PrintExpressionPairList(List<MapDisplayEntry> exprs) {
      Contract.Requires(exprs != null);
      string sep = "";
      foreach (MapDisplayEntry p in exprs) {
        Contract.Assert(p != null);
        wr.Write(sep);
        sep = ", ";
        PrintExpression(p.A, false);
        wr.Write(" := ");
        PrintExpression(p.B, false);
      }
    }

    void PrintFrameExpressionList(List<FrameExpression/*!*/>/*!*/ fexprs) {
      Contract.Requires(fexprs != null);
      string sep = "";
      foreach (FrameExpression fe in fexprs) {
        Contract.Assert(fe != null);
        wr.Write(sep);
        sep = ", ";
        if (fe.E is ImplicitThisExpr) {
          Contract.Assert(fe.FieldName != null);
        } else {
          PrintExpression(fe.E, true);
        }
        if (fe.FieldName != null) {
          wr.Write("`{0}", fe.FieldName);
        }
      }
    }

    /// <summary>
    /// An indent of -1 means print the entire expression on one line.
    /// </summary>
    void PrintExpr(Expression expr, int contextBindingStrength, bool fragileContext, bool isRightmost, bool isFollowedBySemicolon, int indent, string keyword = null, int resolv_count = 2) {
      Contract.Requires(-1 <= indent);
      Contract.Requires(expr != null);

      /* When debugging:
      if (resolv_count > 0 && expr.Resolved != null) {
        PrintExpr(expr.Resolved, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent, resolv_count - 1);
        return;
      }
      */

      if (expr is StaticReceiverExpr) {
        StaticReceiverExpr e = (StaticReceiverExpr)expr;
        wr.Write(e.Type);
      } else if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;
        if (e.Value == null) {
          wr.Write("null");
        } else if (e.Value is bool) {
          wr.Write((bool)e.Value ? "true" : "false");
        } else if (e is CharLiteralExpr) {
          wr.Write("'{0}'", (string)e.Value);
        } else if (e is StringLiteralExpr) {
          var str = (StringLiteralExpr)e;
          wr.Write("{0}\"{1}\"", str.IsVerbatim ? "@" : "", (string)e.Value);
        } else if (e.Value is BaseTypes.BigDec) {
          BaseTypes.BigDec dec = (BaseTypes.BigDec)e.Value;
          wr.Write((dec.Mantissa >= 0) ? "" : "-");
          string s = BigInteger.Abs(dec.Mantissa).ToString();
          int digits = s.Length;
          if (dec.Exponent >= 0) {
            wr.Write("{0}{1}.0", s, new string('0', dec.Exponent));
          } else {
            int exp = -dec.Exponent;
            if (exp < digits) {
              int intDigits = digits - exp;
              int fracDigits = digits - intDigits;
              wr.Write("{0}.{1}", s.Substring(0, intDigits), s.Substring(intDigits, fracDigits));
            } else {
              int fracDigits = digits;
              wr.Write("0.{0}{1}", new string('0', exp - fracDigits), s.Substring(0, fracDigits));
            }
          }
        } else {
          wr.Write((BigInteger)e.Value);
        }

      } else if (expr is ThisExpr) {
        wr.Write("this");

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        if (printFlags.UseOriginalDafnyNames) {
          wr.Write(e.DafnyName);
        } else {
          wr.Write(e.Name);
        }

      } else if (expr is DatatypeValue) {
        var dtv = (DatatypeValue)expr;
        bool printParens;
        if (dtv.MemberName.StartsWith(SystemModuleManager.TupleTypeCtorNamePrefix)) {
          // we're looking at a tuple, whose printed constructor name is essentially the empty string
          printParens = true;
        } else {
          var typeArgs = "";
          if (dtv.InferredTypeArgs != null && dtv.InferredTypeArgs.Count != 0) {
            typeArgs = $"<{string.Join(",", dtv.InferredTypeArgs.ConvertAll(ty => ty.ToString()))}>";
          }
          wr.Write("{0}{1}.{2}", dtv.DatatypeName, typeArgs, dtv.MemberName);
          printParens = dtv.Arguments.Count != 0;
        }
        if (printParens) {
          PrintActualArguments(dtv.Bindings, null, null);
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        if (e is MultiSetDisplayExpr) {
          wr.Write("multiset");
        } else if (e is SetDisplayExpr && !((SetDisplayExpr)e).Finite) {
          wr.Write("iset");
        }
        wr.Write(e is SetDisplayExpr || e is MultiSetDisplayExpr ? "{" : "[");
        PrintExpressionList(e.Elements, false);
        wr.Write(e is SetDisplayExpr || e is MultiSetDisplayExpr ? "}" : "]");

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        wr.Write(e.Finite ? "map" : "imap");
        wr.Write("[");
        PrintExpressionPairList(e.Elements);
        wr.Write("]");

      } else if (expr is NameSegment) {
        var e = (NameSegment)expr;
        wr.Write(e.Name);
        if (e.OptTypeArguments != null) {
          PrintTypeInstantiation(e.OptTypeArguments);
        }

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = !e.Lhs.IsImplicit && ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);
        Contract.Assert(!parensNeeded); // KRML: I think parens are never needed

        if (parensNeeded) { wr.Write("("); }
        if (!e.Lhs.IsImplicit) {
          PrintExpr(e.Lhs, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1, keyword);
          if (e.Lhs.Type is ResolverIdentifierExpr.ResolverTypeType) {
            Contract.Assert(e.Lhs is NameSegment || e.Lhs is ExprDotName);  // these are the only expressions whose .Type can be ResolverType_Type
            if (options.DafnyPrintResolvedFile != null && options.PrintMode == PrintModes.Everything) {
              // The printing of e.Lhs printed the type arguments only if they were given explicitly in the input.
              var optionalTypeArgs = e.Lhs is NameSegment ns ? ns.OptTypeArguments : ((ExprDotName)e.Lhs).OptTypeArguments;
              if (optionalTypeArgs == null && e.Lhs.Resolved is ResolverIdentifierExpr ri) {
                PrintTypeInstantiation(ri.TypeArgs);
              }
            }
          }
          wr.Write(".");
        }
        wr.Write(e.SuffixName);
        PrintTypeInstantiation(e.OptTypeArguments);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = !e.Lhs.IsImplicit && ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);
        Contract.Assert(!parensNeeded); // KRML: I think parens are never needed

        if (parensNeeded) { wr.Write("("); }
        if (ParensMayMatter(e.Lhs)) {
          wr.Write("(");
          PrintExpression(e.Lhs, false);
          wr.Write(")");
        } else {
          PrintExpr(e.Lhs, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1, keyword);
        }
        string name = e.Lhs is NameSegment ? ((NameSegment)e.Lhs).Name : e.Lhs is ExprDotName ? ((ExprDotName)e.Lhs).SuffixName : null;
        PrintActualArguments(e.Bindings, name, e.AtTok);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = !e.Obj.IsImplicit && ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        if (!(e.Obj.IsImplicit)) {
          PrintExpr(e.Obj, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1, keyword);
          wr.Write(".");
        }
        wr.Write(e.MemberName);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Seq, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, indent, keyword);
        wr.Write("[");
        if (e.SelectOne) {
          Contract.Assert(e.E0 != null);
          PrintExpression(e.E0, false);
        } else {
          if (e.E0 != null) {
            PrintExpression(e.E0, false);
          }
          wr.Write(e.E0 != null && e.E1 != null ? " .. " : "..");
          if (e.E1 != null) {
            PrintExpression(e.E1, false);
          }
        }
        wr.Write("]");
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Array, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, indent, keyword);
        string prefix = "[";
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          wr.Write(prefix);
          PrintExpression(idx, false);
          prefix = ", ";
        }
        wr.Write("]");
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Seq, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, indent, keyword);
        wr.Write("[");
        PrintExpression(e.Index, false);
        wr.Write(" := ");
        PrintExpression(e.Value, false);
        wr.Write("]");
        if (parensNeeded) { wr.Write(")"); }
      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Root, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, indent, keyword);
        wr.Write(".(");
        var sep = "";
        foreach (var update in e.Updates) {
          wr.Write("{0}{1} := ", sep, update.Item2);
          PrintExpression(update.Item3, false);
          sep = ", ";
        }
        wr.Write(")");
        if (options.DafnyPrintResolvedFile != null && options.PrintMode == PrintModes.Everything) {
          if (e.ResolvedExpression != null) {
            wr.Write("/*");
            PrintExpression(e.ResolvedExpression, false);
            wr.Write("*/");
          }
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }

        PrintExpr(e.Function, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1, keyword);
        wr.Write("(");
        PrintExpressionList(e.Args, false);
        wr.Write(")");

        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthSuffix;
        bool parensNeeded = !e.Receiver.IsImplicit && ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        if (!e.Receiver.IsImplicit) {
          PrintExpr(e.Receiver, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1, keyword);
          wr.Write(".");
        }
        wr.Write(e.Name);
        /* When debugging, this is nice to have:
        if (e.TypeArgumentSubstitutions.Count > 0) {
          wr.Write("[");
          wr.Write(Util.Comma(",", e.TypeArgumentSubstitutions, kv => kv.Key.FullName() + "->" + kv.Value));
          wr.Write("]");
        }
        */
        if (e.OpenParen == null && e.Args.Count == 0) {
        } else {
          PrintActualArguments(e.Bindings, e.Name, null);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        wr.Write("seq");
        if (e.ExplicitElementType != null) {
          wr.Write("<{0}>", e.ExplicitElementType);
        }
        wr.Write("(");
        PrintExpression(e.N, false);
        wr.Write(", ");
        PrintExpression(e.Initializer, false);
        wr.Write(")");

      } else if (expr is MultiSetFormingExpr) {
        wr.Write("multiset(");
        PrintExpression(((MultiSetFormingExpr)expr).E, false);
        wr.Write(")");

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        wr.Write("old");
        if (e.At != null) {
          wr.Write("@{0}", e.At);
        }
        wr.Write("(");
        PrintExpression(e.Expr, false);
        wr.Write(")");

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        wr.Write("unchanged");
        if (e.At != null) {
          wr.Write("@{0}", e.At);
        }
        wr.Write("(");
        PrintFrameExpressionList(e.Frame);
        wr.Write(")");

      } else if (expr is FreshExpr) {
        var e = (FreshExpr)expr;
        var label = e.At;
        wr.Write("fresh{0}(", label == null ? "" : "@" + label);
        PrintExpression(e.E, false);
        wr.Write(")");

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Cardinality) {
          wr.Write("|");
          PrintExpression(e.E, false);
          wr.Write("|");
        } else if (e.Op == UnaryOpExpr.Opcode.Allocated) {
          wr.Write("allocated(");
          PrintExpression(e.E, false);
          wr.Write(")");
        } else if (e.Op == UnaryOpExpr.Opcode.Lit) {
          wr.Write("Lit(");
          PrintExpression(e.E, false);
          wr.Write(")");
        } else if (e.Op == UnaryOpExpr.Opcode.Assigned) {
          wr.Write("assigned(");
          PrintExpression(e.E, false);
          wr.Write(")");
        } else {
          Contract.Assert(e.Op != UnaryOpExpr.Opcode.Fresh); // this is handled is "is FreshExpr" case above
          // Prefix operator.
          // determine if parens are needed
          string op;
          int opBindingStrength;
          switch (e.Op) {
            case UnaryOpExpr.Opcode.Not:
              op = "!"; opBindingStrength = BindingStrengthUnaryPrefix; break;
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary opcode
          }
          bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

          if (parensNeeded) { wr.Write("("); }
          wr.Write(op);
          PrintExpr(e.E, opBindingStrength, false, parensNeeded || isRightmost, !parensNeeded && isFollowedBySemicolon, -1, keyword);
          if (parensNeeded) { wr.Write(")"); }
        }

      } else if (expr is TypeUnaryExpr) {
        var e = (TypeUnaryExpr)expr;
        int opBindingStrength = BindingStrengthUnarySuffix;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.E, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1, keyword);
        Contract.Assert(e is ConversionExpr || e is TypeTestExpr);
        wr.Write(e is ConversionExpr ? " as " : " is ");
        PrintType(e.ToType);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        // determine if parens are needed
        int opBindingStrength;
        bool fragileLeftContext = false;  // false means "allow same binding power on left without parens"
        bool fragileRightContext = false;  // false means "allow same binding power on right without parens"
        switch (e.Op) {
          case BinaryExpr.Opcode.LeftShift:
          case BinaryExpr.Opcode.RightShift:
            opBindingStrength = BindingStrengthShift; fragileRightContext = true; break;
          case BinaryExpr.Opcode.Add: {
              opBindingStrength = BindingStrengthAdd;
              var t1 = e.E1.Type;
              fragileRightContext = t1 == null || !(t1.IsIntegerType || t1.IsRealType || t1.IsBigOrdinalType || t1.IsBitVectorType);
              break;
            }
          case BinaryExpr.Opcode.Sub:
            opBindingStrength = BindingStrengthAdd; fragileRightContext = true; break;
          case BinaryExpr.Opcode.Mul: {
              opBindingStrength = BindingStrengthMul;
              var t1 = e.E1.Type;
              fragileRightContext = t1 == null || !(t1.IsIntegerType || t1.IsRealType || t1.IsBigOrdinalType || t1.IsBitVectorType);
              break;
            }
          case BinaryExpr.Opcode.Div:
          case BinaryExpr.Opcode.Mod:
            opBindingStrength = BindingStrengthMul; fragileRightContext = true; break;
          case BinaryExpr.Opcode.BitwiseAnd:
            opBindingStrength = BindingStrengthBitwiseAnd; break;
          case BinaryExpr.Opcode.BitwiseOr:
            opBindingStrength = BindingStrengthBitwiseOr; break;
          case BinaryExpr.Opcode.BitwiseXor:
            opBindingStrength = BindingStrengthBitwiseXor; break;
          case BinaryExpr.Opcode.Eq:
          case BinaryExpr.Opcode.Neq:
          case BinaryExpr.Opcode.Gt:
          case BinaryExpr.Opcode.Ge:
          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le:
          case BinaryExpr.Opcode.Disjoint:
          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            opBindingStrength = BindingStrengthCompare; fragileLeftContext = fragileRightContext = true; break;
          case BinaryExpr.Opcode.And:
            opBindingStrength = BindingStrengthAnd; break;
          case BinaryExpr.Opcode.Or:
            opBindingStrength = BindingStrengthOr; break;
          case BinaryExpr.Opcode.Imp:
            opBindingStrength = BindingStrengthImplies; fragileLeftContext = true; break;
          case BinaryExpr.Opcode.Exp:
            opBindingStrength = BindingStrengthExplies; fragileRightContext = true; break;
          case BinaryExpr.Opcode.Iff:
            opBindingStrength = BindingStrengthEquiv; break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary operator
        }
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        string op = BinaryExpr.OpcodeString(e.Op);
        if (parensNeeded) { wr.Write("("); }
        var sem = !parensNeeded && isFollowedBySemicolon;
        if (0 <= indent && e.Op == BinaryExpr.Opcode.And) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, indent, keyword);
          wr.WriteLine(" {0}", op);
          Indent(indent);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, indent, keyword);
        } else if (0 <= indent && e.Op == BinaryExpr.Opcode.Imp) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, indent, keyword);
          wr.WriteLine(" {0}", op);
          int ind = indent + IndentAmount;
          Indent(ind);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, ind, keyword);
        } else if (0 <= indent && e.Op == BinaryExpr.Opcode.Exp) {
          PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, indent, keyword);
          wr.WriteLine(" {0}", op);
          int ind = indent + IndentAmount;
          Indent(ind);
          PrintExpr(e.E0, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, ind, keyword);
        } else if (e.Op == BinaryExpr.Opcode.Exp) {
          PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, -1, keyword);
          wr.Write(" {0} ", op);
          PrintExpr(e.E0, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1, keyword);
        } else {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, -1, keyword);
          wr.Write(" {0} ", op);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1, keyword);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            var opBindingStrength = BindingStrengthCompare;
            var fragileLeftContext = true;
            var fragileRightContext = true;
            bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

            if (parensNeeded) { wr.Write("("); }
            var sem = !parensNeeded && isFollowedBySemicolon;
            PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, -1, keyword);
            wr.Write(" {0}#[", e.Op == TernaryExpr.Opcode.PrefixEqOp ? "==" : "!=");
            PrintExpression(e.E0, false);
            wr.Write("] ");
            PrintExpr(e.E2, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1, keyword);
            if (parensNeeded) { wr.Write(")"); }
            break;
          default:
            Contract.Assert(false);  // unexpected ternary operator
            break;
        }

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        // determine if parens are needed
        int opBindingStrength = BindingStrengthCompare;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        var sem = !parensNeeded && isFollowedBySemicolon;
        PrintExpr(e.Operands[0], opBindingStrength, true, false, sem, -1, keyword);
        for (int i = 0; i < e.Operators.Count; i++) {
          string op = BinaryExpr.OpcodeString(e.Operators[i]);
          if (e.PrefixLimits[i] == null) {
            wr.Write(" {0} ", op);
          } else {
            wr.Write(" {0}#[", op);
            PrintExpression(e.PrefixLimits[i], false);
            wr.Write("] ");
          }
          PrintExpr(e.Operands[i + 1], opBindingStrength, true, i == e.Operators.Count - 1 && (parensNeeded || isRightmost), sem, -1, keyword);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        if (e.Origin is AutoGeneratedOrigin) {
          wr.Write("/* ");
        }
        PrintAttributes(e.Attributes, true, indent);
        if (e.LHSs.Exists(lhs => lhs != null && lhs.Var != null && lhs.Var.IsGhost)) { wr.Write("ghost "); }
        wr.Write("var ");
        string sep = "";
        foreach (var lhs in e.LHSs) {
          wr.Write(sep);
          PrintCasePattern(lhs);
          sep = ", ";
        }
        if (e.Exact) {
          wr.Write(" := ");
        } else {
          PrintAttributes(e.Attributes, false);
          wr.Write(" :| ");
        }
        PrintExpressionList(e.RHSs, true);
        wr.Write("; ");
        if (e.Origin is AutoGeneratedOrigin) {
          wr.Write("*/ ");
        }
        PrintExpression(e.Body, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is LetOrFailExpr) {
        // TODO should we also print the desugared version?
        // If so, should we insert newlines?
        var e = (LetOrFailExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        if (e.Lhs != null) {
          if (e.Lhs.Var != null && e.Lhs.Var.IsGhost) { wr.Write("ghost "); }
          wr.Write("var ");
          PrintCasePattern(e.Lhs);
          wr.Write(" :- ");
        } else {
          wr.Write(":- ");
        }
        PrintExpression(e.Rhs, true);
        wr.Write("; ");
        PrintExpression(e.Body, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is QuantifierExpr) {
        QuantifierExpr e = (QuantifierExpr)expr;

        if (e.SplitQuantifier != null) {
          PrintExpr(e.SplitQuantifierExpression, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent, keyword, resolv_count);
          return;
        }

        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write(e is ForallExpr ? "forall" : "exists");
        wr.Write(" ");
        PrintQuantifierDomain(e.BoundVars, e.Attributes, e.Range);
        if (keyword == null) {
          wr.Write(" :: ");
        } else {
          wr.WriteLine();
          wr.Write(keyword);
        }
        if (0 <= indent) {
          int ind = indent + IndentAmount;
          wr.WriteLine();
          Indent(ind);
          PrintExpression(e.Term, !parensNeeded && isFollowedBySemicolon, ind);
        } else {
          PrintExpression(e.Term, !parensNeeded && isFollowedBySemicolon);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        PrintAttributes(e.Attributes, true, AtAttributesOnSameLineIndent);
        if (e.Finite) {
          wr.Write("set ");
        } else {
          wr.Write("iset ");
        }
        string sep = "";
        foreach (BoundVar bv in e.BoundVars) {
          wr.Write("{0}{1}", sep, bv.DisplayName);
          sep = ", ";
          PrintType(": ", bv.Type);
        }
        PrintAttributes(e.Attributes, false);
        wr.Write(" | ");
        PrintExpression(e.Range, !parensNeeded && isFollowedBySemicolon);
        if (!e.TermIsImplicit) {
          wr.Write(" :: ");
          PrintExpression(e.Term, !parensNeeded && isFollowedBySemicolon);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }

        PrintAttributes(e.Attributes, true);
        wr.Write(e.Finite ? "map " : "imap ");
        string sep = "";
        foreach (BoundVar bv in e.BoundVars) {
          wr.Write("{0}{1}", sep, bv.DisplayName);
          sep = ", ";
          PrintType(": ", bv.Type);
        }
        PrintAttributes(e.Attributes, false);
        wr.Write(" | ");
        PrintExpression(e.Range, false);
        wr.Write(" :: ");
        if (e.TermLeft != null) {
          PrintExpression(e.TermLeft, false);
          wr.Write(" := ");
        }
        PrintExpression(e.Term, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        var skipSignatureParens = e.BoundVars.Count == 1 && !ShowType(e.BoundVars[0].Type);
        if (!skipSignatureParens) { wr.Write("("); }
        wr.Write(Util.Comma(e.BoundVars, bv => bv.DisplayName + (ShowType(bv.Type) ? ": " + bv.Type : "")));
        if (!skipSignatureParens) { wr.Write(")"); }
        if (e.Range != null) {
          wr.Write(" requires ");
          PrintExpression(e.Range, false);
        }

        var firstReadsExpression = true;
        foreach (var read in e.Reads.Expressions) {
          if (firstReadsExpression) {
            PrintAttributes(e.Reads.Attributes, indent, () => {
              wr.Write(" reads ");
            });
            firstReadsExpression = false;
          } else {
            wr.Write(", ");
          }

          PrintExpression(read.E, false);
        }
        wr.Write(" => ");
        PrintExpression(e.Term, isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is WildcardExpr) {
        wr.Write("*");

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        bool parensNeeded;
        if (e.S is AssertStmt || e.S is ExpectStmt || e.S is AssumeStmt || e.S is CalcStmt) {
          parensNeeded = !isRightmost;
        } else {
          parensNeeded = !isRightmost || isFollowedBySemicolon;
        }
        if (parensNeeded) { wr.Write("("); }
        int ind = indent < 0 ? IndentAmount : indent;  // if the expression was to be printed on one line, instead print the .S part at indentation IndentAmount (not pretty, but something)
        PrintStatement(e.S, ind);
        wr.Write(" ");
        PrintExpression(e.E, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ITEExpr) {
        ITEExpr ite = (ITEExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("if ");
        if (options.DafnyPrintResolvedFile == null) {
          PrintGuard(ite.IsBindingGuard, ite.Test);
        } else {
          PrintExpression(ite.Test, false);
        }
        wr.Write(" then ");
        var thenBranch = options.DafnyPrintResolvedFile == null && ite.IsBindingGuard ? ((LetExpr)ite.Thn).Body : ite.Thn;
        PrintExpression(thenBranch, false);
        wr.Write(" else ");
        PrintExpression(ite.Els, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        // printing of parentheses is done optimally, not according to the parentheses in the given program
        PrintExpr(e.E, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent, keyword);

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        string op = "-";
        int opBindingStrength = BindingStrengthUnaryPrefix;
        bool parensNeeded = ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        wr.Write(op);
        PrintExpr(e.E, opBindingStrength, false, parensNeeded || isRightmost, !parensNeeded && isFollowedBySemicolon, -1, keyword);
        if (parensNeeded) { wr.Write(")"); }
      } else if (expr is NestedMatchExpr) {
        var e = (NestedMatchExpr)expr;
        var parensNeeded = !isRightmost && !e.UsesOptionalBraces;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("match ");
        PrintExpression(e.Source, isRightmost && e.Cases.Count == 0, !parensNeeded && isFollowedBySemicolon);
        if (e.UsesOptionalBraces) { wr.Write(" {"); }
        int i = 0;
        foreach (var mc in e.Cases) {
          bool isLastCase = i == e.Cases.Count - 1;
          PrintNestedMatchCase(isRightmost, isFollowedBySemicolon, mc, isLastCase, parensNeeded);
          i++;
        }
        if (e.UsesOptionalBraces) { wr.Write(" }"); } else if (parensNeeded) { wr.Write(")"); }
        // }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        if (options.DafnyPrintResolvedFile == null && e.OrigUnresolved != null) {
          PrintExpr(e.OrigUnresolved, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent);
        } else {
          var parensNeeded = !isRightmost && !e.UsesOptionalBraces;
          if (parensNeeded) { wr.Write("("); }
          wr.Write("match ");
          PrintExpression(e.Source, isRightmost && e.Cases.Count == 0, !parensNeeded && isFollowedBySemicolon);
          if (e.UsesOptionalBraces) { wr.Write(" {"); }
          int i = 0;
          foreach (var mc in e.Cases) {
            bool isLastCase = i == e.Cases.Count - 1;
            wr.Write(" case {0}", mc.Ctor.Name);
            PrintMatchCaseArgument(mc);
            wr.Write(" => ");
            PrintExpression(mc.Body, isRightmost && isLastCase, !parensNeeded && isFollowedBySemicolon);
            i++;
          }
          if (e.UsesOptionalBraces) {
            wr.Write(" }");
          } else if (parensNeeded) {
            wr.Write(")");
          }
        }

      } else if (expr is DefaultValueExpression) {
        var e = (DefaultValueExpression)expr;
        // DefaultValueExpression's are introduced during resolution, so we expect .Resolved to be non-null
        Contract.Assert(e.WasResolved());
        Contract.Assert(e.Resolved != null);
        PrintExpr(e.Resolved, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent, keyword);

      } else if (expr is BoxingCastExpr) {
        // this is not expected for a parsed program, but we may be called for /trace purposes in the translator
        var e = (BoxingCastExpr)expr;
        PrintExpr(e.E, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent, keyword);
      } else if (expr is BoogieGenerator.BoogieWrapper) {
        wr.Write("[BoogieWrapper]");  // this is somewhat unexpected, but we can get here if the /trace switch is used, so it seems best to cover this case here
      } else if (expr is BoogieGenerator.BoogieFunctionCall) {
        wr.Write("[BoogieFunctionCall]");  // this prevents debugger watch window crash
      } else if (expr is ResolverIdentifierExpr) {
        wr.Write("[Resolver_IdentifierExpr]");  // we can get here in the middle of a debugging session
      } else if (expr is DecreasesToExpr decreasesToExpr) {
        var opBindingStrength = BindingStrengthDecreasesTo;
        var parensNeeded =
          opBindingStrength < contextBindingStrength ||
          (opBindingStrength == contextBindingStrength && fragileContext) ||
          decreasesToExpr.OldExpressions.Count != 1 || decreasesToExpr.NewExpressions.Count != 1; // always parenthesize non-simple expressions

        if (parensNeeded) { wr.Write("("); }

        var comma = false;
        foreach (var oldExpr in decreasesToExpr.OldExpressions) {
          if (comma) {
            wr.Write(", ");
          }
          PrintExpr(oldExpr, opBindingStrength, true, false, false, -1);
          comma = true;
        }
        if (decreasesToExpr.AllowNoChange) {
          wr.Write(" nonincreases to ");
        } else {
          wr.Write(" decreases to ");
        }
        comma = false;
        foreach (var newExpr in decreasesToExpr.NewExpressions) {
          if (comma) {
            wr.Write(", ");
          }
          PrintExpr(newExpr, opBindingStrength, true, !parensNeeded && isRightmost, true, -1);
          comma = true;
        }

        if (parensNeeded) { wr.Write(")"); }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    public void PrintNestedMatchCase(bool isRightmost, bool isFollowedBySemicolon, NestedMatchCaseExpr mc, bool isLastCase,
      bool parensNeeded) {
      wr.Write(" ");
      PrintAttributes(mc.Attributes, AtAttributesOnSameLineIndent, () => {
        wr.Write("case");
      });
      wr.Write(" ");
      PrintExtendedPattern(mc.Pat);
      wr.Write(" => ");
      PrintExpression(mc.Body, isRightmost && isLastCase, !parensNeeded && isFollowedBySemicolon);
    }
  }
}
