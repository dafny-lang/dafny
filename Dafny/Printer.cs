//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Printer {
    TextWriter wr;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(wr!=null);
    }

    public Printer(TextWriter wr) {
      Contract.Requires(wr != null);
      this.wr = wr;
    }

    public void PrintProgram(Program prog) {
      Contract.Requires(prog != null);
      if (Bpl.CommandLineOptions.Clo.ShowEnv != Bpl.CommandLineOptions.ShowEnvironment.Never) {
        wr.WriteLine("// " + Bpl.CommandLineOptions.Clo.Version);
        wr.WriteLine("// " + Bpl.CommandLineOptions.Clo.Environment);
      }
      wr.WriteLine("// {0}", prog.Name);
      foreach (ModuleDecl module in prog.Modules) {
        wr.WriteLine();
        if (module.IsDefaultModule) {
          PrintTopLevelDecls(module.TopLevelDecls, 0);
        } else {
          wr.Write("module");
          PrintAttributes(module.Attributes);
          wr.Write(" {0} ", module.Name);
          if (module.RefinementBaseName != null) {
            wr.Write("refines {0} ", module.RefinementBaseName);
          }
          if (module.ImportNames.Count != 0) {
            string sep = "imports ";
            foreach (string imp in module.ImportNames) {
              wr.Write("{0}{1}", sep, imp);
              sep = ", ";
            }
          }
          if (module.TopLevelDecls.Count == 0) {
            wr.WriteLine(" { }");
          } else {
            wr.WriteLine(" {");
            PrintTopLevelDecls(module.TopLevelDecls, IndentAmount);
            wr.WriteLine("}");
          }
        }
      }
    }

    public void PrintTopLevelDecls(List<TopLevelDecl> classes, int indent) {
      Contract.Requires(classes!= null);
      int i = 0;
      foreach (TopLevelDecl d in classes) {
        Contract.Assert(d != null);
        if (d is ArbitraryTypeDecl) {
          var at = (ArbitraryTypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("type", at.Attributes, at.Name, new List<TypeParameter>());
          if (at.EqualitySupport == TypeParameter.EqualitySupportValue.Required) {
            wr.Write("(==)");
          }
          wr.WriteLine(";");
        } else if (d is DatatypeDecl) {
          if (i++ != 0) { wr.WriteLine(); }
          PrintDatatype((DatatypeDecl)d, indent);
        } else {
          ClassDecl cl = (ClassDecl)d;
          if (!cl.IsDefaultClass) {
            if (i++ != 0) { wr.WriteLine(); }
            PrintClass(cl, indent);
          } else if (cl.Members.Count == 0) {
            // print nothing
          } else {
            if (i++ != 0) { wr.WriteLine(); }
            PrintClass_Members(cl, indent);
          }
        }
      }
    }

    public void PrintClass(ClassDecl c, int indent) {
      Contract.Requires(c != null);
      Indent(indent);
      PrintClassMethodHelper("class", c.Attributes, c.Name, c.TypeArgs);
      if (c.Members.Count == 0) {
        wr.WriteLine(" { }");
      } else {
        wr.WriteLine(" {");
        PrintClass_Members(c, indent + IndentAmount);
        Indent(indent);
        wr.WriteLine("}");
      }
    }

    public void PrintClass_Members(ClassDecl c, int indent)
    {
      Contract.Requires(c != null);
      Contract.Requires( c.Members.Count != 0);

      int state = 0;  // 0 - no members yet; 1 - previous member was a field; 2 - previous member was non-field
      foreach (MemberDecl m in c.Members) {
        if (m is Method) {
          if (state != 0) { wr.WriteLine(); }
          PrintMethod((Method)m, indent);
          state = 2;
        } else if (m is Field) {
          if (state == 2) { wr.WriteLine(); }
          PrintField((Field)m, indent);
          state = 1;
        } else if (m is Function) {
          if (state != 0) { wr.WriteLine(); }
          PrintFunction((Function)m, indent);
          state = 2;
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
      }
    }

    /// <summary>
    /// Prints no space before "kind", but does print a space before "attrs" and "name".
    /// </summary>
    void PrintClassMethodHelper(string kind, Attributes attrs, string name, List<TypeParameter> typeArgs) {
      Contract.Requires(kind != null);
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      if (kind.Length != 0) {
        wr.Write(kind);
      }

      PrintAttributes(attrs);

      wr.Write(" {0}", name);
      if (typeArgs.Count != 0) {
        wr.Write("<");
        string sep = "";
        foreach (TypeParameter tp in typeArgs) {
          Contract.Assert(tp != null);
          wr.Write("{0}{1}", sep, tp.Name);
          if (tp.EqualitySupport == TypeParameter.EqualitySupportValue.Required) {
            wr.Write("(==)");
          }
          sep = ", ";
        }
        wr.Write(">");
      }
    }

    public void PrintDatatype(DatatypeDecl dt, int indent) {
      Contract.Requires(dt != null);
      Indent(indent);
      PrintClassMethodHelper(dt is IndDatatypeDecl ? "datatype" : "codatatype", dt.Attributes, dt.Name, dt.TypeArgs);
      wr.Write(" =");
      string sep = "";
      foreach (DatatypeCtor ctor in dt.Ctors) {
        wr.Write(sep);
        PrintClassMethodHelper("", ctor.Attributes, ctor.Name, new List<TypeParameter>());
        if (ctor.Formals.Count != 0) {
          PrintFormals(ctor.Formals);
        }
        sep = " |";
      }
      wr.WriteLine(";");
    }

    /// <summary>
    /// Prints a space before each attribute.
    /// </summary>
    public void PrintAttributes(Attributes a) {
      if (a != null) {
        PrintAttributes(a.Prev);

        wr.Write(" {{:{0}", a.Name);
        if (a.Args != null)
        {
          PrintAttributeArgs(a.Args);
        }
        wr.Write("}");
      }
    }

    public void PrintAttributeArgs(List<Attributes.Argument> args) {
      Contract.Requires(args != null);
      string prefix = " ";
      foreach (Attributes.Argument arg in args) {
        Contract.Assert(arg != null);
        wr.Write(prefix);
        prefix = ", ";
        if (arg.S != null) {
          wr.Write("\"{0}\"", arg.S);
        } else {
          Contract.Assert( arg.E != null);
          PrintExpression(arg.E);
        }
      }
    }

    public void PrintField(Field field, int indent) {
      Contract.Requires(field != null);
      Indent(indent);
      if (field.IsGhost) {
        wr.Write("ghost ");
      }
      wr.Write("var");
      PrintAttributes(field.Attributes);
      wr.Write(" {0}: ", field.Name);
      PrintType(field.Type);
      wr.WriteLine(";");
    }

    public void PrintFunction(Function f, int indent) {
      Contract.Requires(f != null);
      var isPredicate = f is Predicate;
      Indent(indent);
      string k = isPredicate ? "predicate" : "function";
      if (f.IsStatic) { k = "static " + k; }
      if (!f.IsGhost) { k += " method"; }
      PrintClassMethodHelper(k, f.Attributes, f.Name, f.TypeArgs);
      if (f.SignatureIsOmitted) {
        wr.WriteLine(" ...");
      } else {
        if (f.OpenParen != null) {
          PrintFormals(f.Formals);
        } else {
          Contract.Assert(isPredicate);
        }
        if (!isPredicate) {
          wr.Write(": ");
          PrintType(f.ResultType);
        }
        wr.WriteLine();
      }

      int ind = indent + IndentAmount;
      PrintSpec("requires", f.Req, ind);
      PrintFrameSpecLine("reads", f.Reads, ind, null);
      PrintSpec("ensures", f.Ens, ind);
      PrintDecreasesSpec(f.Decreases, ind);
      if (f.Body != null) {
        Indent(indent);
        wr.WriteLine("{");
        PrintExtendedExpr(f.Body, ind, true, false);
        Indent(indent);
        wr.WriteLine("}");
      }
    }

    // ----------------------------- PrintMethod -----------------------------

    const int IndentAmount = 2;
    const string BunchaSpaces = "                                ";
    void Indent(int amount)
    {  Contract.Requires( 0 <= amount);

      while (0 < amount) {
        wr.Write(BunchaSpaces.Substring(0, amount));
        amount -= BunchaSpaces.Length;
      }
    }

    public void PrintMethod(Method method, int indent) {
      Contract.Requires(method != null);

      Indent(indent);
      string k = method is Constructor ? "constructor" : "method";
      if (method.IsStatic) { k = "static " + k; }
      if (method.IsGhost) { k = "ghost " + k; }
      PrintClassMethodHelper(k, method.Attributes, method.Name, method.TypeArgs);
      if (method.SignatureIsOmitted) {
        wr.WriteLine(" ...");
      } else {
        PrintFormals(method.Ins);
        if (method.Outs.Count != 0) {
          if (method.Ins.Count + method.Outs.Count <= 3) {
            wr.Write(" returns ");
          } else {
            wr.WriteLine();
            Indent(3 * IndentAmount);
            wr.Write("returns ");
          }
          PrintFormals(method.Outs);
        }
        wr.WriteLine();
      }

      int ind = indent + IndentAmount;
      PrintSpec("requires", method.Req, ind);
      if (method.Mod.Expressions != null)
      {
        PrintFrameSpecLine("modifies", method.Mod.Expressions, ind, method.Mod.HasAttributes() ? method.Mod.Attributes : null);
      }
      PrintSpec("ensures", method.Ens, ind);
      PrintDecreasesSpec(method.Decreases, ind);

      if (method.Body != null) {
        Indent(indent);
        PrintStatement(method.Body, indent);
        wr.WriteLine();
      }
    }

    void PrintFormals(List<Formal> ff) {
      Contract.Requires(ff!=null);
      wr.Write("(");
      string sep = "";
      foreach (Formal f in ff) {
        Contract.Assert(f != null);
        wr.Write(sep);
        sep = ", ";
        PrintFormal(f);
      }
      wr.Write(")");
    }

    void PrintFormal(Formal f) {
      Contract.Requires(f != null);
      if (f.IsGhost) {
        wr.Write("ghost ");
      }
      if (f.HasName) {
        wr.Write("{0}: ", f.Name);
      }
      PrintType(f.Type);
    }

    void PrintSpec(string kind, List<Expression> ee, int indent) {
      Contract.Requires(kind != null);
      Contract.Requires(ee != null);
      foreach (Expression e in ee) {
        Contract.Assert(e != null);
        Indent(indent);
        wr.Write("{0} ", kind);
        PrintExpression(e);
        wr.WriteLine(";");
      }
    }

    void PrintDecreasesSpec(Specification<Expression> decs, int indent) {
      Contract.Requires(decs != null);
      if (decs.Expressions != null && decs.Expressions.Count != 0) {
        Indent(indent);
        wr.Write("decreases");
        if (decs.HasAttributes())
        {
          PrintAttributes(decs.Attributes);
        }
        wr.Write(" ");
        PrintExpressionList(decs.Expressions);
        wr.WriteLine(";");
      }
    }

    void PrintFrameSpecLine(string kind, List<FrameExpression/*!*/> ee, int indent, Attributes attrs) {
      Contract.Requires(kind != null);
      Contract.Requires(cce.NonNullElements(ee));
      if (ee != null && ee.Count != 0) {
        Indent(indent);
        wr.Write("{0}", kind);
        if (attrs != null) {
          PrintAttributes(attrs);
        }
        wr.Write(" ");
        PrintFrameExpressionList(ee);
        wr.WriteLine(";");
      }
    }

    void PrintSpec(string kind, List<MaybeFreeExpression> ee, int indent) {
      Contract.Requires(kind != null);
      Contract.Requires(ee != null);
      foreach (MaybeFreeExpression e in ee)
      {
        Contract.Assert(e != null);
        Indent(indent);
        wr.Write("{0}{1}", e.IsFree ? "free " : "", kind);

        if (e.HasAttributes())
        {
          PrintAttributes(e.Attributes);
        }

        wr.Write(" ");
        PrintExpression(e.E);

        wr.WriteLine(";");
      }
    }

    // ----------------------------- PrintType -----------------------------

    public void PrintType(Type ty) {
      Contract.Requires(ty != null);
      wr.Write(ty.ToString());
    }

    public void PrintType(string prefix, Type ty) {
      Contract.Requires(prefix != null);
      Contract.Requires(ty != null);
      string s = ty.ToString();
      if (s != "?") {
        wr.Write("{0}{1}", prefix, s);
      }
    }

    // ----------------------------- PrintStatement -----------------------------

    /// <summary>
    /// Prints from the current position of the current line.
    /// If the statement requires several lines, subsequent lines are indented at "indent".
    /// No newline is printed after the statement.
    /// </summary>
    public void PrintStatement(Statement stmt, int indent) {
      Contract.Requires(stmt != null);
      for (LList<Label> label = stmt.Labels; label != null; label = label.Next) {
        if (label.Data.Name != null) {
          wr.WriteLine("label {0}:", label.Data.Name);
          Indent(indent);
        }
      }

      if (stmt is PredicateStmt) {
        Expression expr = ((PredicateStmt)stmt).Expr;
        wr.Write(stmt is AssertStmt ? "assert" : "assume");
        if (stmt.HasAttributes()) {
          PrintAttributes(stmt.Attributes);
        }
        wr.Write(" ");
        PrintExpression(expr);
        wr.Write(";");

      } else if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        wr.Write("print");
        PrintAttributeArgs(s.Args);
        wr.Write(";");

      } else if (stmt is BreakStmt) {
        BreakStmt s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          wr.Write("break {0};", s.TargetLabel);
        } else {
          string sep = "";
          for (int i = 0; i < s.BreakCount; i++) {
            wr.Write("{0}break", sep);
            sep = " ";
          }
          wr.Write(";");
        }

      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt) stmt;
        wr.Write("return");
        if (s.rhss != null) {
          var sep = " ";
          foreach (var rhs in s.rhss) {
            wr.Write(sep);
            PrintRhs(rhs);
            sep = ", ";
          }
        }
          wr.Write(";");

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        PrintExpression(s.Lhs);
        wr.Write(" := ");
        PrintRhs(s.Rhs);
        wr.Write(";");

      } else if (stmt is VarDecl) {
        VarDecl s = (VarDecl)stmt;
        if (s.IsGhost) {
          wr.Write("ghost ");
        }
        wr.Write("var {0}", s.Name);
        PrintType(": ", s.OptionalType);
        wr.Write(";");

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        if (s.Lhs.Count != 0) {
          string sep = "";
          foreach (IdentifierExpr v in s.Lhs) {
            wr.Write(sep);
            PrintExpression(v);
            sep = ", ";
          }
          wr.Write(" := ");
        }
        if (!(s.Receiver is ImplicitThisExpr)) {
          PrintExpr(s.Receiver, 0x70, false, false, -1);
          wr.Write(".");
        }
        wr.Write("{0}(", s.MethodName);
        PrintExpressionList(s.Args);
        wr.Write(");");

      } else if (stmt is BlockStmt) {
        wr.WriteLine("{");
        int ind = indent + IndentAmount;
        foreach (Statement s in ((BlockStmt)stmt).Body) {
          Indent(ind);
          PrintStatement(s, ind);
          wr.WriteLine();
        }
        Indent(indent);
        wr.Write("}");

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        PrintIfStatement(indent, s, false);

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        wr.WriteLine("if {");
        PrintAlternatives(indent, s.Alternatives);
        Indent(indent);
        wr.Write("}");

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        PrintWhileStatement(indent, s, false, false);

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        wr.WriteLine("while");
        PrintSpec("invariant", s.Invariants, indent + IndentAmount);
        PrintDecreasesSpec(s.Decreases, indent + IndentAmount);

        Indent(indent);
        wr.WriteLine("{");
        PrintAlternatives(indent, s.Alternatives);
        Indent(indent);
        wr.Write("}");

      } else if (stmt is ParallelStmt) {
        var s = (ParallelStmt)stmt;
        wr.Write("parallel (");
        if (s.BoundVars.Count != 0) {
          PrintQuantifierDomain(s.BoundVars, s.Attributes, s.Range);
        }
        if (s.Ens.Count == 0) {
          wr.Write(") ");
        } else {
          wr.WriteLine(")");
          PrintSpec("ensures", s.Ens, indent + IndentAmount);
          Indent(indent);
        }
        PrintStatement(s.Body, indent);

      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt)stmt;
        wr.Write("match ");
        PrintExpression(s.Source);
        wr.WriteLine(" {");
        int caseInd = indent + IndentAmount;
        foreach (MatchCaseStmt mc in s.Cases) {
          Indent(caseInd);
          wr.Write("case {0}", mc.Id);
          if (mc.Arguments.Count != 0) {
            string sep = "(";
            foreach (BoundVar bv in mc.Arguments) {
              wr.Write("{0}{1}", sep, bv.Name);
              sep = ", ";
            }
            wr.Write(")");
          }
          wr.WriteLine(" =>");
          foreach (Statement bs in mc.Body) {
            Indent(caseInd + IndentAmount);
            PrintStatement(bs, caseInd + IndentAmount);
            wr.WriteLine();
          }
        }
        Indent(indent);
        wr.Write("}");

      } else if (stmt is ConcreteUpdateStatement) {
        var s = (ConcreteUpdateStatement)stmt;
        string sep = "";
        foreach (var lhs in s.Lhss) {
          wr.Write(sep);
          PrintExpression(lhs);
          sep = ", ";
        }
        PrintUpdateRHS(s);
        wr.Write(";");

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Lhss[0].IsGhost) {
          wr.Write("ghost ");
        }
        wr.Write("var ");
        string sep = "";
        foreach (var lhs in s.Lhss) {
          wr.Write("{0}{1}", sep, lhs.Name);
          PrintType(": ", lhs.OptionalType);
          sep = ", ";
        }
        if (s.Update != null) {
          PrintUpdateRHS(s.Update);
        }
        wr.Write(";");

      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        if (s.S == null) {
          wr.Write("...;");
        } else if (s.S is AssertStmt) {
          Contract.Assert(s.ConditionOmitted);
          wr.Write("assert ...;");
        } else if (s.S is AssumeStmt) {
          Contract.Assert(s.ConditionOmitted);
          wr.Write("assume ...;");
        } else if (s.S is IfStmt) {
          PrintIfStatement(indent, (IfStmt)s.S, s.ConditionOmitted);
        } else if (s.S is WhileStmt) {
          PrintWhileStatement(indent, (WhileStmt)s.S, s.ConditionOmitted, s.BodyOmitted);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected skeleton statement
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    /// <summary>
    /// Does not print LHS
    /// </summary>
    void PrintUpdateRHS(ConcreteUpdateStatement s) {
      Contract.Requires(s != null);
      if (s is UpdateStmt) {
        var update = (UpdateStmt)s;
        if (update.Lhss.Count != 0) {
          wr.Write(" := ");
        }
        var sep = "";
        foreach (var rhs in update.Rhss) {
          wr.Write(sep);
          PrintRhs(rhs);
          sep = ", ";
        }
      } else if (s is AssignSuchThatStmt) {
        var update = (AssignSuchThatStmt)s;
        wr.Write(" :| ");
        if (update.AssumeToken != null) {
          wr.Write("assume ");
        }
        PrintExpression(update.Expr);
      } else {
        Contract.Assert(s == null);  // otherwise, unknown type
      }
    }

    void PrintIfStatement(int indent, IfStmt s, bool omitGuard) {
      while (true) {
        if (omitGuard) {
          wr.Write("if ... ");
        } else {
          wr.Write("if (");
          PrintGuard(s.Guard);
          wr.Write(") ");
        }
        PrintStatement(s.Thn, indent);
        if (s.Els == null) {
          break;
        }
        wr.Write(" else ");
        if (s.Els is IfStmt) {
          s = (IfStmt)s.Els;
        } else {
          PrintStatement(s.Els, indent);
          break;
        }
      }
    }

    void PrintWhileStatement(int indent, WhileStmt s, bool omitGuard, bool omitBody) {
      if (omitGuard) {
        wr.WriteLine("while ...");
      } else {
        wr.Write("while (");
        PrintGuard(s.Guard);
        wr.WriteLine(")");
      }

      PrintSpec("invariant", s.Invariants, indent + IndentAmount);
      PrintDecreasesSpec(s.Decreases, indent + IndentAmount);
      if (s.Mod.Expressions != null) {
        PrintFrameSpecLine("modifies", s.Mod.Expressions, indent + IndentAmount, s.Mod.HasAttributes() ? s.Mod.Attributes : null);
      }
      Indent(indent);
      if (omitBody) {
        wr.WriteLine("...;");
      } else {
        PrintStatement(s.Body, indent);
      }
    }

    void PrintAlternatives(int indent, List<GuardedAlternative> alternatives) {
      int caseInd = indent + IndentAmount;
      foreach (var alternative in alternatives) {
        Indent(caseInd);
        wr.Write("case ");
        PrintExpression(alternative.Guard);
        wr.WriteLine(" =>");
        foreach (Statement s in alternative.Body) {
          Indent(caseInd + IndentAmount);
          PrintStatement(s, caseInd + IndentAmount);
          wr.WriteLine();
        }
      }
    }

    void PrintRhs(AssignmentRhs rhs) {
      Contract.Requires(rhs != null);
      if (rhs is ExprRhs) {
        PrintExpression(((ExprRhs)rhs).Expr);
      } else if (rhs is HavocRhs) {
        wr.Write("*");
      } else if (rhs is TypeRhs) {
        TypeRhs t = (TypeRhs)rhs;
        wr.Write("new ");
        PrintType(t.EType);
        if (t.ArrayDimensions != null) {
          string s = "[";
          foreach (Expression dim in t.ArrayDimensions) {
            Contract.Assume(dim != null);
            wr.Write(s);
            PrintExpression(dim);
            s = ", ";
          }
          wr.Write("]");
        } else if (t.InitCall != null) {
          wr.Write(".{0}(", t.InitCall.MethodName);
          PrintExpressionList(t.InitCall.Args);
          wr.Write(")");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
      }

      if (rhs.HasAttributes())
      {
        PrintAttributes(rhs.Attributes);
      }
    }

    void PrintGuard(Expression guard) {
      if (guard == null) {
        wr.Write("*");
      } else {
        PrintExpression(guard);
      }
    }

    // ----------------------------- PrintExpression -----------------------------

    public void PrintExtendedExpr(Expression expr, int indent, bool isRightmost, bool endWithCloseParen) {
      Contract.Requires(expr != null);
      Indent(indent);
      if (expr is ITEExpr) {
        while (true) {
          ITEExpr ite = (ITEExpr)expr;
          wr.Write("if ");
          PrintExpression(ite.Test);
          wr.WriteLine(" then");
          PrintExtendedExpr(ite.Thn, indent + IndentAmount, true, false);
          expr = ite.Els;
          if (expr is ITEExpr) {
            Indent(indent);  wr.Write("else ");
          } else {
            Indent(indent);  wr.WriteLine("else");
            Indent(indent + IndentAmount);
            PrintExpression(expr);
            wr.WriteLine(endWithCloseParen ? ")" : "");
            return;
          }
        }
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        wr.Write("match ");
        PrintExpression(me.Source);
        wr.WriteLine();
        int i = 0;
        foreach (MatchCaseExpr mc in me.Cases) {
          bool isLastCase = i == me.Cases.Count - 1;
          Indent(indent);
          wr.Write("case {0}", mc.Id);
          if (mc.Arguments.Count != 0) {
            string sep = "(";
            foreach (BoundVar bv in mc.Arguments) {
              wr.Write("{0}{1}", sep, bv.Name);
              sep = ", ";
            }
            wr.Write(")");
          }
          bool parensNeeded = !isLastCase && mc.Body.WasResolved() && mc.Body.Resolved is MatchExpr;
          if (parensNeeded) {
            wr.WriteLine(" => (");
          } else {
            wr.WriteLine(" =>");
          }
          PrintExtendedExpr(mc.Body, indent + IndentAmount, isLastCase, parensNeeded || (isLastCase && endWithCloseParen));
          i++;
        }
      } else if (expr is ParensExpression) {
        PrintExtendedExpr(((ParensExpression)expr).E, indent, isRightmost, endWithCloseParen);
      } else {
        PrintExpression(expr, indent);
        wr.WriteLine(endWithCloseParen ? ")" : "");
      }
    }

    public void PrintExpression(Expression expr) {
      Contract.Requires(expr != null);
      PrintExpr(expr, 0, false, true, -1);
    }

    /// <summary>
    /// An indent of -1 means print the entire expression on one line.
    /// </summary>
    public void PrintExpression(Expression expr, int indent) {
      Contract.Requires(expr != null);
      PrintExpr(expr, 0, false, true, indent);
    }

    /// <summary>
    /// An indent of -1 means print the entire expression on one line.
    /// </summary>
    void PrintExpr(Expression expr, int contextBindingStrength, bool fragileContext, bool isRightmost, int indent)
    {
      Contract.Requires(-1 <= indent);
      Contract.Requires(expr != null);

      if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;
        if (e.Value == null) {
          wr.Write("null");
        } else if (e.Value is bool) {
          wr.Write((bool)e.Value ? "true" : "false");
        } else {
          wr.Write((BigInteger)e.Value);
        }

      } else if (expr is ThisExpr) {
        wr.Write("this");

      } else if (expr is IdentifierExpr) {
        wr.Write(((IdentifierExpr)expr).Name);

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        wr.Write("#{0}.{1}", dtv.DatatypeName, dtv.MemberName);
        if (dtv.Arguments.Count != 0) {
          wr.Write("(");
          PrintExpressionList(dtv.Arguments);
          wr.Write(")");
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        if (e is MultiSetDisplayExpr) wr.Write("multiset");
        wr.Write(e is SetDisplayExpr || e is MultiSetDisplayExpr ? "{" : "[");
        PrintExpressionList(e.Elements);
        wr.Write(e is SetDisplayExpr || e is MultiSetDisplayExpr ? "}" : "]");

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        wr.Write("map");
        wr.Write("{");
        PrintExpressionPairList(e.Elements);
        wr.Write("}");
      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Obj is ImplicitThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        if (!(e.Obj is ImplicitThisExpr)) {
          PrintExpr(e.Obj, opBindingStrength, false, false, -1);
          wr.Write(".");
        }
        wr.Write(e.SuffixName);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Obj is ImplicitThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        if (!(e.Obj is ImplicitThisExpr)) {
          PrintExpr(e.Obj, opBindingStrength, false, false, -1);
          wr.Write(".");
        }
        wr.Write(e.FieldName);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Seq, 0x00, false, false, indent);  // BOGUS: fix me
        wr.Write("[");
        if (e.SelectOne) {
          Contract.Assert( e.E0 != null);
          PrintExpression(e.E0);
        } else {
          if (e.E0 != null) {
            PrintExpression(e.E0);
          }
          wr.Write(e.E0 != null && e.E1 != null ? " .. " : "..");
          if (e.E1 != null) {
            PrintExpression(e.E1);
          }
        }
        wr.Write("]");
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Array, 0x00, false, false, indent);  // BOGUS: fix me
        string prefix = "[";
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          wr.Write(prefix);
          PrintExpression(idx);
          prefix = ", ";
        }
        wr.Write("]");
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Seq, 00, false, false, indent);  // BOGUS: fix me
        wr.Write("[");
        PrintExpression(e.Index);
        wr.Write(" := ");
        PrintExpression(e.Value);
        wr.Write("]");
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Receiver is ImplicitThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        if (!(e.Receiver is ImplicitThisExpr)) {
          PrintExpr(e.Receiver, opBindingStrength, false, false, -1);
          wr.Write(".");
        }
        wr.Write(e.Name);
        if (e.OpenParen == null) {
          Contract.Assert(e.Args.Count == 0);
        } else {
          wr.Write("(");
          PrintExpressionList(e.Args);
          wr.Write(")");
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is OldExpr) {
        wr.Write("old(");
        PrintExpression(((OldExpr)expr).E);
        wr.Write(")");

      } else if (expr is MultiSetFormingExpr) {
        wr.Write("multiset(");
        PrintExpression(((MultiSetFormingExpr)expr).E);
        wr.Write(")");

      } else if (expr is FreshExpr) {
        wr.Write("fresh(");
        PrintExpression(((FreshExpr)expr).E);
        wr.Write(")");

      } else if (expr is AllocatedExpr) {
        wr.Write("allocated(");
        PrintExpression(((AllocatedExpr)expr).E);
        wr.Write(")");

      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        if (e.Op == UnaryExpr.Opcode.SeqLength) {
          wr.Write("|");
          PrintExpression(e.E);
          wr.Write("|");
        } else {
          // Prefix operator.
          // determine if parens are needed
          string op;
          int opBindingStrength;
          switch (e.Op) {
            case UnaryExpr.Opcode.SetChoose:
              op = "choose ";  opBindingStrength = 0;  break;
            case UnaryExpr.Opcode.Not:
              op = "!";  opBindingStrength = 0x60;  break;
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary opcode
          }
          bool parensNeeded = opBindingStrength < contextBindingStrength ||
            (fragileContext && opBindingStrength == contextBindingStrength);

          bool containsNestedNot = e.E is ParensExpression &&
                                ((ParensExpression)e.E).E is UnaryExpr &&
                                ((UnaryExpr)((ParensExpression)e.E).E).Op == UnaryExpr.Opcode.Not;

          if (parensNeeded) { wr.Write("("); }
          wr.Write(op);
          PrintExpr(e.E, opBindingStrength, containsNestedNot, parensNeeded || isRightmost, -1);
          if (parensNeeded) { wr.Write(")"); }
        }

      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        // determine if parens are needed
        int opBindingStrength;
        bool fragileLeftContext = false;  // false means "allow same binding power on left without parens"
        bool fragileRightContext = false;  // false means "allow same binding power on right without parens"
        switch (e.Op)
        {
          case BinaryExpr.Opcode.Add:
            opBindingStrength = 0x40; break;
          case BinaryExpr.Opcode.Sub:
            opBindingStrength = 0x40; fragileRightContext = true; break;
          case BinaryExpr.Opcode.Mul:
            opBindingStrength = 0x50; break;
          case BinaryExpr.Opcode.Div:
          case BinaryExpr.Opcode.Mod:
            opBindingStrength = 0x50; fragileRightContext = true; break;
          case BinaryExpr.Opcode.Eq:
          case BinaryExpr.Opcode.Neq:
          case BinaryExpr.Opcode.Gt:
          case BinaryExpr.Opcode.Ge:
          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le:
          case BinaryExpr.Opcode.Disjoint:
          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            opBindingStrength = 0x30; fragileLeftContext = fragileRightContext = true; break;
          case BinaryExpr.Opcode.And:
            opBindingStrength = 0x20; break;
          case BinaryExpr.Opcode.Or:
            opBindingStrength = 0x21; break;
          case BinaryExpr.Opcode.Imp:
            opBindingStrength = 0x10; fragileLeftContext = true; break;
          case BinaryExpr.Opcode.Iff:
            opBindingStrength = 0x08; break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary operator
        }
        int opBS = opBindingStrength & 0xF8;
        int ctxtBS = contextBindingStrength & 0xF8;
        bool parensNeeded = opBS < ctxtBS ||
          (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

        string op = BinaryExpr.OpcodeString(e.Op);
        if (parensNeeded) { wr.Write("("); }
        if (0 <= indent && e.Op == BinaryExpr.Opcode.And) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, indent);
          wr.WriteLine(" {0}", op);
          Indent(indent);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, indent);
        } else if (0 <= indent && e.Op == BinaryExpr.Opcode.Imp) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, indent);
          wr.WriteLine(" {0}", op);
          int ind = indent + IndentAmount;
          Indent(ind);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, ind);
        } else {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, -1);
          wr.Write(" {0} ", op);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, -1);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        // determine if parens are needed
        int opBindingStrength = 0x30;
        int opBS = opBindingStrength & 0xF8;
        int ctxtBS = contextBindingStrength & 0xF8;
        bool parensNeeded = opBS < ctxtBS ||
          (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Operands[0], opBindingStrength, true, false, -1);
        for (int i = 0; i < e.Operators.Count; i++) {
          string op = BinaryExpr.OpcodeString(e.Operators[i]);
          wr.Write(" {0} ", op);
          PrintExpr(e.Operands[i+1], opBindingStrength, true, i == e.Operators.Count - 1 && (parensNeeded || isRightmost), -1);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("var ");
        string sep = "";
        foreach (var v in e.Vars) {
          wr.Write("{0}{1}", sep, v.Name);
          PrintType(": ", v.Type);
          sep = ", ";
        }
        wr.Write(" := ");
        PrintExpressionList(e.RHSs);
        wr.Write("; ");
        PrintExpression(e.Body);
        if (parensNeeded) { wr.Write(")"); }


      } else if (expr is QuantifierExpr) {
        QuantifierExpr e = (QuantifierExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write(e is ForallExpr ? "forall " : "exists ");
        PrintQuantifierDomain(e.BoundVars, e.Attributes, e.Range);
        wr.Write(" :: ");
        if (0 <= indent) {
          int ind = indent + IndentAmount;
          wr.WriteLine();
          Indent(ind);
          PrintExpression(e.Term, ind);
        } else {
          PrintExpression(e.Term);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("set ");
        string sep = "";
        foreach (BoundVar bv in e.BoundVars) {
          wr.Write("{0}{1}", sep, bv.Name);
          sep = ", ";
          PrintType(": ", bv.Type);
        }
        PrintAttributes(e.Attributes);
        wr.Write(" | ");
        PrintExpression(e.Range);
        if (!e.TermIsImplicit) {
          wr.Write(" :: ");
          PrintExpression(e.Term);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("map ");
        string sep = "";
        foreach (BoundVar bv in e.BoundVars) {
          wr.Write("{0}{1}", sep, bv.Name);
          sep = ", ";
          PrintType(": ", bv.Type);
        }
        PrintAttributes(e.Attributes);
        wr.Write(" | ");
        PrintExpression(e.Range);
        wr.Write(" :: ");
        PrintExpression(e.Term);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is WildcardExpr) {
        wr.Write("*");

      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("{0} ", e.Kind);
        PrintExpression(e.Guard);
        wr.Write("; ");
        PrintExpression(e.Body);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ITEExpr) {
        ITEExpr ite = (ITEExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("if ");
        PrintExpression(ite.Test);
        wr.Write(" then ");
        PrintExpression(ite.Thn);
        wr.Write(" else ");
        PrintExpression(ite.Els);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        // printing of parentheses is done optimally, not according to the parentheses in the given program
        PrintExpr(e.E, contextBindingStrength, fragileContext, isRightmost, indent);

      } else if (expr is IdentifierSequence) {
        var e = (IdentifierSequence)expr;
        string sep = "";
        foreach (var id in e.Tokens) {
          wr.Write("{0}{1}", sep, id.val);
          sep = ".";
        }
        if (e.Arguments != null) {
          wr.Write("(");
          PrintExpressionList(e.Arguments);
          wr.Write(")");
        }

      } else if (expr is MatchExpr) {
        Contract.Assert(false); throw new cce.UnreachableException();  // MatchExpr is an extended expression and should be printed only using PrintExtendedExpr
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    private void PrintQuantifierDomain(List<BoundVar> boundVars, Attributes attrs, Expression range) {
      Contract.Requires(boundVars != null);
      string sep = "";
      foreach (BoundVar bv in boundVars) {
        wr.Write("{0}{1}", sep, bv.Name);
        PrintType(": ", bv.Type);
        sep = ", ";
      }
      PrintAttributes(attrs);
      if (range != null) {
        wr.Write(" | ");
        PrintExpression(range);
      }
    }

    void PrintExpressionList(List<Expression> exprs) {
      Contract.Requires(exprs != null);
      string sep = "";
      foreach (Expression e in exprs) {
        Contract.Assert(e != null);
        wr.Write(sep);
        sep = ", ";
        PrintExpression(e);
      }
    }
    void PrintExpressionPairList(List<ExpressionPair> exprs) {
      Contract.Requires(exprs != null);
      string sep = "";
      foreach (ExpressionPair p in exprs) {
        Contract.Assert(p != null);
        wr.Write(sep);
        sep = ", ";
        PrintExpression(p.A);
        wr.Write(":=");
        PrintExpression(p.B);
      }
    }

    void PrintFrameExpressionList(List<FrameExpression/*!*/>/*!*/ fexprs) {
      Contract.Requires(fexprs != null);
      string sep = "";
      foreach (FrameExpression fe in fexprs) {
        Contract.Assert(fe != null);
        wr.Write(sep);
        sep = ", ";
        PrintExpression(fe.E);
        if (fe.FieldName != null) {
          wr.Write("`{0}", fe.FieldName);
        }
      }
    }
  }
}
