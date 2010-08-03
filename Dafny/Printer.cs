//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using Microsoft.Contracts;
using System.Numerics;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  class Printer {
    TextWriter! wr;
    public Printer(TextWriter! wr) {
      this.wr = wr;
    }
    
    public void PrintProgram(Program! prog) {
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
          wr.Write("module ");
          PrintAttributes(module.Attributes);
          wr.Write("{0} ", module.Name);
          if (module.Imports.Count != 0) {
            string sep = "imports ";
            foreach (string imp in module.Imports) {
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
    
    public void PrintTopLevelDecls(List<TopLevelDecl!>! classes, int indent) {
      int i = 0;
      foreach (TopLevelDecl d in classes) {
        if (d is DatatypeDecl) {
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
    
    public void PrintClass(ClassDecl! c, int indent) {      
      Indent(indent);
      PrintClassMethodHelper("class", c.Attributes, c.Name, c.TypeArgs);
      if (c is ClassRefinementDecl) {
        wr.Write(" refines ");
        wr.Write(((ClassRefinementDecl)c).RefinedClass.val);
      }
      if (c.Members.Count == 0) {
        wr.WriteLine(" { }");
      } else {
        wr.WriteLine(" {");
        PrintClass_Members(c, indent + IndentAmount);
        Indent(indent);
        wr.WriteLine("}");
      }
    }
    
    public void PrintClass_Members(ClassDecl! c, int indent)
      requires c.Members.Count != 0;
    {
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
        } else if (m is CouplingInvariant) {
          wr.WriteLine();
          PrintCouplingInvariant((CouplingInvariant)m, indent);
          state = 2;    
        } else {
          assert false;  // unexpected member
        }
      }
    }
    
    void PrintClassMethodHelper(string! kind, Attributes attrs, string! name, List<TypeParameter!>! typeArgs) {
      if (kind.Length != 0) {
        wr.Write("{0} ", kind);
      }
      PrintAttributes(attrs);
      wr.Write(name);
      if (typeArgs.Count != 0) {
        wr.Write("<");
        string sep = "";
        foreach (TypeParameter tp in typeArgs) {
          wr.Write("{0}{1}", sep, tp.Name);
          sep = ", ";
        }
        wr.Write(">");
      }
    }
    
    public void PrintDatatype(DatatypeDecl! dt, int indent) {
      Indent(indent);
      PrintClassMethodHelper("datatype", dt.Attributes, dt.Name, dt.TypeArgs);
      if (dt.Ctors.Count == 0) {
        wr.WriteLine(" { }");
      } else {
        wr.WriteLine(" {");
        int ind = indent + IndentAmount;
        foreach (DatatypeCtor ctor in dt.Ctors) {
          PrintCtor(ctor, ind);
        }
        Indent(indent);  wr.WriteLine("}");
      }
    }
    
    public void PrintAttributes(Attributes a) {
      if (a != null) {
        PrintAttributes(a.Prev);
        
        wr.Write("{ :{0}", a.Name);
        PrintAttributeArgs(a.Args);
        wr.Write(" } ");
      }
    }
    
    public void PrintAttributeArgs(List<Attributes.Argument!>! args) {
      string prefix = " ";
      foreach (Attributes.Argument arg in args) {
        wr.Write(prefix);
        prefix = ", ";
        if (arg.S != null) {
          wr.Write("\"{0}\"", arg.S);
        } else {
          assert arg.E != null;
          PrintExpression(arg.E);
        }
      }
    }
    
    public void PrintField(Field! field, int indent) {
      Indent(indent);
      if (field.IsGhost) {
        wr.Write("ghost ");
      }
      wr.Write("var ");
      PrintAttributes(field.Attributes);
      wr.Write("{0}: ", field.Name);
      PrintType(field.Type);
      wr.WriteLine(";");
    }
    
    public void PrintCouplingInvariant(CouplingInvariant! inv, int indent) {
      Indent(indent);
      wr.Write("replaces");
      string sep = " ";
      foreach (string tok in inv.Tokens()) {
        wr.Write(sep);
        wr.Write(tok);
        sep = ", ";
      }
      wr.Write(" by ");
      PrintExpression(inv.Expr);
      wr.WriteLine(";");      
    }
    
    public void PrintFunction(Function! f, int indent) {
      Indent(indent);
      string k = "function";
      if (f.IsUnlimited) { k = "unlimited " + k; }
      if (f.IsStatic) { k = "static " + k; }
      if (!f.IsGhost) { k += " method"; }
      PrintClassMethodHelper(k, f.Attributes, f.Name, f.TypeArgs);
      PrintFormals(f.Formals);
      wr.Write(": ");
      PrintType(f.ResultType);
      wr.WriteLine(f.Body == null ? ";" : "");

      int ind = indent + IndentAmount;
      PrintSpec("requires", f.Req, ind);
      PrintFrameSpecLine("reads", f.Reads, ind);
      PrintSpecLine("decreases", f.Decreases, ind);
      if (f.Body != null) {
        Indent(indent);
        wr.WriteLine("{");
        PrintExtendedExpr(f.Body, ind);
        Indent(indent);
        wr.WriteLine("}");
      }
    }
    
    public void PrintCtor(DatatypeCtor! ctor, int indent) {
      Indent(indent);
      PrintClassMethodHelper("", ctor.Attributes, ctor.Name, ctor.TypeArgs);
      if (ctor.Formals.Count != 0) {
        PrintFormals(ctor.Formals);
      }
      wr.WriteLine(";");
    }
    
    // ----------------------------- PrintMethod -----------------------------

    const int IndentAmount = 2;
    const string! BunchaSpaces = "                                ";
    void Indent(int amount)
      requires 0 <= amount;
    {
      while (0 < amount) {
        wr.Write(BunchaSpaces.Substring(0, amount));
        amount -= BunchaSpaces.Length;
      }
    }
    
    public void PrintMethod(Method! method, int indent) {      
      Indent(indent);
      string k = method is MethodRefinement ? "refines" : "method";
      if (method.IsStatic) { k = "static " + k; }
      if (method.IsGhost) { k = "ghost " + k; }
      PrintClassMethodHelper(k, method.Attributes, method.Name, method.TypeArgs);
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
      wr.WriteLine(method.Body == null ? ";" : "");

      int ind = indent + IndentAmount;      
      PrintSpec("requires", method.Req, ind);
      PrintFrameSpecLine("modifies", method.Mod, ind);
      PrintSpec("ensures", method.Ens, ind);
      PrintSpecLine("decreases", method.Decreases, ind);
      
      if (method.Body != null) {
        Indent(indent);
        PrintStatement(method.Body, indent);
        wr.WriteLine();
      }
    }
    
    void PrintFormals(List<Formal!>! ff) {
      wr.Write("(");
      string sep = "";
      foreach (Formal f in ff) {
        wr.Write(sep);
        sep = ", ";
        PrintFormal(f);
      }
      wr.Write(")");
    }
    
    void PrintFormal(Formal! f) {
      if (f.IsGhost) {
        wr.Write("ghost ");
      }
      if (!f.Name.StartsWith("#")) {
        wr.Write("{0}: ", f.Name);
      }
      PrintType(f.Type);
    }
    
    void PrintSpec(string! kind, List<Expression!>! ee, int indent) {
      foreach (Expression e in ee) {
        Indent(indent);
        wr.Write("{0} ", kind);
        PrintExpression(e);
        wr.WriteLine(";");
      }
    }

    void PrintSpecLine(string! kind, List<Expression!>! ee, int indent) {
      if (ee.Count != 0) {
        Indent(indent);
        wr.Write("{0} ", kind);
        PrintExpressionList(ee);
        wr.WriteLine(";");
      }
    }

    void PrintFrameSpecLine(string! kind, List<FrameExpression!>! ee, int indent) {
      if (ee.Count != 0) {
        Indent(indent);
        wr.Write("{0} ", kind);
        PrintFrameExpressionList(ee);
        wr.WriteLine(";");
      }
    }

    void PrintSpec(string! kind, List<MaybeFreeExpression!>! ee, int indent) {
      foreach (MaybeFreeExpression e in ee) {
        Indent(indent);
        wr.Write("{0}{1} ", e.IsFree ? "free " : "", kind);
        PrintExpression(e.E);
        wr.WriteLine(";");
      }
    }

    // ----------------------------- PrintType -----------------------------
    
    public void PrintType(Type! ty) {
      wr.Write(ty.ToString());
    }

    public void PrintType(string! prefix, Type! ty) {
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
    public void PrintStatement(Statement! stmt, int indent) {
      if (stmt is AssertStmt) {
        wr.Write("assert ");
        PrintExpression(((AssertStmt)stmt).Expr);
        wr.Write(";");
        
      } else if (stmt is AssumeStmt) {
        wr.Write("assume ");
        PrintExpression(((AssumeStmt)stmt).Expr);
        wr.Write(";");
        
      } else if (stmt is UseStmt) {
        wr.Write("use ");
        PrintExpression(((UseStmt)stmt).Expr);
        wr.Write(";");
        
      } else if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        wr.Write("print");
        PrintAttributeArgs(s.Args);
        wr.Write(";");
        
      } else if (stmt is LabelStmt) {
        wr.Write("label {0}:", ((LabelStmt)stmt).Label);
        
      } else if (stmt is BreakStmt) {
        BreakStmt s = (BreakStmt)stmt;
        if (s.TargetLabel == null) {
          wr.Write("break;");
        } else {
          wr.Write("break {0};", s.TargetLabel);
        }
        
      } else if (stmt is ReturnStmt) {
        wr.Write("return;");
        
      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        if (s.Rhs is HavocRhs) {
          wr.Write("havoc ");
          PrintExpression(s.Lhs);
        } else {
          PrintExpression(s.Lhs);
          wr.Write(" := ");
          PrintDeterminedRhs((DeterminedAssignmentRhs)s.Rhs);
        }
        wr.Write(";");
        
      } else if (stmt is VarDecl) {
        VarDecl s = (VarDecl)stmt;
        if (s.IsGhost) {
          wr.Write("ghost ");
        }
        wr.Write("var {0}", s.Name);
        if (s.OptionalType != null) {
          PrintType(": ", s.OptionalType);
        }
        if (s.Rhs != null) {
          wr.Write(" := ");
          PrintDeterminedRhs(s.Rhs);
        }
        wr.Write(";");
      
      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        wr.Write("call ");
        if (s.Lhs.Count != 0) {
          string sep = "";
          foreach (IdentifierExpr v in s.Lhs) {
            wr.Write(sep);
            PrintExpression(v);
            sep = ", ";
          }
          wr.Write(" := ");
        }
        if (!(s.Receiver is ThisExpr)) {
          PrintExpr(s.Receiver, 0x70, false, -1);
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
        while (true) {
          wr.Write("if (");
          PrintGuard(s.Guard);
          wr.Write(") ");
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
      
      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt)stmt;
        wr.Write("while (");
        PrintGuard(s.Guard);
        wr.WriteLine(")");

        int ind = indent + IndentAmount;
        PrintSpec("invariant", s.Invariants, ind);
        PrintSpecLine("decreases", s.Decreases, indent);
        Indent(indent);
        PrintStatement(s.Body, indent);
        
      } else if (stmt is ForeachStmt) {
        ForeachStmt s = (ForeachStmt)stmt;
        wr.Write("foreach ({0} in ", s.BoundVar.Name);
        PrintExpression(s.Collection);
        if (!LiteralExpr.IsTrue(s.Range)) {
          wr.Write(" | ");
          PrintExpression(s.Range);
        }
        wr.WriteLine(") {");
        int ind = indent + IndentAmount;
        foreach (PredicateStmt t in s.BodyPrefix) {
          Indent(ind);
          PrintStatement(t, ind);
          wr.WriteLine();
        }
        Indent(ind);
        PrintStatement(s.BodyAssign, ind);
        wr.WriteLine();
        Indent(indent);
        wr.Write("}");
        
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
            PrintStatement(bs, caseInd + IndentAmount);
          }
        }
        Indent(indent);
        wr.WriteLine("}");
        
      } else {
        assert false;  // unexpected statement
      }
    }
    
    void PrintDeterminedRhs(DeterminedAssignmentRhs! rhs) {
      if (rhs is ExprRhs) {
        PrintExpression(((ExprRhs)rhs).Expr);
      } else if (rhs is TypeRhs) {
        TypeRhs t = (TypeRhs)rhs;
        wr.Write("new ");
        PrintType(t.EType);
        if (t.ArraySize != null) {
          wr.Write("[");
          PrintExpression(t.ArraySize);
          wr.Write("]");
        }
      } else {
        assert false;  // unexpected RHS
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

    public void PrintExtendedExpr(Expression! expr, int indent) {
      Indent(indent);
      if (expr is ITEExpr) {
        while (true) {
          ITEExpr ite = (ITEExpr)expr;
          wr.Write("if ");
          PrintExpression(ite.Test);
          wr.WriteLine(" then");
          PrintExtendedExpr(ite.Thn, indent + IndentAmount);
          expr = ite.Els;
          if (expr is ITEExpr) {
            Indent(indent);  wr.Write("else ");
          } else {
            Indent(indent);  wr.WriteLine("else");
            Indent(indent + IndentAmount);
            PrintExpression(expr);
            wr.WriteLine();
            return;
          }
        }
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        wr.Write("match ");
        PrintExpression(me.Source);
        foreach (MatchCaseExpr mc in me.Cases) {
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
          wr.WriteLine(" =>");
          PrintExtendedExpr(mc.Body, indent + IndentAmount);
        }
      } else {
        PrintExpression(expr, indent);
        wr.WriteLine();
      }
    }
    
    public void PrintExpression(Expression! expr) {
      PrintExpr(expr, 0, false, -1);
    }
    
    /// <summary>
    /// An indent of -1 means print the entire expression on one line.
    /// </summary>
    public void PrintExpression(Expression! expr, int indent) {
      PrintExpr(expr, 0, false, indent);
    }
    
    /// <summary>
    /// An indent of -1 means print the entire expression on one line.
    /// </summary>
    void PrintExpr(Expression! expr, int contextBindingStrength, bool fragileContext, int indent)
      requires -1 <= indent;
    {
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
        wr.Write(e is SetDisplayExpr ? "{" : "[");
        PrintExpressionList(e.Elements);
        wr.Write(e is SetDisplayExpr ? "}" : "]");
        
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Obj is ImplicitThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);
        
        if (parensNeeded) { wr.Write("("); }
        if (!(e.Obj is ImplicitThisExpr)) {
          PrintExpr(e.Obj, opBindingStrength, false, -1);
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
        PrintExpr(e.Seq, 0x00, false, indent);  // BOGUS: fix me
        wr.Write("[");
        if (e.SelectOne) {
          assert e.E0 != null;
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
      
      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);
        
        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Seq, 00, false, indent);  // BOGUS: fix me
        wr.Write("[");
        PrintExpression(e.Index);
        wr.Write(" := ");
        PrintExpression(e.Value);
        wr.Write("]");
        if (parensNeeded) { wr.Write(")"); }
      
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Receiver is ThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);
        
        if (parensNeeded) { wr.Write("("); }
        if (!(e.Receiver is ThisExpr)) {
          PrintExpr(e.Receiver, opBindingStrength, false, -1);
          wr.Write(".");
        }
        wr.Write(e.Name);
        wr.Write("(");
        PrintExpressionList(e.Args);
        wr.Write(")");
        if (parensNeeded) { wr.Write(")"); }
      
      } else if (expr is OldExpr) {
        wr.Write("old(");
        PrintExpression(((OldExpr)expr).E);
        wr.Write(")");
      
      } else if (expr is FreshExpr) {
        wr.Write("fresh(");
        PrintExpression(((FreshExpr)expr).E);
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
            case UnaryExpr.Opcode.Not:
              op = "!";  opBindingStrength = 0x60;  break;
            default:
              assert false;  // unexpected unary opcode
          }
          bool parensNeeded = opBindingStrength < contextBindingStrength ||
            (fragileContext && opBindingStrength == contextBindingStrength);

          if (parensNeeded) { wr.Write("("); }
          wr.Write(op);
          PrintExpr(e.E, opBindingStrength, false, -1);
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
            assert false;  // unexpected binary operator
        }
        int opBS = opBindingStrength & 0xF8;
        int ctxtBS = contextBindingStrength & 0xF8;
        bool parensNeeded = opBS < ctxtBS ||
          (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

        string op = BinaryExpr.OpcodeString(e.Op);
        if (parensNeeded) { wr.Write("("); }
        if (0 <= indent && e.Op == BinaryExpr.Opcode.And) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, indent);
          wr.WriteLine(" {0}", op);
          Indent(indent);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, indent);
        } else if (0 <= indent && e.Op == BinaryExpr.Opcode.Imp) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, indent);
          wr.WriteLine(" {0}", op);
          int ind = indent + IndentAmount;
          Indent(ind);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, ind);
        } else {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, -1);
          wr.Write(" {0} ", op);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, -1);
        }
        if (parensNeeded) { wr.Write(")"); }
      
      } else if (expr is QuantifierExpr) {
        QuantifierExpr e = (QuantifierExpr)expr;
        wr.Write(e is ForallExpr ? "(forall " : "(exists ");
        string sep = "";
        foreach (BoundVar bv in e.BoundVars) {
          wr.Write("{0}{1}", sep, bv.Name);
          sep = ", ";
          PrintType(": ", bv.Type);
        }
        wr.Write(" :: ");
        PrintAttributes(e.Attributes);
        PrintTriggers(e.Trigs);
        if (0 <= indent) {
          int ind = indent + IndentAmount;
          wr.WriteLine();
          Indent(ind);
          PrintExpression(e.Body, ind);
        } else {
          PrintExpression(e.Body);
        }
        wr.Write(")");
        
      } else if (expr is WildcardExpr) {
        wr.Write("*");
        
      } else if (expr is ITEExpr) {
        ITEExpr ite = (ITEExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x00;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);
        
        if (parensNeeded) { wr.Write("("); }
        wr.Write("if ");
        PrintExpression(ite.Test);
        wr.Write(" then ");
        PrintExpression(ite.Thn);
        wr.Write(" else ");
        PrintExpr(ite.Els, opBindingStrength, false, indent);
        if (parensNeeded) { wr.Write(")"); }
        
      } else if (expr is MatchExpr) {
        assert false;  // MatchExpr is an extended expression and should be printed only using PrintExtendedExpr
      } else {
        assert false;  // unexpected expression
      }
    }
    
    void PrintTriggers(Triggers trigs) {
      if (trigs != null) {
        PrintTriggers(trigs.Prev);
        
        wr.Write("{ ");
        PrintExpressionList(trigs.Terms);
        wr.Write(" } ");
      }
    }
    
    void PrintExpressionList(List<Expression!>! exprs) {
      string sep = "";
      foreach (Expression e in exprs) {
        wr.Write(sep);
        sep = ", ";
        PrintExpression(e);
      }
    }
    
    void PrintFrameExpressionList(List<FrameExpression!>! fexprs) {
      string sep = "";
      foreach (FrameExpression fe in fexprs) {
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
