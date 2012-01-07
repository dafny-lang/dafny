//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
// This file contains the transformations that are applied to a module that is
// constructed as a refinement of another.  It is invoked during program resolution,
// so the transformation is done syntactically.  Upon return from the RefinementTransformer,
// the caller is expected to resolve the resulting module.
//
// As for now (and perhaps this is always the right thing to do), attributes do
// not survive the transformation.
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using IToken = Microsoft.Boogie.IToken;

namespace Microsoft.Dafny {
  public class RefinementToken : IToken
  {
    IToken tok;
    public RefinementToken(IToken tok)
    {
      this.tok = tok;
    }

    public int kind {
      get { return tok.kind; }
      set { throw new NotSupportedException(); }
    }
    public string filename {
      get { return tok.filename; }
      set { throw new NotSupportedException(); }
    }
    public int pos {
      get { return tok.pos; }
      set { throw new NotSupportedException(); }
    }
    public int col {
      get { return tok.col; }
      set { throw new NotSupportedException(); }
    }
    public int line {
      get { return tok.line; }
      set { throw new NotSupportedException(); }
    }
    public string/*!*/ val {
      get { return tok.val; }
      set { throw new NotSupportedException(); }
    }
    public bool IsValid {
      get { return tok.IsValid; }
    }
  }

  public class RefinementTransformer
  {
    ResolutionErrorReporter reporter;
    public RefinementTransformer(ResolutionErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }

    public void Construct(ModuleDecl m) {
      Contract.Requires(m != null);
      Contract.Requires(m.RefinementBase != null);

      var prev = m.RefinementBase;

      // Include the imports of the base.  Note, prev is itself NOT added as an import
      // of m; instead, the contents from prev is merged directly into m.
      // (Here, we change the import declarations.  But edges for these imports will
      // not be added to the importGraph of the calling resolver.  However, the refines
      // clause gave rise to an edge in the importGraph, so the transitive import edges
      // are represented in the importGraph.)
      foreach (var im in prev.Imports) {
        if (!m.ImportNames.Contains(im.Name)) {
          m.ImportNames.Add(im.Name);
          m.Imports.Add(im);
        }
      }

      // Create a simple name-to-decl dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < m.TopLevelDecls.Count; i++) {
        var d = m.TopLevelDecls[i];
        if (!declaredNames.ContainsKey(d.Name)) {
          declaredNames.Add(d.Name, i);
        }
      }

      // Merge the declarations of prev into the declarations of m
      foreach (var d in prev.TopLevelDecls) {
        int index;
        if (!declaredNames.TryGetValue(d.Name, out index)) {
          m.TopLevelDecls.Add(CloneDeclaration(d, m));
        } else {
          var nw = m.TopLevelDecls[index];
          if (d is ArbitraryTypeDecl) {
            // this is allowed to be refined by any type declaration, so just keep the new one
          } else if (nw is ArbitraryTypeDecl) {
            reporter.Error(nw, "an arbitrary type declaration ({0}) in a refining module cannot replace a more specific type declaration in the refinement base", nw.Name);
          } else if (nw is DatatypeDecl) {
            if (d is ClassDecl) {
              reporter.Error(nw, "a datatype declaration ({0}) in a refining module cannot replace a class declaration in the refinement base", nw.Name);
            } else {
              m.TopLevelDecls[index] = MergeDatatype((DatatypeDecl)nw, (DatatypeDecl)d);
            }
          } else {
            Contract.Assert(nw is ClassDecl);
            if (d is DatatypeDecl) {
              reporter.Error(nw, "a class declaration ({0}) in a refining module cannot replace a datatype declaration in the refinement base", nw.Name);
            } else {
              m.TopLevelDecls[index] = MergeClass((ClassDecl)nw, (ClassDecl)d);
            }
          }
        }
      }
    }

    IToken Tok(IToken tok) {
      return new RefinementToken(tok);
    }

    // -------------------------------------------------- Cloning ---------------------------------------------------------------

    TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDecl m) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      if (d is ArbitraryTypeDecl) {
        var dd = (ArbitraryTypeDecl)d;
        return new ArbitraryTypeDecl(Tok(dd.tok), dd.Name, m, null);
      } else if (d is DatatypeDecl) {
        var dd = (DatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new DatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, null);
        return dt;
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        var cl = new ClassDecl(Tok(dd.tok), dd.Name, m, tps, mm, null);
        return cl;
      } else {
        Contract.Assert(false);  // unexpected declaration
        return null;  // to please compiler
      }
    }

    DatatypeCtor CloneCtor(DatatypeCtor ct) {
      return new DatatypeCtor(Tok(ct.tok), ct.Name, ct.Formals.ConvertAll(CloneFormal), null);
    }

    TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(Tok(tp.tok), tp.Name);
    }

    MemberDecl CloneMember(MemberDecl member) {
      if (member is Field) {
        var f = (Field)member;
        return new Field(Tok(f.tok), f.Name, f.IsGhost, f.IsMutable, CloneType(f.Type), null);
      } else if (member is Function) {
        var f = (Function)member;
        var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
        return new Function(Tok(f.tok), f.Name, f.IsStatic, f.IsGhost, f.IsUnlimited, tps, f.Formals.ConvertAll(CloneFormal), CloneType(f.ResultType),
          f.Req.ConvertAll(CloneExpr), f.Reads.ConvertAll(CloneFrameExpr), f.Ens.ConvertAll(CloneExpr), CloneSpecExpr(f.Decreases), CloneExpr(f.Body), null);
      } else {
        var m = (Method)member;
        var tps = m.TypeArgs.ConvertAll(CloneTypeParam);
        return new Method(Tok(m.tok), m.Name, m.IsStatic, m.IsGhost, tps, m.Ins.ConvertAll(CloneFormal), m.Outs.ConvertAll(CloneFormal),
          m.Req.ConvertAll(CloneMayBeFreeExpr), CloneSpecFrameExpr(m.Mod), m.Ens.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(m.Decreases), CloneBlockStmt(m.Body), null);
      }
    }

    Type CloneType(Type t) {
      if (t is BasicType) {
        return t;
      } else if (t is SetType) {
        var tt = (SetType)t;
        return new SetType(tt.Arg);
      } else if (t is SeqType) {
        var tt = (SeqType)t;
        return new SeqType(tt.Arg);
      } else if (t is MultiSetType) {
        var tt = (MultiSetType)t;
        return new MultiSetType(tt.Arg);
      } else if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
        return new UserDefinedType(Tok(tt.tok), tt.Name, tt.TypeArgs.ConvertAll(CloneType));
      } else if (t is InferredTypeProxy) {
        return new InferredTypeProxy();
      } else {
        Contract.Assert(false);  // unexpected type (e.g., no other type proxies are expected at this time)
        return null;  // to please compiler
      }
    }

    Formal CloneFormal(Formal formal) {
      return new Formal(Tok(formal.tok), formal.Name, formal.Type, formal.InParam, formal.IsGhost);
    }

    BoundVar CloneBoundVar(BoundVar bv) {
      return new BoundVar(Tok(bv.tok), bv.Name, bv.Type);
    }

    Specification<Expression> CloneSpecExpr(Specification<Expression> spec) {
      var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(CloneExpr);
      return new Specification<Expression>(ee, null);
    }

    Specification<FrameExpression> CloneSpecFrameExpr(Specification<FrameExpression> frame) {
      var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(CloneFrameExpr);
      return new Specification<FrameExpression>(ee, null);
    }

    FrameExpression CloneFrameExpr(FrameExpression frame) {
      return new FrameExpression(CloneExpr(frame.E), frame.FieldName);
    }

    Attributes.Argument CloneAttrArg(Attributes.Argument aa) {
      if (aa.E != null) {
        return new Attributes.Argument(Tok(aa.Tok), CloneExpr(aa.E));
      } else {
        return new Attributes.Argument(Tok(aa.Tok), aa.S);
      }
    }

    MaybeFreeExpression CloneMayBeFreeExpr(MaybeFreeExpression expr) {
      return new MaybeFreeExpression(CloneExpr(expr.E), expr.IsFree);
    }

    Expression CloneExpr(Expression expr) {
#if SOON
      if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e.Value == null) {
          return new LiteralExpr(Tok(e.tok));
        } else if (e.Value is bool) {
          return new LiteralExpr(Tok(e.tok), (bool)e.Value);
        } else {
          return new LiteralExpr(Tok(e.tok), (BigInteger)e.Value);
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
        FunctionCallExpr e = (FunctionCallExpr)expr;
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
        wr.Write("(");
        PrintExpressionList(e.Args);
        wr.Write(")");
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
#else
      return expr;  // TODO
#endif
    }

    AssignmentRhs CloneRHS(AssignmentRhs rhs) {
      if (rhs is ExprRhs) {
        var r = (ExprRhs)rhs;
        return new ExprRhs(r.Expr);
      } else if (rhs is HavocRhs) {
        return new HavocRhs(Tok(rhs.Tok));
      } else {
        var r = (TypeRhs)rhs;
        if (r.ArrayDimensions != null) {
          return new TypeRhs(Tok(r.Tok), r.EType, r.ArrayDimensions.ConvertAll(CloneExpr));
        } else if (r.InitCall != null) {
          return new TypeRhs(Tok(r.Tok), r.EType, (CallStmt)CloneStmt(r.InitCall));
        } else {
          return new TypeRhs(Tok(r.Tok), r.EType);
        }
      }
    }

    BlockStmt CloneBlockStmt(BlockStmt stmt) {
      if (stmt == null) {
        return null;
      } else {
        return new BlockStmt(Tok(stmt.Tok), stmt.Body.ConvertAll(CloneStmt));
      }
    }

    Statement CloneStmt(Statement stmt) {
      if (stmt == null) {
        return null;
      }

      Statement r;
      if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(Tok(s.Tok), s.Expr);

      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(Tok(s.Tok), s.Expr);

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        r = new PrintStmt(Tok(s.Tok), s.Args.ConvertAll(CloneAttrArg));

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          r = new BreakStmt(Tok(s.Tok), s.TargetLabel);
        } else {
          r = new BreakStmt(Tok(s.Tok), s.BreakCount);
        }

      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        r = new ReturnStmt(Tok(s.Tok), s.rhss == null ? null : s.rhss.ConvertAll(CloneRHS));

      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        r = new AssignStmt(Tok(s.Tok), CloneExpr(s.Lhs), CloneRHS(s.Rhs));

      } else if (stmt is VarDecl) {
        var s = (VarDecl)stmt;
        r = new VarDecl(Tok(s.Tok), s.Name, s.OptionalType, s.IsGhost);

      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        r = new CallStmt(Tok(s.Tok), s.Lhs.ConvertAll(CloneExpr), CloneExpr(s.Receiver), s.MethodName, s.Args.ConvertAll(CloneExpr));

      } else if (stmt is BlockStmt) {
        r = CloneBlockStmt((BlockStmt)stmt);

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        r = new IfStmt(Tok(s.Tok), CloneExpr(s.Guard), CloneStmt(s.Thn), CloneStmt(s.Els));

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(Tok(s.Tok), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(Tok(s.Tok), CloneExpr(s.Guard), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), CloneStmt(s.Body));

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(Tok(s.Tok), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is ParallelStmt) {
        var s = (ParallelStmt)stmt;
        r = new ParallelStmt(Tok(s.Tok), s.BoundVars.ConvertAll(CloneBoundVar), null, CloneExpr(s.Range), s.Ens.ConvertAll(CloneMayBeFreeExpr), CloneStmt(s.Body));

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        r = new MatchStmt(Tok(s.Tok), CloneExpr(s.Source), s.Cases.ConvertAll(c => new MatchCaseStmt(Tok(c.tok), c.Id, c.Arguments.ConvertAll(CloneBoundVar), c.Body.ConvertAll(CloneStmt))));

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        r = new UpdateStmt(Tok(s.Tok), s.Lhss.ConvertAll(CloneExpr), s.Rhss.ConvertAll(CloneRHS), s.CanMutateKnownState);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        r = new VarDeclStmt(Tok(s.Tok), s.Lhss.ConvertAll(c => (VarDecl)CloneStmt(c)), (UpdateStmt)CloneStmt(s.Update));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }

      // add labels to the cloned statement
      AddStmtLabels(r, stmt.Labels);

      return r;
    }

    void AddStmtLabels(Statement s, LabelNode node) {
      if (node != null) {
        AddStmtLabels(s, node.Next);
        s.Labels = new LabelNode(Tok(node.Tok), node.Label, s.Labels);
      }
    }

    GuardedAlternative CloneGuardedAlternative(GuardedAlternative alt) {
      return new GuardedAlternative(Tok(alt.Tok), CloneExpr(alt.Guard), alt.Body.ConvertAll(CloneStmt));
    }

    // -------------------------------------------------- Merging ---------------------------------------------------------------

    DatatypeDecl MergeDatatype(DatatypeDecl nw, DatatypeDecl prev) {
      // TODO
      return nw;
    }

    ClassDecl MergeClass(ClassDecl nw, ClassDecl prev) {
      // TODO
      return nw;
    }
  }
}
