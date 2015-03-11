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
using System.Linq;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Printer {
    TextWriter wr;
    DafnyOptions.PrintModes printMode;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(wr!=null);
    }

    public Printer(TextWriter wr, DafnyOptions.PrintModes printMode = DafnyOptions.PrintModes.Everything) {
      Contract.Requires(wr != null);
      this.wr = wr;
      this.printMode = printMode;
    }

    public static string ExprToString(Expression expr)
    {
      Contract.Requires(expr != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintExpression(expr, false);
        return wr.ToString();
      }
    }

    public static string GuardToString(Expression expr) {
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintGuard(expr);
        return wr.ToString();
      }
    }

    public static string ExtendedExprToString(Expression expr) {
      Contract.Requires(expr != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintExtendedExpr(expr, 0, true, false);
        return wr.ToString();
      }
    }

    public static string FrameExprListToString(List<FrameExpression> fexprs) {
      Contract.Requires(fexprs != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintFrameExpressionList(fexprs);
        return wr.ToString();
      }
    }

    public static string StatementToString(Statement stmt) {
      Contract.Requires(stmt != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintStatement(stmt, 0);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string IteratorClassToString(IteratorDecl iter) {
      Contract.Requires(iter != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintIteratorClass(iter, 0, null);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string IteratorSignatureToString(IteratorDecl iter) {
      Contract.Requires(iter != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintIteratorSignature(iter, 0);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string FunctionSignatureToString(Function f) {
      Contract.Requires(f != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintFunction(f, 0, true);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string MethodSignatureToString(Method m) {
      Contract.Requires(m != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr);
        pr.PrintMethod(m, 0, true);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string ToStringWithoutNewline(System.IO.StringWriter wr) {
      Contract.Requires(wr != null);
      var sb = wr.GetStringBuilder();
      var len = sb.Length;
      while (len > 0 && (sb[len - 1] == '\n' || sb[len - 1] == '\r')) {
        len--;
      }
      return sb.ToString(0, len);
    }

    public void PrintProgram(Program prog) {
      Contract.Requires(prog != null);
      if (Bpl.CommandLineOptions.Clo.ShowEnv != Bpl.CommandLineOptions.ShowEnvironment.Never) {
        wr.WriteLine("// " + Bpl.CommandLineOptions.Clo.Version);
        wr.WriteLine("// " + Bpl.CommandLineOptions.Clo.Environment);
      }
      wr.WriteLine("// {0}", prog.Name);
      if (DafnyOptions.O.DafnyPrintResolvedFile != null) {
        wr.WriteLine();
        wr.WriteLine("/*");
        PrintModuleDefinition(prog.BuiltIns.SystemModule, 0, Path.GetFullPath(DafnyOptions.O.DafnyPrintResolvedFile));
        wr.WriteLine("*/");
      }
      wr.WriteLine();
      PrintCallGraph(prog.DefaultModuleDef, 0);
      PrintTopLevelDecls(prog.DefaultModuleDef.TopLevelDecls, 0, Path.GetFullPath(prog.Name));
      wr.Flush();
    }

    public void PrintCallGraph(ModuleDefinition module, int indent) {
      Contract.Requires(module != null);
      Contract.Requires(0 <= indent);
      if (DafnyOptions.O.DafnyPrintResolvedFile != null) {
        // print call graph
        Indent(indent); wr.WriteLine("/* CALL GRAPH for module {0}:", module.Name);
        var SCCs = module.CallGraph.TopologicallySortedComponents();
        SCCs.Reverse();
        foreach (var clbl in SCCs) {
          Indent(indent); wr.WriteLine(" * SCC at height {0}:", module.CallGraph.GetSCCRepresentativeId(clbl));
          var r = module.CallGraph.GetSCC(clbl);
          foreach (var m in r) {
            Indent(indent); wr.WriteLine(" *   {0}", m.NameRelativeToModule);
          }
        }
        Indent(indent); wr.WriteLine(" */");
      }
    }

    public void PrintTopLevelDecls(List<TopLevelDecl> decls, int indent, string fileBeingPrinted) {
      Contract.Requires(decls!= null);
      int i = 0;
      foreach (TopLevelDecl d in decls) {
        Contract.Assert(d != null);
        if (PrintModeSkipGeneral(d.tok, fileBeingPrinted)) { continue; }
        if (d is OpaqueTypeDecl) {
          var at = (OpaqueTypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("type", at.Attributes, at.Name, new List<TypeParameter>());
          wr.Write(EqualitySupportSuffix(at.EqualitySupport));
          wr.WriteLine();
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("newtype", dd.Attributes, dd.Name, new List<TypeParameter>());
          wr.Write(" = ");
          if (dd.Var == null) {
            PrintType(dd.BaseType);
          } else {
            wr.Write(dd.Var.DisplayName);
            if (!(dd.Var.Type is TypeProxy) || DafnyOptions.O.DafnyPrintResolvedFile != null) {
              wr.Write(": ");
              PrintType(dd.BaseType);
            }
            wr.Write(" | ");
            PrintExpression(dd.Constraint, true);
          }
          wr.WriteLine();
        } else if (d is TypeSynonymDecl) {
          var syn = (TypeSynonymDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("type", syn.Attributes, syn.Name, syn.TypeArgs);
          wr.Write(" = ");
          PrintType(syn.Rhs);
          wr.WriteLine();
        } else if (d is DatatypeDecl) {
          if (i++ != 0) { wr.WriteLine(); }
          PrintDatatype((DatatypeDecl)d, indent);
        } else if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          PrintIteratorSignature(iter, indent);

          if (iter.Body != null) {
            Indent(indent);
            PrintStatement(iter.Body, indent);
            wr.WriteLine();
          }

          if (DafnyOptions.O.DafnyPrintResolvedFile != null) {
            // also print the members that were created as part of the interpretation of the iterator
            Contract.Assert(iter.Members.Count != 0);  // filled in during resolution
            wr.WriteLine("/*---------- iterator members ----------");
            PrintIteratorClass(iter, indent, fileBeingPrinted);
            wr.WriteLine("---------- iterator members ----------*/");
          }

        } else if (d is ClassDecl) {
          ClassDecl cl = (ClassDecl)d;
          if (!cl.IsDefaultClass) {
            if (i++ != 0) { wr.WriteLine(); }
            PrintClass(cl, indent, fileBeingPrinted);
          } else if (cl.Members.Count == 0) {
            // print nothing
          } else {
            if (i++ != 0) { wr.WriteLine(); }
            PrintMembers(cl.Members, indent, fileBeingPrinted);
          }

        } else if (d is ModuleDecl) {
          wr.WriteLine();
          Indent(indent);
          if (d is LiteralModuleDecl) {
            ModuleDefinition module = ((LiteralModuleDecl)d).ModuleDef;
            PrintModuleDefinition(module, indent, fileBeingPrinted);
          } else if (d is AliasModuleDecl) {
            wr.Write("import"); if (((AliasModuleDecl)d).Opened) wr.Write(" opened");
            wr.Write(" {0} ", ((AliasModuleDecl)d).Name);
            wr.WriteLine("= {0}", Util.Comma(".", ((AliasModuleDecl)d).Path, id => id.val));
          } else if (d is ModuleFacadeDecl) {
            wr.Write("import"); if (((ModuleFacadeDecl)d).Opened) wr.Write(" opened");
            wr.Write(" {0} ", ((ModuleFacadeDecl)d).Name);
            wr.WriteLine("as {0}", Util.Comma(".", ((ModuleFacadeDecl)d).Path, id => id.val));
          }

        } else {
          Contract.Assert(false);  // unexpected TopLevelDecl
        }
      }
    }

    void PrintModuleDefinition(ModuleDefinition module, int indent, string fileBeingPrinted) {
      Contract.Requires(module != null);
      Contract.Requires(0 <= indent);
      if (module.IsAbstract) {
        wr.Write("abstract ");
      }
      wr.Write("module");
      PrintAttributes(module.Attributes);
      wr.Write(" {0} ", module.Name);
      if (module.RefinementBaseName != null) {
        wr.Write("refines {0} ", Util.Comma(".", module.RefinementBaseName, id => id.val));
      }
      if (module.TopLevelDecls.Count == 0) {
        wr.WriteLine("{ }");
      } else {
        wr.WriteLine("{");
        PrintCallGraph(module, indent + IndentAmount);
        PrintTopLevelDecls(module.TopLevelDecls, indent + IndentAmount, fileBeingPrinted);
        Indent(indent);
        wr.WriteLine("}");
      }
    }

    void PrintIteratorSignature(IteratorDecl iter, int indent) {
      Indent(indent);
      PrintClassMethodHelper("iterator", iter.Attributes, iter.Name, iter.TypeArgs);
      if (iter.SignatureIsOmitted) {
        wr.WriteLine(" ...");
      } else {
        PrintFormals(iter.Ins);
        if (iter.Outs.Count != 0) {
          if (iter.Ins.Count + iter.Outs.Count <= 3) {
            wr.Write(" yields ");
          } else {
            wr.WriteLine();
            Indent(indent + 2 * IndentAmount);
            wr.Write("yields ");
          }
          PrintFormals(iter.Outs);
        }
        wr.WriteLine();
      }

      int ind = indent + IndentAmount;
      PrintSpec("requires", iter.Requires, ind);
      if (iter.Reads.Expressions != null) {
        PrintFrameSpecLine("reads", iter.Reads.Expressions, ind, iter.Reads.HasAttributes() ? iter.Reads.Attributes : null);
      }
      if (iter.Modifies.Expressions != null) {
        PrintFrameSpecLine("modifies", iter.Modifies.Expressions, ind, iter.Modifies.HasAttributes() ? iter.Modifies.Attributes : null);
      }
      PrintSpec("yield requires", iter.YieldRequires, ind);
      PrintSpec("yield ensures", iter.YieldEnsures, ind);
      PrintSpec("ensures", iter.Ensures, ind);
      PrintDecreasesSpec(iter.Decreases, ind);
    }

    private void PrintIteratorClass(IteratorDecl iter, int indent, string fileBeingPrinted) {
      PrintClassMethodHelper("class", null, iter.Name, iter.TypeArgs);
      wr.WriteLine(" {");
      PrintMembers(iter.Members, indent + IndentAmount, fileBeingPrinted);
      Indent(indent); wr.WriteLine("}");
    }

    public void PrintClass(ClassDecl c, int indent, string fileBeingPrinted) {
      Contract.Requires(c != null);
      Indent(indent);
      PrintClassMethodHelper((c is TraitDecl) ? "trait" : "class", c.Attributes, c.Name, c.TypeArgs);
      if (c.TraitsStr!=string.Empty) {
          wr.Write(" extends {0}", c.TraitsStr);
      }
      if (c.Members.Count == 0) {
        wr.WriteLine(" { }");
      } else {
        wr.WriteLine(" {");
        PrintMembers(c.Members, indent + IndentAmount, fileBeingPrinted);
        Indent(indent);
        wr.WriteLine("}");
      }
    }

    public void PrintMembers(List<MemberDecl> members, int indent, string fileBeingPrinted)
    {
      Contract.Requires(members != null);

      int state = 0;  // 0 - no members yet; 1 - previous member was a field; 2 - previous member was non-field
      foreach (MemberDecl m in members) {
        if (PrintModeSkipGeneral(m.tok, fileBeingPrinted)) { continue; }
        if (m is Method) {
          if (state != 0) { wr.WriteLine(); }
          PrintMethod((Method)m, indent, false);
          var com = m as CoLemma;
          if (com != null && com.PrefixLemma != null) {
            Indent(indent); wr.WriteLine("/***");
            PrintMethod(com.PrefixLemma, indent, false);
            Indent(indent); wr.WriteLine("***/");
          }
          state = 2;
        } else if (m is Field) {
          if (state == 2) { wr.WriteLine(); }
          PrintField((Field)m, indent);
          state = 1;
        } else if (m is Function) {
          if (state != 0) { wr.WriteLine(); }
          PrintFunction((Function)m, indent, false);
          var cop = m as CoPredicate;
          if (cop != null && cop.PrefixPredicate != null) {
            Indent(indent); wr.WriteLine("/***");
            PrintFunction(cop.PrefixPredicate, indent, false);
            Indent(indent); wr.WriteLine("***/");
          }
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
      PrintTypeParams(typeArgs);
    }

    private void PrintTypeParams(List<TypeParameter> typeArgs) {
      Contract.Requires(typeArgs != null);
      if (typeArgs.Count != 0) {
        wr.Write("<" +
                 Util.Comma(", ", typeArgs,
                   tp => tp.Name + EqualitySupportSuffix(tp.EqualitySupport))
                 + ">");
      }
    }

    private void PrintTypeInstantiation(List<Type> typeArgs) {
      Contract.Requires(typeArgs == null || typeArgs.Count != 0);
      if (typeArgs != null) {
        wr.Write("<{0}>", Util.Comma(",", typeArgs, ty => ty.ToString()));
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
      wr.WriteLine();
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
          PrintAttributeArgs(a.Args, false);
        }
        wr.Write("}");
      }
    }

    public void PrintAttributeArgs(List<Expression> args, bool isFollowedBySemicolon) {
      Contract.Requires(args != null);
      string prefix = " ";
      foreach (var arg in args) {
        Contract.Assert(arg != null);
        wr.Write(prefix);
        prefix = ", ";
        PrintExpression(arg, isFollowedBySemicolon);
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
      if (field.IsUserMutable) {
        // nothing more to say
      } else if (field.IsMutable) {
        wr.Write("  // non-assignable");
      } else {
        wr.Write("  // immutable");
      }
      wr.WriteLine();
    }

    public void PrintFunction(Function f, int indent, bool printSignatureOnly) {
      Contract.Requires(f != null);

      if (PrintModeSkipFunctionOrMethod(f.IsGhost, f.Attributes, f.Name)) { return; }
      var isPredicate = f is Predicate || f is PrefixPredicate;
      Indent(indent);
      string k = isPredicate ? "predicate" : f is CoPredicate ? "copredicate" : "function";
      if (f.IsProtected) { k = "protected " + k; }
      if (f.HasStaticKeyword) { k = "static " + k; }
      if (!f.IsGhost) { k += " method"; }
      PrintClassMethodHelper(k, f.Attributes, f.Name, f.TypeArgs);
      if (f.SignatureIsOmitted) {
        wr.WriteLine(" ...");
      } else {
        PrintFormals(f.Formals, f.Name);
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
      if (f.Body != null && !printSignatureOnly) {
        Indent(indent);
        wr.WriteLine("{");
        PrintExtendedExpr(f.Body, ind, true, false);
        Indent(indent);
        wr.WriteLine("}");
      }
    }

    // ----------------------------- PrintMethod -----------------------------

    const int IndentAmount = 2; // The amount of indent for each new scope
    const string BunchaSpaces = "                                ";
    void Indent(int amount)
    {
      Contract.Requires(0 <= amount);

      while (0 < amount) {
        wr.Write(BunchaSpaces.Substring(0, amount));
        amount -= BunchaSpaces.Length;
      }
    }

    private bool PrintModeSkipFunctionOrMethod(bool IsGhost, Attributes attributes, string name)
    {
      if (printMode == DafnyOptions.PrintModes.NoGhost && IsGhost)
          { return true; }
      if (printMode == DafnyOptions.PrintModes.NoIncludes || printMode == DafnyOptions.PrintModes.NoGhost)
      {
          bool verify = true;
          if (Attributes.ContainsBool(attributes, "verify", ref verify) && !verify)
          { return true; }
          if (name.Contains("INTERNAL") || name.StartsWith("reveal_"))
          { return true; }
      }
      return false;
    }

    private bool PrintModeSkipGeneral(Bpl.IToken tok, string fileBeingPrinted)
    {
        return (printMode == DafnyOptions.PrintModes.NoIncludes || printMode == DafnyOptions.PrintModes.NoGhost)
               && (tok.filename != null && fileBeingPrinted != null && Path.GetFullPath(tok.filename) != fileBeingPrinted);
    }

    public void PrintMethod(Method method, int indent, bool printSignatureOnly) {
      Contract.Requires(method != null);

      if (PrintModeSkipFunctionOrMethod(method.IsGhost, method.Attributes, method.Name)) { return; }
      Indent(indent);
      string k = method is Constructor ? "constructor" : method is CoLemma ? "colemma" : method is Lemma ? "lemma" : "method";
      if (method.HasStaticKeyword) { k = "static " + k; }
      if (method.IsGhost && !(method is Lemma) && !(method is CoLemma)) { k = "ghost " + k; }
      string nm = method is Constructor && !((Constructor)method).HasName ? "" : method.Name;
      PrintClassMethodHelper(k, method.Attributes, nm, method.TypeArgs);
      if (method.SignatureIsOmitted) {
        wr.WriteLine(" ...");
      } else {
        PrintFormals(method.Ins, method.Name);
        if (method.Outs.Count != 0) {
          if (method.Ins.Count + method.Outs.Count <= 3) {
            wr.Write(" returns ");
          } else {
            wr.WriteLine();
            Indent(indent + 2 * IndentAmount);
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

      if (method.Body != null && !printSignatureOnly) {
        Indent(indent);
        PrintStatement(method.Body, indent);
        wr.WriteLine();
      }
    }

    internal void PrintFormals(List<Formal> ff, string name = null) {
      Contract.Requires(ff != null);
      if (name != null && name.EndsWith("#")) {
        wr.Write("[");
        PrintFormal(ff[0]);
        wr.Write("]");
        ff = new List<Formal>(ff.Skip(1));
      }
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
        wr.Write("{0}: ", f.DisplayName);
      }
      PrintType(f.Type);
    }

    internal void PrintSpec(string kind, List<Expression> ee, int indent) {
      Contract.Requires(kind != null);
      Contract.Requires(ee != null);
      foreach (Expression e in ee) {
        Contract.Assert(e != null);
        Indent(indent);
        wr.Write("{0} ", kind);
        PrintExpression(e, true);
        wr.WriteLine();
      }
    }

    internal void PrintDecreasesSpec(Specification<Expression> decs, int indent, bool newLine = true) {
      Contract.Requires(decs != null);
      if (printMode == DafnyOptions.PrintModes.NoGhost) { return; }
      if (decs.Expressions != null && decs.Expressions.Count != 0) {
        Indent(indent);
        wr.Write("decreases");
        if (decs.HasAttributes())
        {
          PrintAttributes(decs.Attributes);
        }
        wr.Write(" ");
        PrintExpressionList(decs.Expressions, true);
        if (newLine) {
          wr.WriteLine();
        } else {
          wr.Write(" ");
        }
      }
    }

    internal void PrintFrameSpecLine(string kind, List<FrameExpression/*!*/> ee, int indent, Attributes attrs, bool newLine = true) {
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
        if (newLine) {
          wr.WriteLine();
        } else {
          wr.Write(" ");
        }
      }
    }

    internal void PrintSpec(string kind, List<MaybeFreeExpression> ee, int indent, bool newLine = true) {
      Contract.Requires(kind != null);
      Contract.Requires(ee != null);
      if (printMode == DafnyOptions.PrintModes.NoGhost) { return; }
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
        PrintExpression(e.E, true);
        if (newLine) {
          wr.WriteLine();
        } else {
          wr.Write(" ");
        }
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

    string EqualitySupportSuffix(TypeParameter.EqualitySupportValue es) {
      if (es == TypeParameter.EqualitySupportValue.Required ||
        (es == TypeParameter.EqualitySupportValue.InferredRequired && DafnyOptions.O.DafnyPrintResolvedFile != null)) {
        return "(==)";
      } else {
        return "";
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

      if (stmt.IsGhost && printMode == DafnyOptions.PrintModes.NoGhost) { return; }
      for (LList<Label> label = stmt.Labels; label != null; label = label.Next) {
        if (label.Data.Name != null) {
          wr.WriteLine("label {0}:", label.Data.Name);
          Indent(indent);
        }
      }

      if (stmt is PredicateStmt) {
        if (printMode == DafnyOptions.PrintModes.NoGhost) { return; }
        Expression expr = ((PredicateStmt)stmt).Expr;
        wr.Write(stmt is AssertStmt ? "assert" : "assume");
        if (stmt.Attributes != null) {
          PrintAttributes(stmt.Attributes);
        }
        wr.Write(" ");
        PrintExpression(expr, true);
        wr.Write(";");

      } else if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        wr.Write("print");
        PrintAttributeArgs(s.Args, true);
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

      } else if (stmt is ProduceStmt) {
        var s = (ProduceStmt) stmt;
        wr.Write(s is YieldStmt ? "yield" : "return");
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
        PrintExpression(s.Lhs, true);
        wr.Write(" := ");
        PrintRhs(s.Rhs);
        wr.Write(";");

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

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        wr.Write("forall");
        if (s.BoundVars.Count != 0) {
          wr.Write(" ");
          PrintQuantifierDomain(s.BoundVars, s.Attributes, s.Range);
        }
        if (s.Ens.Count == 0) {
          wr.Write(" ");
        } else {
          wr.WriteLine();
          PrintSpec("ensures", s.Ens, indent + IndentAmount, s.Body != null);
          Indent(indent);
        }
        if (s.Body != null) {
          PrintStatement(s.Body, indent);
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        PrintModifyStmt(indent, s, false);

      } else if (stmt is CalcStmt) {
        CalcStmt s = (CalcStmt)stmt;
        if (printMode == DafnyOptions.PrintModes.NoGhost) { return; }   // Calcs don't get a "ghost" attribute, but they are.
        wr.Write("calc ");
        if (!s.Op.Equals(CalcStmt.DefaultOp)) {
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
          if (!s.Op.Equals(op)) {
            Indent(indent);  // this lines up with the "calc"
            PrintCalcOp(op);
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

      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt)stmt;
        wr.Write("match ");
        PrintExpression(s.Source, false);
        if (s.UsesOptionalBraces) {
          wr.Write(" {");
        }
        int caseInd = indent + (s.UsesOptionalBraces ? IndentAmount : 0);
        foreach (MatchCaseStmt mc in s.Cases) {
          wr.WriteLine();
          Indent(caseInd);
          wr.Write("case {0}", mc.Id);
          if (mc.Arguments.Count != 0) {
            string sep = "(";
            foreach (BoundVar bv in mc.Arguments) {
              wr.Write("{0}{1}", sep, bv.DisplayName);
              if (bv.Type is NonProxyType) {
                wr.Write(": {0}", bv.Type);
              }
              sep = ", ";
            }
            wr.Write(")");
          }
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

      } else if (stmt is ConcreteUpdateStatement) {
        var s = (ConcreteUpdateStatement)stmt;
        string sep = "";
        foreach (var lhs in s.Lhss) {
          wr.Write(sep);
          PrintExpression(lhs, true);
          sep = ", ";
        }
        PrintUpdateRHS(s);
        wr.Write(";");

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Locals.Exists(v => v.IsGhost) && printMode == DafnyOptions.PrintModes.NoGhost) { return; }
        if (s.Locals.Exists(v => v.IsGhost)) {
          wr.Write("ghost ");
        }
        wr.Write("var");
        string sep = "";
        foreach (var local in s.Locals) {
          wr.Write(sep);
          if (local.Attributes != null) {
            PrintAttributes(local.Attributes);
          }
          wr.Write(" {0}", local.DisplayName);
          PrintType(": ", local.OptionalType);
          sep = ",";
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
        } else if (s.S is ModifyStmt) {
          PrintModifyStmt(indent, (ModifyStmt)s.S, true);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected skeleton statement
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    private void PrintModifyStmt(int indent, ModifyStmt s, bool omitFrame) {
      Contract.Requires(0 <= indent);
      Contract.Requires(s != null);
      Contract.Requires(!omitFrame || s.Mod.Expressions.Count == 0);

      wr.Write("modify");
      PrintAttributes(s.Mod.Attributes);
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
        PrintExpression(update.Expr, true);
      } else {
        Contract.Assert(s == null);  // otherwise, unknown type
      }
    }

    void PrintIfStatement(int indent, IfStmt s, bool omitGuard) {
      while (true) {
        if (omitGuard) {
          wr.Write("if ... ");
        } else {
          wr.Write("if ");
          PrintGuard(s.Guard);
          wr.Write(" ");
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
      Contract.Requires(0 <= indent);
      if (omitGuard) {
        wr.WriteLine("while ...");
      } else {
        wr.Write("while ");
        PrintGuard(s.Guard);
        wr.WriteLine();
      }

      PrintSpec("invariant", s.Invariants, indent + IndentAmount, s.Body != null || omitBody || (s.Decreases.Expressions != null && s.Decreases.Expressions.Count != 0) || (s.Mod.Expressions != null && s.Mod.Expressions.Count != 0));
      PrintDecreasesSpec(s.Decreases, indent + IndentAmount, s.Body != null || omitBody || (s.Mod.Expressions != null && s.Mod.Expressions.Count != 0));
      if (s.Mod.Expressions != null) {
        PrintFrameSpecLine("modifies", s.Mod.Expressions, indent + IndentAmount, s.Mod.HasAttributes() ? s.Mod.Attributes : null, s.Body != null || omitBody);
      }
      Indent(indent);
      if (omitBody) {
        wr.WriteLine("...;");
      } else if (s.Body != null) {
        PrintStatement(s.Body, indent);
      }
    }

    void PrintAlternatives(int indent, List<GuardedAlternative> alternatives) {
      int caseInd = indent + IndentAmount;
      foreach (var alternative in alternatives) {
        Indent(caseInd);
        wr.Write("case ");
        PrintExpression(alternative.Guard, false);
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
        PrintExpression(((ExprRhs)rhs).Expr, true);
      } else if (rhs is HavocRhs) {
        wr.Write("*");
      } else if (rhs is TypeRhs) {
        TypeRhs t = (TypeRhs)rhs;
        wr.Write("new ");
        if (t.ArrayDimensions != null) {
          PrintType(t.EType);
          string s = "[";
          foreach (Expression dim in t.ArrayDimensions) {
            Contract.Assume(dim != null);
            wr.Write(s);
            PrintExpression(dim, false);
            s = ", ";
          }
          wr.Write("]");
        } else if (t.Arguments == null) {
          PrintType(t.EType);
        } else {
          PrintType(t.Path);
          wr.Write("(");
          PrintExpressionList(t.Arguments, false);
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
        PrintExpression(guard, false);
      }
    }

    void PrintCalcOp(CalcStmt.CalcOp op) {
      Contract.Requires(op != null);
      wr.Write(op.ToString());
      if (op is CalcStmt.TernaryCalcOp) {
        wr.Write("[");
        PrintExpression(((CalcStmt.TernaryCalcOp) op).Index, false);
        wr.Write("]");
      }
    }

    // ----------------------------- PrintExpression -----------------------------

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
          PrintExpression(ite.Test, false);
          wr.WriteLine(" then");
          PrintExtendedExpr(ite.Thn, indent + IndentAmount, true, false);
          expr = ite.Els;
          if (expr is ITEExpr) {
            Indent(indent);  wr.Write("else ");
          } else {
            Indent(indent);  wr.WriteLine("else");
            Indent(indent + IndentAmount);
            PrintExpression(expr, isRightmost, false);
            wr.WriteLine(endWithCloseParen ? ")" : "");
            return;
          }
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        Indent(indent);
        var parensNeeded = !isRightmost && !e.UsesOptionalBraces;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("match ");
        PrintExpression(e.Source, isRightmost && e.Cases.Count == 0, false);
        if (e.UsesOptionalBraces) { wr.WriteLine(" {"); }
        else if (parensNeeded && e.Cases.Count == 0) { wr.WriteLine(")"); }
        else { wr.WriteLine(); }
        int i = 0;
        int ind = indent + (e.UsesOptionalBraces ? IndentAmount : 0);
        foreach (var mc in e.Cases) {
          bool isLastCase = i == e.Cases.Count - 1;
          Indent(ind);
          wr.Write("case {0}", mc.Id);
          if (mc.Arguments.Count != 0) {
            string sep = "(";
            foreach (BoundVar bv in mc.Arguments) {
              wr.Write("{0}{1}", sep, bv.DisplayName);
              if (bv.Type is NonProxyType) {
                wr.Write(": {0}", bv.Type);
              }
              sep = ", ";
            }
            wr.Write(")");
          }
          wr.WriteLine(" =>");
          PrintExtendedExpr(mc.Body, ind + IndentAmount, isLastCase, isLastCase && (parensNeeded || endWithCloseParen));
          i++;
        }
        if (e.UsesOptionalBraces) {
          Indent(indent);
          wr.WriteLine("}");
        }
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        Indent(indent);
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
          wr.Write(" :| ");
        }
        PrintExpressionList(e.RHSs, true);
        wr.WriteLine(";");
        PrintExtendedExpr(e.Body, indent, isRightmost, endWithCloseParen);

      } else if (expr is ParensExpression) {
        PrintExtendedExpr(((ParensExpression)expr).E, indent, isRightmost, endWithCloseParen);
      } else {
        Indent(indent);
        PrintExpression(expr, false, indent);
        wr.WriteLine(endWithCloseParen ? ")" : "");
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

    /// <summary>
    /// An indent of -1 means print the entire expression on one line.
    /// </summary>
    void PrintExpr(Expression expr, int contextBindingStrength, bool fragileContext, bool isRightmost, bool isFollowedBySemicolon, int indent, int resolv_count = 2)
    {
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
        } else if (e.Value is Basetypes.BigDec) {
          Basetypes.BigDec dec = (Basetypes.BigDec)e.Value;
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
        wr.Write(((IdentifierExpr)expr).Name);

      } else if (expr is DatatypeValue) {
        var dtv = (DatatypeValue)expr;
        bool printParens;
        if (dtv.MemberName == BuiltIns.TupleTypeCtorName) {
          // we're looking at a tuple, whose printed constructor name is essentially the empty string
          printParens = true;
        } else {
          wr.Write("{0}.{1}", dtv.DatatypeName, dtv.MemberName);
          printParens = dtv.Arguments.Count != 0;
        }
        if (printParens) {
          wr.Write("(");
          PrintExpressionList(dtv.Arguments, false);
          wr.Write(")");
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        if (e is MultiSetDisplayExpr) wr.Write("multiset");
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
        PrintTypeInstantiation(e.OptTypeArguments);

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Lhs is ImplicitThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        if (!(e.Lhs is ImplicitThisExpr)) {
          PrintExpr(e.Lhs, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1);
          wr.Write(".");
        }
        wr.Write(e.SuffixName);
        PrintTypeInstantiation(e.OptTypeArguments);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Lhs is ImplicitThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        if (ParensMayMatter(e.Lhs)) {
          wr.Write("(");
          PrintExpression(e.Lhs, false);
          wr.Write(")");
        } else {
          PrintExpr(e.Lhs, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1);
        }
        wr.Write("(");
        PrintExpressionList(e.Args, false);
        wr.Write(")");
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = !(e.Obj is ImplicitThisExpr) &&
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        if (!(e.Obj is ImplicitThisExpr)) {
          PrintExpr(e.Obj, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1);
          wr.Write(".");
        }
        wr.Write(e.MemberName);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Seq, 0x00, false, false, !parensNeeded && isFollowedBySemicolon, indent);  // BOGUS: fix me
        wr.Write("[");
        if (e.SelectOne) {
          Contract.Assert( e.E0 != null);
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
        int opBindingStrength = 0x70;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }
        PrintExpr(e.Array, 0x00, false, false, !parensNeeded && isFollowedBySemicolon, indent);  // BOGUS: fix me
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
        if (e.ResolvedUpdateExpr != null)
        {
          PrintExpr(e.ResolvedUpdateExpr, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent);
        }
        else
        {
          // determine if parens are needed
          int opBindingStrength = 0x70;
          bool parensNeeded = opBindingStrength < contextBindingStrength ||
            (fragileContext && opBindingStrength == contextBindingStrength);

          if (parensNeeded) { wr.Write("("); }
          PrintExpr(e.Seq, 00, false, false, !parensNeeded && isFollowedBySemicolon, indent);  // BOGUS: fix me
          wr.Write("[");
          PrintExpression(e.Index, false);
          wr.Write(" := ");
          PrintExpression(e.Value, false);
          wr.Write("]");
          if (parensNeeded) { wr.Write(")"); }
        }
      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        // determine if parens are needed
        int opBindingStrength = 0x70;
        bool parensNeeded =
          opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        if (parensNeeded) { wr.Write("("); }

        PrintExpr(e.Function, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1);
        wr.Write("(");
        PrintExpressionList(e.Args, false);
        wr.Write(")");

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
          PrintExpr(e.Receiver, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1);
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
          PrintActualArguments(e.Args, e.Name);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is OldExpr) {
        wr.Write("old(");
        PrintExpression(((OldExpr)expr).E, false);
        wr.Write(")");

      } else if (expr is MultiSetFormingExpr) {
        wr.Write("multiset(");
        PrintExpression(((MultiSetFormingExpr)expr).E, false);
        wr.Write(")");

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Cardinality) {
          wr.Write("|");
          PrintExpression(e.E, false);
          wr.Write("|");
        } else if (e.Op == UnaryOpExpr.Opcode.Fresh) {
          wr.Write("fresh(");
          PrintExpression(e.E, false);
          wr.Write(")");
        } else {
          // Prefix operator.
          // determine if parens are needed
          string op;
          int opBindingStrength;
          switch (e.Op) {
            case UnaryOpExpr.Opcode.Not:
              op = "!";  opBindingStrength = 0x60;  break;
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary opcode
          }
          bool parensNeeded = opBindingStrength < contextBindingStrength ||
            (fragileContext && opBindingStrength == contextBindingStrength);

          bool containsNestedNot = e.E is ParensExpression &&
                                ((ParensExpression)e.E).E is UnaryExpr &&
                                ((UnaryOpExpr)((ParensExpression)e.E).E).Op == UnaryOpExpr.Opcode.Not;

          if (parensNeeded) { wr.Write("("); }
          wr.Write(op);
          PrintExpr(e.E, opBindingStrength, containsNestedNot, parensNeeded || isRightmost, !parensNeeded && isFollowedBySemicolon, -1);
          if (parensNeeded) { wr.Write(")"); }
        }

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        PrintType(e.ToType);
        wr.Write("(");
        PrintExpression(e.E, false);
        wr.Write(")");

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
          case BinaryExpr.Opcode.Exp:
            opBindingStrength = 0x11; fragileRightContext = true; break;
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
        var sem = !parensNeeded && isFollowedBySemicolon;
        if (0 <= indent && e.Op == BinaryExpr.Opcode.And) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, indent);
          wr.WriteLine(" {0}", op);
          Indent(indent);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, indent);
        } else if (0 <= indent && e.Op == BinaryExpr.Opcode.Imp) {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, indent);
          wr.WriteLine(" {0}", op);
          int ind = indent + IndentAmount;
          Indent(ind);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, ind);
        } else if (0 <= indent && e.Op == BinaryExpr.Opcode.Exp) {
          PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, indent);
          wr.WriteLine(" {0}", op);
          int ind = indent + IndentAmount;
          Indent(ind);
          PrintExpr(e.E0, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, ind);
        } else if (e.Op == BinaryExpr.Opcode.Exp) {
          PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, -1);
          wr.Write(" {0} ", op);
          PrintExpr(e.E0, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1);
        } else {
          PrintExpr(e.E0, opBindingStrength, fragileLeftContext, false, sem, -1);
          wr.Write(" {0} ", op);
          PrintExpr(e.E1, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            var opBindingStrength = 0x30;
            var fragileLeftContext = true;
            var fragileRightContext = true;

            int opBS = opBindingStrength & 0xF8;
            int ctxtBS = contextBindingStrength & 0xF8;
            bool parensNeeded = opBS < ctxtBS ||
              (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

            if (parensNeeded) { wr.Write("("); }
            var sem = !parensNeeded && isFollowedBySemicolon;
            PrintExpr(e.E1, opBindingStrength, fragileLeftContext, false, sem, -1);
            wr.Write(" {0}#[", e.Op == TernaryExpr.Opcode.PrefixEqOp ? "==" : "!=");
            PrintExpression(e.E0, false);
            wr.Write("] ");
            PrintExpr(e.E2, opBindingStrength, fragileRightContext, parensNeeded || isRightmost, sem, -1);
            if (parensNeeded) { wr.Write(")"); }
            break;
          default:
            Contract.Assert(false);  // unexpected ternary operator
            break;
        }

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        // determine if parens are needed
        int opBindingStrength = 0x30;
        int opBS = opBindingStrength & 0xF8;
        int ctxtBS = contextBindingStrength & 0xF8;
        bool parensNeeded = opBS < ctxtBS ||
          (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

        if (parensNeeded) { wr.Write("("); }
        var sem = !parensNeeded && isFollowedBySemicolon;
        PrintExpr(e.Operands[0], opBindingStrength, true, false, sem, -1);
        for (int i = 0; i < e.Operators.Count; i++) {
          string op = BinaryExpr.OpcodeString(e.Operators[i]);
          if (e.PrefixLimits[i] == null) {
            wr.Write(" {0} ", op);
          } else {
            wr.Write(" {0}#[", op);
            PrintExpression(e.PrefixLimits[i], false);
            wr.Write("] ");
          }
          PrintExpr(e.Operands[i+1], opBindingStrength, true, i == e.Operators.Count - 1 && (parensNeeded || isRightmost), sem, -1);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
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
          wr.Write(" :| ");
        }
        PrintExpressionList(e.RHSs, true);
        wr.Write("; ");
        PrintExpression(e.Body, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is QuantifierExpr) {
        QuantifierExpr e = (QuantifierExpr)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write(e is ForallExpr ? "forall" : "exists");
        PrintTypeParams(e.TypeArgs); // new!
        wr.Write(" ");
        PrintQuantifierDomain(e.BoundVars, e.Attributes, e.Range);
        wr.Write(" :: ");
        if (0 <= indent) {
          int ind = indent + IndentAmount;
          wr.WriteLine();
          Indent(ind);
          PrintExpression(e.Term, !parensNeeded && isFollowedBySemicolon, ind);
        } else {
          PrintExpression(e.Term, !parensNeeded && isFollowedBySemicolon);
        }
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        wr.Write("expr {0}: ", e.Name);
        PrintExpression(e.Body, isFollowedBySemicolon);

       } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        bool parensNeeded = !isRightmost;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("set ");
        string sep = "";
        foreach (BoundVar bv in e.BoundVars) {
          wr.Write("{0}{1}", sep, bv.DisplayName);
          sep = ", ";
          PrintType(": ", bv.Type);
        }
        PrintAttributes(e.Attributes);
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
        wr.Write(e.Finite ? "map " : "imap ");
        string sep = "";
        foreach (BoundVar bv in e.BoundVars) {
          wr.Write("{0}{1}", sep, bv.DisplayName);
          sep = ", ";
          PrintType(": ", bv.Type);
        }
        PrintAttributes(e.Attributes);
        wr.Write(" | ");
        PrintExpression(e.Range, !parensNeeded && isFollowedBySemicolon);
        wr.Write(" :: ");
        PrintExpression(e.Term, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        wr.Write("(");
        wr.Write(Util.Comma(e.BoundVars, bv => bv.DisplayName + ":" + bv.Type));
        wr.Write(")");
        if (e.Range != null) {
          wr.Write(" requires ");
          PrintExpression(e.Range, false);
        }
        foreach (var read in e.Reads) {
          wr.Write(" reads ");
          PrintExpression(read.E, false);
        }
        wr.Write(e.OneShot ? " -> " : " => ");
        PrintExpression(e.Body, isFollowedBySemicolon);

      } else if (expr is WildcardExpr) {
        wr.Write("*");

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        bool parensNeeded;
        if (e.S is AssertStmt || e.S is AssumeStmt || e.S is CalcStmt) {
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
        PrintExpression(ite.Test, false);
        wr.Write(" then ");
        PrintExpression(ite.Thn, false);
        wr.Write(" else ");
        PrintExpression(ite.Els, !parensNeeded && isFollowedBySemicolon);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        // printing of parentheses is done optimally, not according to the parentheses in the given program
        PrintExpr(e.E, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent);

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        string op = "-";
        int opBindingStrength = 0x60;
        bool parensNeeded = opBindingStrength < contextBindingStrength ||
          (fragileContext && opBindingStrength == contextBindingStrength);

        bool containsNestedNegation = e.E is ParensExpression && ((ParensExpression)e.E).E is NegationExpression;

        if (parensNeeded) { wr.Write("("); }
        wr.Write(op);
        PrintExpr(e.E, opBindingStrength, containsNestedNegation, parensNeeded || isRightmost, !parensNeeded && isFollowedBySemicolon, -1);
        if (parensNeeded) { wr.Write(")"); }

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var parensNeeded = !isRightmost && !e.UsesOptionalBraces;
        if (parensNeeded) { wr.Write("("); }
        wr.Write("match ");
        PrintExpression(e.Source, isRightmost && e.Cases.Count == 0, !parensNeeded && isFollowedBySemicolon);
        if (e.UsesOptionalBraces) { wr.Write(" {"); }
        int i = 0;
        foreach (var mc in e.Cases) {
          bool isLastCase = i == e.Cases.Count - 1;
          wr.Write(" case {0}", mc.Id);
          if (mc.Arguments.Count != 0) {
            string sep = "(";
            foreach (BoundVar bv in mc.Arguments) {
              wr.Write("{0}{1}", sep, bv.DisplayName);
              sep = ", ";
            }
            wr.Write(")");
          }
          wr.Write(" => ");
          PrintExpression(mc.Body, isRightmost && isLastCase, !parensNeeded && isFollowedBySemicolon);
          i++;
        }
        if (e.UsesOptionalBraces) { wr.Write(" }"); }
        else if (parensNeeded) { wr.Write(")"); }

      } else if (expr is BoxingCastExpr) {
        // this is not expected for a parsed program, but we may be called for /trace purposes in the translator
        var e = (BoxingCastExpr)expr;
        PrintExpr(e.E, contextBindingStrength, fragileContext, isRightmost, isFollowedBySemicolon, indent);
      } else if (expr is Translator.BoogieWrapper) {
        wr.Write("[BoogieWrapper]");  // this is somewhat unexpected, but we can get here if the /trace switch is used, so it seems best to cover this case here
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
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

    void PrintCasePattern(CasePattern pat) {
      Contract.Requires(pat != null);
      var v = pat.Var;
      if (v != null) {
        wr.Write(v.DisplayName);
        if (v.Type is NonProxyType || DafnyOptions.O.DafnyPrintResolvedFile != null) {
          PrintType(": ", v.Type);
        }
      } else {
        wr.Write(pat.Id);
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

    private void PrintQuantifierDomain(List<BoundVar> boundVars, Attributes attrs, Expression range) {
      Contract.Requires(boundVars != null);
      string sep = "";
      foreach (BoundVar bv in boundVars) {
        wr.Write("{0}{1}", sep, bv.DisplayName);
        PrintType(": ", bv.Type);
        sep = ", ";
      }
      PrintAttributes(attrs);
      if (range != null) {
        wr.Write(" | ");
        PrintExpression(range, false);
      }
    }

    void PrintActualArguments(List<Expression> args, string name) {
      Contract.Requires(args != null);
      Contract.Requires(name != null);
      if (name.EndsWith("#")) {
        wr.Write("[");
        PrintExpression(args[0], false);
        wr.Write("]");
        args = new List<Expression>(args.Skip(1));
      }
      wr.Write("(");
      PrintExpressionList(args, false);
      wr.Write(")");
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
    void PrintExpressionPairList(List<ExpressionPair> exprs) {
      Contract.Requires(exprs != null);
      string sep = "";
      foreach (ExpressionPair p in exprs) {
        Contract.Assert(p != null);
        wr.Write(sep);
        sep = ", ";
        PrintExpression(p.A, false);
        wr.Write(":=");
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
        PrintExpression(fe.E, true);
        if (fe.FieldName != null) {
          wr.Write("`{0}", fe.FieldName);
        }
      }
    }
  }
}
