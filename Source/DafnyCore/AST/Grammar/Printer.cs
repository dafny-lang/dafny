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
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public enum PrintModes {
    Everything,
    DllEmbed,
    NoIncludes,
    NoGhost
  }

  public class Printer {
    private DafnyOptions options;
    static Printer() {
      DafnyOptions.RegisterLegacyBinding(PrintMode, (options, value) => {
        options.PrintMode = value;
      });
    }

    public static readonly Option<PrintModes> PrintMode = new("--print-mode", () => PrintModes.Everything, @"
Everything - Print everything listed below.
DllEmbed - print the source that will be included in a compiled dll.
NoIncludes - disable printing of {:verify false} methods
    incorporated via the include mechanism, as well as datatypes and
    fields included from other files.
NoGhost - disable printing of functions, ghost methods, and proof
    statements in implementation methods. It also disables anything
    NoIncludes disables.".TrimStart()) {
      IsHidden = true
    };

    TextWriter wr;
    PrintModes printMode;
    bool afterResolver;
    bool printingExportSet = false;
    bool printingDesugared = false;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(wr != null);
    }

    public Printer(TextWriter wr, DafnyOptions options, PrintModes printMode = PrintModes.Everything) {
      Contract.Requires(wr != null);
      this.wr = wr;
      this.options = options;
      this.printMode = printMode;
    }

    public static string ExprToString(DafnyOptions options, Expression expr) {
      Contract.Requires(expr != null);
      using var wr = new StringWriter();
      var pr = new Printer(wr, options);
      pr.PrintExpression(expr, false);
      return wr.ToString();
    }

    public static string GuardToString(DafnyOptions options, bool isBindingGuard, Expression expr) {
      Contract.Requires(!isBindingGuard || (expr is ExistsExpr && ((ExistsExpr)expr).Range == null));
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, options);
        pr.PrintGuard(isBindingGuard, expr);
        return wr.ToString();
      }
    }

    public static string ExtendedExprToString(DafnyOptions options, Expression expr) {
      Contract.Requires(expr != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, options);
        pr.PrintExtendedExpr(expr, 0, true, false);
        return wr.ToString();
      }
    }

    public static string FrameExprListToString(DafnyOptions options, List<FrameExpression> fexprs) {
      Contract.Requires(fexprs != null);
      using var wr = new StringWriter();
      var pr = new Printer(wr, options);
      pr.PrintFrameExpressionList(fexprs);
      return wr.ToString();
    }

    public static string StatementToString(DafnyOptions options, Statement stmt) {
      Contract.Requires(stmt != null);
      using var wr = new StringWriter();
      var pr = new Printer(wr, options);
      pr.PrintStatement(stmt, 0);
      return ToStringWithoutNewline(wr);
    }

    public static string IteratorClassToString(DafnyOptions options, IteratorDecl iter) {
      Contract.Requires(iter != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, options);
        pr.PrintIteratorClass(iter, 0, null);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string IteratorSignatureToString(DafnyOptions options, IteratorDecl iter) {
      Contract.Requires(iter != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, options);
        pr.PrintIteratorSignature(iter, 0);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string FieldToString(DafnyOptions options, Field field) {
      Contract.Requires(field != null);
      using (var wr = new StringWriter()) {
        var pr = new Printer(wr, options);
        pr.PrintField(field, 0);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string FunctionSignatureToString(DafnyOptions options, Function f) {
      Contract.Requires(f != null);
      using var wr = new StringWriter();
      var pr = new Printer(wr, options);
      pr.PrintFunction(f, 0, true);
      return ToStringWithoutNewline(wr);
    }

    public static string MethodSignatureToString(DafnyOptions options, Method m) {
      Contract.Requires(m != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, options);
        pr.PrintMethod(m, 0, true);
        return ToStringWithoutNewline(wr);
      }
    }

    public static string ModuleDefinitionToString(DafnyOptions options, ModuleDefinition m, PrintModes printMode = PrintModes.Everything) {
      Contract.Requires(m != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, options, printMode);
        pr.PrintModuleDefinition(m, m.VisibilityScope, 0, null, null);
        return ToStringWithoutNewline(wr);
      }
    }


    /// <summary>
    /// Returns a string for all attributes on the list "a".  Each attribute is
    /// followed by a space.
    /// </summary>
    public static string AttributesToString(DafnyOptions options, Attributes a) {
      if (a == null) {
        return "";
      } else {
        return AttributesToString(options, a.Prev) + OneAttributeToString(options, a) + " ";
      }
    }

    public static string OneAttributeToString(DafnyOptions options, Attributes a, string nameSubstitution = null) {
      Contract.Requires(a != null);
      using (var wr = new System.IO.StringWriter()) {
        var pr = new Printer(wr, options);
        pr.PrintOneAttribute(a, nameSubstitution);
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

    public void PrintProgram(Program prog, bool afterResolver) {
      Contract.Requires(prog != null);
      this.afterResolver = afterResolver;
      if (options.ShowEnv != Bpl.ExecutionEngineOptions.ShowEnvironment.Never) {
        wr.WriteLine("// " + options.Version);
        wr.WriteLine("// " + options.Environment);
      }
      if (options.PrintMode != PrintModes.DllEmbed) {
        wr.WriteLine("// {0}", prog.Name);
      }
      if (options.DafnyPrintResolvedFile != null && options.PrintMode == PrintModes.Everything) {
        wr.WriteLine();
        wr.WriteLine("/*");
        PrintModuleDefinition(prog.BuiltIns.SystemModule, null, 0, null, Path.GetFullPath(options.DafnyPrintResolvedFile));
        wr.Write("// bitvector types in use:");
        foreach (var w in prog.BuiltIns.Bitwidths) {
          wr.Write(" bv{0}", w);
        }
        wr.WriteLine();
        wr.WriteLine("*/");
      }
      wr.WriteLine();
      PrintCallGraph(prog.DefaultModuleDef, 0);
      PrintTopLevelDecls(prog.DefaultModuleDef.TopLevelDecls, 0, null, Path.GetFullPath(prog.FullName));
      foreach (var tup in prog.DefaultModuleDef.PrefixNamedModules) {
        var decls = new List<TopLevelDecl>() { tup.Item2 };
        PrintTopLevelDecls(decls, 0, tup.Item1, Path.GetFullPath(prog.FullName));
      }
      wr.Flush();
    }

    public void PrintCallGraph(ModuleDefinition module, int indent) {
      Contract.Requires(module != null);
      Contract.Requires(0 <= indent);
      if (options.DafnyPrintResolvedFile != null && options.PrintMode == PrintModes.Everything) {
        // print call graph
        Indent(indent); wr.WriteLine("/* CALL GRAPH for module {0}:", module.Name);
        var SCCs = module.CallGraph.TopologicallySortedComponents();
        // Sort output SCCs in order of: descending height, then decreasing size of SCC, then alphabetical order of the name of
        // the representative element. By being this specific, we reduce changes in output from minor changes in the code. (With
        // more effort, we could be even more deterministic, if needed in the future.)
        SCCs.Sort((m, n) => {
          var mm = module.CallGraph.GetSCCRepresentativePredecessorCount(m);
          var nn = module.CallGraph.GetSCCRepresentativePredecessorCount(n);
          if (mm < nn) {
            return 1;
          } else if (mm > nn) {
            return -1;
          }
          mm = module.CallGraph.GetSCCSize(m);
          nn = module.CallGraph.GetSCCSize(n);
          if (mm < nn) {
            return 1;
          } else if (mm > nn) {
            return -1;
          }
          return string.CompareOrdinal(m.NameRelativeToModule, n.NameRelativeToModule);
        });
        foreach (var clbl in SCCs) {
          Indent(indent);
          wr.WriteLine(" * SCC at height {0}:", module.CallGraph.GetSCCRepresentativePredecessorCount(clbl));
          var r = module.CallGraph.GetSCC(clbl);
          foreach (var m in r) {
            Indent(indent);
            var maybeByMethod = m is Method method && method.IsByMethod ? " (by method)" : "";
            wr.WriteLine($" *   {m.NameRelativeToModule}{maybeByMethod}");
          }
        }
        Indent(indent); wr.WriteLine(" */");
      }
    }

    public void PrintTopLevelDecls(List<TopLevelDecl> decls, int indent, List<IToken>/*?*/ prefixIds, string fileBeingPrinted) {
      Contract.Requires(decls != null);
      int i = 0;
      foreach (TopLevelDecl d in decls) {
        Contract.Assert(d != null);
        if (PrintModeSkipGeneral(d.tok, fileBeingPrinted)) { continue; }
        if (d is OpaqueTypeDecl) {
          var at = (OpaqueTypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("type", at.Attributes, at.Name + TPCharacteristicsSuffix(at.Characteristics), d.TypeArgs);
          if (at.Members.Count == 0) {
            wr.WriteLine();
          } else {
            wr.WriteLine(" {");
            PrintMembers(at.Members, indent + IndentAmount, fileBeingPrinted);
            Indent(indent);
            wr.WriteLine("}");
          }
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("newtype", dd.Attributes, dd.Name, new List<TypeParameter>());
          wr.Write(" = ");
          if (dd.Var == null) {
            PrintType(dd.BaseType);
            wr.WriteLine();
          } else {
            wr.Write(dd.Var.DisplayName);
            if (ShowType(dd.Var.Type)) {
              wr.Write(": ");
              PrintType(dd.BaseType);
            }
            wr.WriteLine();
            Indent(indent + IndentAmount);
            wr.Write("| ");
            PrintExpression(dd.Constraint, true);
            wr.WriteLine();
            if (dd.WitnessKind != SubsetTypeDecl.WKind.CompiledZero) {
              Indent(indent + IndentAmount);
              PrintWitnessClause(dd);
              wr.WriteLine();
            }
          }
          if (dd.Members.Count != 0) {
            Indent(indent);
            wr.WriteLine("{");
            PrintMembers(dd.Members, indent + IndentAmount, fileBeingPrinted);
            Indent(indent);
            wr.WriteLine("}");
          }
        } else if (d is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("type", dd.Attributes, dd.Name + TPCharacteristicsSuffix(dd.Characteristics), dd.TypeArgs);
          wr.Write(" = ");
          wr.Write(dd.Var.DisplayName);
          if (ShowType(dd.Var.Type)) {
            wr.Write(": ");
            PrintType(dd.Rhs);
          }
          if (dd is NonNullTypeDecl) {
            wr.Write(" ");
          } else {
            wr.WriteLine();
            Indent(indent + IndentAmount);
          }
          wr.Write("| ");
          PrintExpression(dd.Constraint, true);
          if (dd.WitnessKind != SubsetTypeDecl.WKind.CompiledZero) {
            if (dd is NonNullTypeDecl) {
              wr.Write(" ");
            } else {
              wr.WriteLine();
              Indent(indent + IndentAmount);
            }
            PrintWitnessClause(dd);
          }
          wr.WriteLine();
        } else if (d is TypeSynonymDecl) {
          var dd = (TypeSynonymDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("type", dd.Attributes, dd.Name + TPCharacteristicsSuffix(dd.Characteristics), dd.TypeArgs);
          wr.Write(" = ");
          PrintType(dd.Rhs);
          wr.WriteLine();
        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          PrintDatatype(dd, indent, fileBeingPrinted);
        } else if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          PrintIteratorSignature(iter, indent);

          if (iter.Body != null) {
            Indent(indent);
            PrintStatement(iter.Body, indent);
            wr.WriteLine();
          }

          if (options.DafnyPrintResolvedFile != null) {
            // also print the members that were created as part of the interpretation of the iterator
            Contract.Assert(iter.Members.Count != 0);  // filled in during resolution
            Indent(indent); wr.WriteLine("/*---------- iterator members ----------");
            Indent(indent); PrintIteratorClass(iter, indent, fileBeingPrinted);
            Indent(indent); wr.WriteLine("---------- iterator members ----------*/");
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

        } else if (d is ValuetypeDecl) {
          var vtd = (ValuetypeDecl)d;
          if (i++ != 0) { wr.WriteLine(); }
          Indent(indent);
          PrintClassMethodHelper("type", vtd.Attributes, vtd.Name, vtd.TypeArgs);
          if (vtd.Members.Count == 0) {
            wr.WriteLine(" { }");
          } else {
            wr.WriteLine(" {");
            PrintMembers(new List<MemberDecl>(vtd.Members.Values), indent + IndentAmount, fileBeingPrinted);
            Indent(indent);
            wr.WriteLine("}");
          }

        } else if (d is ModuleDecl) {
          wr.WriteLine();
          Indent(indent);
          if (d is LiteralModuleDecl modDecl) {
            VisibilityScope scope = null;
            if (modDecl.Signature != null) {
              scope = modDecl.Signature.VisibilityScope;
            }
            PrintModuleDefinition(modDecl.ModuleDef, scope, indent, prefixIds, fileBeingPrinted);
          } else if (d is AliasModuleDecl) {
            var dd = (AliasModuleDecl)d;

            wr.Write("import");
            if (dd.Opened) {
              wr.Write(" opened");
            }
            if (dd.ResolvedHash.HasValue && this.printMode == PrintModes.DllEmbed) {
              wr.Write(" /*");
              wr.Write(dd.ResolvedHash);
              wr.Write("*/");
            }
            wr.Write(" {0}", dd.Name);
            if (dd.Name != dd.TargetQId.ToString()) {
              wr.Write(" = {0}", dd.TargetQId.ToString());
            }
            if (dd.Exports.Count == 1) {
              wr.Write("`{0}", dd.Exports[0].val);
            }
            if (dd.Exports.Count > 1) {
              wr.Write("`{{{0}}}", Util.Comma(dd.Exports, id => id.val));
            }
            wr.WriteLine();
          } else if (d is AbstractModuleDecl) {
            var dd = (AbstractModuleDecl)d;

            wr.Write("import");
            if (dd.Opened) {
              wr.Write(" opened");
            }
            if (dd.ResolvedHash.HasValue && this.printMode == PrintModes.DllEmbed) {
              wr.Write(" /*");
              wr.Write(dd.ResolvedHash);
              wr.Write("*/");
            }
            wr.Write(" {0} ", dd.Name);
            wr.Write(": {0}", dd.QId.ToString());
            if (dd.Exports.Count > 0) {
              wr.Write("`{{{0}}}", Util.Comma(dd.Exports, id => id.val));
            }
            wr.WriteLine();

          } else if (d is ModuleExportDecl) {
            ModuleExportDecl e = (ModuleExportDecl)d;
            if (!e.IsDefault) {
              wr.Write("export {0}", e.Name);
            } else {
              wr.Write("export");
            }

            if (e.IsRefining) {
              wr.Write(" ...");
            }
            if (e.Extends.Count > 0) {
              wr.Write(" extends {0}", Util.Comma(e.Extends, id => id.val));
            }

            wr.WriteLine();
            PrintModuleExportDecl(e, indent + IndentAmount, fileBeingPrinted);
            wr.WriteLine();
          } else {
            Contract.Assert(false); // unexpected ModuleDecl
          }
        } else {
          Contract.Assert(false); // unexpected TopLevelDecl
        }
      }
    }

    private void PrintWitnessClause(RedirectingTypeDecl dd) {
      Contract.Requires(dd != null);
      Contract.Requires(dd.WitnessKind != SubsetTypeDecl.WKind.CompiledZero);

      switch (dd.WitnessKind) {
        case SubsetTypeDecl.WKind.Ghost:
          wr.Write("ghost ");
          goto case SubsetTypeDecl.WKind.Compiled;
        case SubsetTypeDecl.WKind.Compiled:
          wr.Write("witness ");
          PrintExpression(dd.Witness, true);
          break;
        case SubsetTypeDecl.WKind.OptOut:
          wr.Write("witness *");
          break;
        case SubsetTypeDecl.WKind.Special:
          wr.Write("/*special witness*/");
          break;
        case SubsetTypeDecl.WKind.CompiledZero:
        default:
          Contract.Assert(false);  // unexpected WKind
          break;
      }
    }

    void PrintModuleExportDecl(ModuleExportDecl m, int indent, string fileBeingPrinted) {
      Contract.Requires(m != null);

      if (m.RevealAll) {
        Indent(indent);
        wr.WriteLine("reveals *");
      }
      if (m.ProvideAll) {
        Indent(indent);
        wr.WriteLine("provides *");
      }
      var i = 0;
      while (i < m.Exports.Count) {
        var start = i;
        var bodyKind = m.Exports[start].Opaque;
        do {
          i++;
        } while (i < m.Exports.Count && m.Exports[i].Opaque == bodyKind);
        // print [start..i)
        Indent(indent);
        wr.Write("{0} ", bodyKind ? "provides" : "reveals");
        wr.WriteLine(Util.Comma(i - start, j => m.Exports[start + j].ToString()));

        if (options.DafnyPrintResolvedFile != null) {
          Contract.Assert(!printingExportSet);
          printingExportSet = true;
          Indent(indent);
          wr.WriteLine("/*----- exported view:");
          for (int j = start; j < i; j++) {
            var id = m.Exports[j];
            if (id.Decl is TopLevelDecl) {
              PrintTopLevelDecls(new List<TopLevelDecl> { (TopLevelDecl)id.Decl }, indent + IndentAmount, null, fileBeingPrinted);
            } else if (id.Decl is MemberDecl) {
              PrintMembers(new List<MemberDecl> { (MemberDecl)id.Decl }, indent + IndentAmount, fileBeingPrinted);
            }
          }
          Indent(indent);
          wr.WriteLine("-----*/");
          Contract.Assert(printingExportSet);
          printingExportSet = false;
        }
      }
    }

    public void PrintModuleDefinition(ModuleDefinition module, VisibilityScope scope, int indent, List<IToken>/*?*/ prefixIds, string fileBeingPrinted) {
      Contract.Requires(module != null);
      Contract.Requires(0 <= indent);
      Type.PushScope(scope);
      if (module.IsAbstract) {
        wr.Write("abstract ");
      }
      wr.Write("module");
      PrintAttributes(module.Attributes);
      wr.Write(" ");
      if (prefixIds != null) {
        foreach (var p in prefixIds) {
          wr.Write("{0}.", p.val);
        }
      }
      wr.Write("{0} ", module.Name);
      if (module.RefinementQId != null) {
        wr.Write("refines {0} ", module.RefinementQId.ToString());
      }
      if (module.TopLevelDecls.Count == 0) {
        wr.WriteLine("{ }");
      } else {
        wr.WriteLine("{");
        PrintCallGraph(module, indent + IndentAmount);
        PrintTopLevelDeclsOrExportedView(module, indent, fileBeingPrinted);
        Indent(indent);
        wr.WriteLine("}");
      }
      Type.PopScope(scope);
    }

    void PrintTopLevelDeclsOrExportedView(ModuleDefinition module, int indent, string fileBeingPrinted) {
      var decls = module.TopLevelDecls;
      // only filter based on view name after resolver.
      if (afterResolver && options.DafnyPrintExportedViews.Count != 0) {
        decls = new List<TopLevelDecl>();
        foreach (var nameOfView in options.DafnyPrintExportedViews) {
          foreach (var decl in module.TopLevelDecls) {
            if (decl.FullName.Equals(nameOfView)) {
              decls.Add(decl);
            }
          }
        }
      }
      PrintTopLevelDecls(decls, indent + IndentAmount, null, fileBeingPrinted);
      foreach (var tup in module.PrefixNamedModules) {
        decls = new List<TopLevelDecl>() { tup.Item2 };
        PrintTopLevelDecls(decls, indent + IndentAmount, tup.Item1, fileBeingPrinted);
      }
    }

    void PrintIteratorSignature(IteratorDecl iter, int indent) {
      Indent(indent);
      PrintClassMethodHelper("iterator", iter.Attributes, iter.Name, iter.TypeArgs);
      if (iter.IsRefining) {
        wr.Write(" ... ");
      } else {
        PrintFormals(iter.Ins, iter);
        if (iter.Outs.Count != 0) {
          if (iter.Ins.Count + iter.Outs.Count <= 3) {
            wr.Write(" yields ");
          } else {
            wr.WriteLine();
            Indent(indent + 2 * IndentAmount);
            wr.Write("yields ");
          }
          PrintFormals(iter.Outs, iter);
        }
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
      wr.WriteLine();
    }

    private void PrintIteratorClass(IteratorDecl iter, int indent, string fileBeingPrinted) {
      PrintClassMethodHelper("class", null, iter.Name, iter.TypeArgs);
      wr.WriteLine(" {");
      PrintMembers(iter.Members, indent + IndentAmount, fileBeingPrinted);
      Indent(indent); wr.WriteLine("}");

      Contract.Assert(iter.NonNullTypeDecl != null);
      PrintTopLevelDecls(new List<TopLevelDecl> { iter.NonNullTypeDecl }, indent, null, fileBeingPrinted);
    }

    public void PrintClass(ClassDecl c, int indent, string fileBeingPrinted) {
      Contract.Requires(c != null);

      Indent(indent);
      PrintClassMethodHelper((c is TraitDecl) ? "trait" : "class", c.Attributes, c.Name, c.TypeArgs);
      if (c.IsRefining) {
        wr.Write(" ... ");
      } else {
        string sep = " extends ";
        foreach (var trait in c.ParentTraits) {
          wr.Write(sep);
          PrintType(trait);
          sep = ", ";
        }
      }

      if (c.Members.Count == 0) {
        wr.WriteLine(" { }");
      } else {
        wr.WriteLine(" {");
        PrintMembers(c.Members, indent + IndentAmount, fileBeingPrinted);
        Indent(indent);
        wr.WriteLine("}");
      }

      if (options.DafnyPrintResolvedFile != null && c.NonNullTypeDecl != null) {
        if (!printingExportSet) {
          Indent(indent); wr.WriteLine("/*-- non-null type");
        }
        PrintTopLevelDecls(new List<TopLevelDecl> { c.NonNullTypeDecl }, indent, null, fileBeingPrinted);
        if (!printingExportSet) {
          Indent(indent); wr.WriteLine("*/");
        }
      }
    }

    public void PrintMembers(List<MemberDecl> members, int indent, string fileBeingPrinted) {
      Contract.Requires(members != null);

      int state = 0;  // 0 - no members yet; 1 - previous member was a field; 2 - previous member was non-field
      foreach (MemberDecl m in members) {
        if (PrintModeSkipGeneral(m.tok, fileBeingPrinted)) { continue; }
        if (printMode == PrintModes.DllEmbed && Attributes.Contains(m.Attributes, "auto_generated")) {
          // omit this declaration
        } else if (m is Method) {
          if (state != 0) { wr.WriteLine(); }
          PrintMethod((Method)m, indent, false);
          var com = m as ExtremeLemma;
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
          if (m is ExtremePredicate fixp && fixp.PrefixPredicate != null) {
            Indent(indent); wr.WriteLine("/*** (note, what is printed here does not show substitutions of calls to prefix predicates)");
            PrintFunction(fixp.PrefixPredicate, indent, false);
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

      wr.Write(kind);
      PrintAttributes(attrs);

      if (ArrowType.IsArrowTypeName(name)) {
        PrintArrowType(ArrowType.ANY_ARROW, name, typeArgs);
      } else if (ArrowType.IsPartialArrowTypeName(name)) {
        PrintArrowType(ArrowType.PARTIAL_ARROW, name, typeArgs);
      } else if (ArrowType.IsTotalArrowTypeName(name)) {
        PrintArrowType(ArrowType.TOTAL_ARROW, name, typeArgs);
      } else if (BuiltIns.IsTupleTypeName(name)) {
        wr.Write(" /*{0}*/ ({1})", name, Util.Comma(typeArgs, TypeParamString));
      } else {
        wr.Write(" {0}", name);
        PrintTypeParams(typeArgs);
      }
    }

    private void PrintTypeParams(List<TypeParameter> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(
        typeArgs.All(tp => tp.Name.StartsWith("_")) ||
        typeArgs.All(tp => !tp.Name.StartsWith("_")));

      if (typeArgs.Count != 0 && !typeArgs[0].Name.StartsWith("_")) {
        wr.Write("<{0}>", Util.Comma(typeArgs, TypeParamString));
      }
    }

    public string TypeParamString(TypeParameter tp) {
      Contract.Requires(tp != null);
      string variance;
      switch (tp.VarianceSyntax) {
        case TypeParameter.TPVarianceSyntax.Covariant_Permissive:
          variance = "*";
          break;
        case TypeParameter.TPVarianceSyntax.Covariant_Strict:
          variance = "+";
          break;
        case TypeParameter.TPVarianceSyntax.NonVariant_Permissive:
          variance = "!";
          break;
        case TypeParameter.TPVarianceSyntax.NonVariant_Strict:
          variance = "";
          break;
        case TypeParameter.TPVarianceSyntax.Contravariance:
          variance = "-";
          break;
        default:
          Contract.Assert(false);  // unexpected VarianceSyntax
          throw new cce.UnreachableException();
      }
      return variance + tp.Name + TPCharacteristicsSuffix(tp.Characteristics);
    }

    private void PrintArrowType(string arrow, string internalName, List<TypeParameter> typeArgs) {
      Contract.Requires(arrow != null);
      Contract.Requires(internalName != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(1 <= typeArgs.Count);  // argument list ends with the result type
      wr.Write(" /*{0}*/ ", internalName);
      int arity = typeArgs.Count - 1;
      if (arity != 1) {
        wr.Write("(");
      }
      wr.Write(Util.Comma(arity, i => TypeParamString(typeArgs[i])));
      if (arity != 1) {
        wr.Write(")");
      }
      wr.Write(" {0} {1}", arrow, TypeParamString(typeArgs[arity]));
    }

    private void PrintTypeInstantiation(List<Type> typeArgs) {
      Contract.Requires(typeArgs == null || typeArgs.Count != 0);
      wr.Write(Type.TypeArgsToString(options, typeArgs));
    }

    public void PrintDatatype(DatatypeDecl dt, int indent, string fileBeingPrinted) {
      Contract.Requires(dt != null);
      Indent(indent);
      PrintClassMethodHelper(dt is IndDatatypeDecl ? "datatype" : "codatatype", dt.Attributes, dt.Name, dt.TypeArgs);
      wr.Write(" =");
      string sep = "";
      foreach (DatatypeCtor ctor in dt.Ctors) {
        wr.Write(sep);
        PrintClassMethodHelper(ctor.IsGhost ? " ghost" : "", ctor.Attributes, ctor.Name, new List<TypeParameter>());
        if (ctor.Formals.Count != 0) {
          PrintFormals(ctor.Formals, null);
        }
        sep = " |";
      }
      if (dt.Members.Count == 0) {
        wr.WriteLine();
      } else {
        wr.WriteLine(" {");
        PrintMembers(dt.Members, indent + IndentAmount, fileBeingPrinted);
        Indent(indent);
        wr.WriteLine("}");
      }
    }

    /// <summary>
    /// Prints a space before each attribute.
    /// </summary>
    public void PrintAttributes(Attributes a) {
      if (a != null) {
        PrintAttributes(a.Prev);
        wr.Write(" ");
        PrintOneAttribute(a);
      }
    }
    public void PrintOneAttribute(Attributes a, string nameSubstitution = null) {
      Contract.Requires(a != null);
      var name = nameSubstitution ?? a.Name;
      var usAttribute = name.StartsWith("_") || (options.DisallowExterns && name == "extern");
      wr.Write("{1}{{:{0}", name, usAttribute ? "/*" : "");
      if (a.Args != null) {
        PrintAttributeArgs(a.Args, false);
      }
      wr.Write("}}{0}", usAttribute ? "*/" : "");

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
      if (field.HasStaticKeyword) {
        wr.Write("static ");
      }
      if (field.IsGhost) {
        wr.Write("ghost ");
      }
      if (field is ConstantField) {
        wr.Write("const");
      } else {
        wr.Write("var");
      }
      PrintAttributes(field.Attributes);
      wr.Write(" {0}", field.Name);
      if (ShowType(field.Type)) {
        wr.Write(": ");
        PrintType(field.Type);
      }
      if (field is ConstantField) {
        var c = (ConstantField)field;
        if (c.Rhs != null) {
          wr.Write(" := ");
          PrintExpression(c.Rhs, true);
        }
      } else if (field.IsUserMutable) {
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
      Indent(indent);
      PrintClassMethodHelper(f.GetFunctionDeclarationKeywords(options), f.Attributes, f.Name, f.TypeArgs);
      if (f.SignatureIsOmitted) {
        wr.Write(" ...");
      } else {
        if (f is ExtremePredicate) {
          PrintKTypeIndication(((ExtremePredicate)f).TypeOfK);
        }
        PrintFormals(f.Formals, f, f.Name);
        if (f.Result != null || (f is not Predicate && f is not ExtremePredicate && f is not TwoStatePredicate && f is not PrefixPredicate)) {
          wr.Write(": ");
          if (f.Result != null) {
            wr.Write("(");
            PrintFormal(f.Result, false);
            wr.Write(")");
          } else {
            PrintType(f.ResultType);
          }
        }
      }

      int ind = indent + IndentAmount;
      PrintSpec("requires", f.Req, ind);
      PrintFrameSpecLine("reads", f.Reads, ind, null);
      PrintSpec("ensures", f.Ens, ind);
      PrintDecreasesSpec(f.Decreases, ind);
      wr.WriteLine();
      if (f.Body != null && !printSignatureOnly) {
        Indent(indent);
        wr.WriteLine("{");
        PrintExtendedExpr(f.Body, ind, true, false);
        Indent(indent);
        wr.Write("}");
        if (f.ByMethodBody != null) {
          wr.Write(" by method ");
          if (options.DafnyPrintResolvedFile != null && f.ByMethodDecl != null) {
            Contract.Assert(f.ByMethodDecl.Ens.Count == 1);
            wr.Write("/* ensures");
            PrintAttributedExpression(f.ByMethodDecl.Ens[0]);
            wr.Write(" */ ");
          }
          PrintStatement(f.ByMethodBody, indent);
        }
        wr.WriteLine();
      }
    }

    // ----------------------------- PrintMethod -----------------------------

    const int IndentAmount = 2; // The amount of indent for each new scope
    void Indent(int amount) {
      Contract.Requires(0 <= amount);
      wr.Write(new String(' ', amount));
    }

    private bool PrintModeSkipFunctionOrMethod(bool IsGhost, Attributes attributes, string name) {
      if (printMode == PrintModes.NoGhost && IsGhost) { return true; }
      if (printMode == PrintModes.NoIncludes || printMode == PrintModes.NoGhost) {
        bool verify = true;
        if (Attributes.ContainsBool(attributes, "verify", ref verify) && !verify) { return true; }
        if (name.Contains("INTERNAL") || name.StartsWith("reveal_")) { return true; }
      }
      return false;
    }

    private bool PrintModeSkipGeneral(Bpl.IToken tok, string fileBeingPrinted) {
      return (printMode == PrintModes.NoIncludes || printMode == PrintModes.NoGhost)
             && tok.filename != null && fileBeingPrinted != null && Path.GetFullPath(tok.filename) != fileBeingPrinted;
    }

    public void PrintMethod(Method method, int indent, bool printSignatureOnly) {
      Contract.Requires(method != null);

      if (PrintModeSkipFunctionOrMethod(method.IsGhost, method.Attributes, method.Name)) { return; }
      Indent(indent);
      string k = method is Constructor ? "constructor" :
        method is LeastLemma ? "least lemma" :
        method is GreatestLemma ? "greatest lemma" :
        method is Lemma || method is PrefixLemma ? "lemma" :
        method is TwoStateLemma ? "twostate lemma" :
        "method";
      if (method.HasStaticKeyword) { k = "static " + k; }
      if (method.IsGhost && !method.IsLemmaLike) {
        k = "ghost " + k;
      }
      string nm = method is Constructor && !((Constructor)method).HasName ? "" : method.Name;
      PrintClassMethodHelper(k, method.Attributes, nm, method.TypeArgs);
      if (method.SignatureIsOmitted) {
        wr.Write(" ...");
      } else {
        if (method is ExtremeLemma) {
          PrintKTypeIndication(((ExtremeLemma)method).TypeOfK);
        }
        PrintFormals(method.Ins, method, method.Name);
        if (method.Outs.Count != 0) {
          if (method.Ins.Count + method.Outs.Count <= 3) {
            wr.Write(" returns ");
          } else {
            wr.WriteLine();
            Indent(indent + 2 * IndentAmount);
            wr.Write("returns ");
          }
          PrintFormals(method.Outs, method);
        }
      }

      int ind = indent + IndentAmount;
      PrintSpec("requires", method.Req, ind);
      if (method.Mod.Expressions != null) {
        PrintFrameSpecLine("modifies", method.Mod.Expressions, ind, method.Mod.HasAttributes() ? method.Mod.Attributes : null);
      }
      PrintSpec("ensures", method.Ens, ind);
      PrintDecreasesSpec(method.Decreases, ind);
      wr.WriteLine();

      if (method.Body != null && !printSignatureOnly) {
        Indent(indent);
        PrintStatement(method.Body, indent);
        wr.WriteLine();
      }
    }

    void PrintKTypeIndication(ExtremePredicate.KType kType) {
      switch (kType) {
        case ExtremePredicate.KType.Nat:
          wr.Write("[nat]");
          break;
        case ExtremePredicate.KType.ORDINAL:
          wr.Write("[ORDINAL]");
          break;
        case ExtremePredicate.KType.Unspecified:
          break;
        default:
          Contract.Assume(false);  // unexpected KType value
          break;
      }
    }

    internal void PrintFormals(List<Formal> ff, ICallable/*?*/ context, string name = null) {
      Contract.Requires(ff != null);
      if (name != null && name.EndsWith("#")) {
        wr.Write("[");
        PrintFormal(ff[0], false);
        wr.Write("]");
        ff = new List<Formal>(ff.Skip(1));
      }
      wr.Write("(");
      string sep = "";
      foreach (Formal f in ff) {
        Contract.Assert(f != null);
        wr.Write(sep);
        sep = ", ";
        PrintFormal(f, (context is TwoStateLemma || context is TwoStateFunction) && f.InParam);
      }
      wr.Write(")");
    }

    void PrintFormal(Formal f, bool showNewKeyword) {
      Contract.Requires(f != null);
      if (showNewKeyword && !f.IsOld) {
        wr.Write("new ");
      }
      if (f.IsOlder) {
        Contract.Assert(f.HasName);
        wr.Write("older ");
      }
      if (f.IsGhost) {
        wr.Write("ghost ");
      }
      if (f.IsNameOnly) {
        Contract.Assert(f.HasName);
        wr.Write("nameonly ");
      }
      if (f.HasName) {
        wr.Write("{0}: ", f.DisplayName);
      }
      PrintType(f.Type);
      if (f.DefaultValue != null) {
        wr.Write(" := ");
        PrintExpression(f.DefaultValue, false);
      }
    }

    internal void PrintDecreasesSpec(Specification<Expression> decs, int indent) {
      Contract.Requires(decs != null);
      if (printMode == PrintModes.NoGhost) { return; }
      if (decs.Expressions != null && decs.Expressions.Count != 0) {
        wr.WriteLine();
        Indent(indent);
        wr.Write("decreases");
        if (decs.HasAttributes()) {
          PrintAttributes(decs.Attributes);
        }
        wr.Write(" ");
        PrintExpressionList(decs.Expressions, true);
      }
    }

    internal void PrintFrameSpecLine(string kind, List<FrameExpression> ee, int indent, Attributes attrs) {
      Contract.Requires(kind != null);
      Contract.Requires(cce.NonNullElements(ee));
      if (ee != null && ee.Count != 0) {
        wr.WriteLine();
        Indent(indent);
        wr.Write("{0}", kind);
        if (attrs != null) {
          PrintAttributes(attrs);
        }
        wr.Write(" ");
        PrintFrameExpressionList(ee);
      }
    }

    internal void PrintSpec(string kind, List<AttributedExpression> ee, int indent) {
      Contract.Requires(kind != null);
      Contract.Requires(ee != null);
      if (printMode == PrintModes.NoGhost) { return; }
      foreach (AttributedExpression e in ee) {
        Contract.Assert(e != null);
        wr.WriteLine();
        Indent(indent);
        wr.Write("{0}", kind);
        PrintAttributedExpression(e);
      }
    }

    void PrintAttributedExpression(AttributedExpression e) {
      Contract.Requires(e != null);

      if (e.HasAttributes()) {
        PrintAttributes(e.Attributes);
      }

      wr.Write(" ");
      if (e.Label != null) {
        wr.Write("{0}: ", e.Label.Name);
      }
      PrintExpression(e.E, true);
    }

    // ----------------------------- PrintType -----------------------------

    public void PrintType(Type ty) {
      Contract.Requires(ty != null);
      wr.Write(ty.TypeName(options, null, true));
    }

    public void PrintType(string prefix, Type ty) {
      Contract.Requires(prefix != null);
      Contract.Requires(ty != null);
      if (options.DafnyPrintResolvedFile != null) {
        ty = ty.Normalize();
      }
      string s = ty.TypeName(options, null, true);
      if (!(ty is TypeProxy) && !s.StartsWith("_")) {
        wr.Write("{0}{1}", prefix, s);
      }
    }

    public string TPCharacteristicsSuffix(TypeParameter.TypeParameterCharacteristics characteristics) {
      string s = null;
      if (characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Required ||
        (characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.InferredRequired && options.DafnyPrintResolvedFile != null)) {
        s = "==";
      }
      if (characteristics.HasCompiledValue) {
        var prefix = s == null ? "" : s + ",";
        s = prefix + "0";
      } else if (characteristics.IsNonempty) {
        var prefix = s == null ? "" : s + ",";
        s = prefix + "00";
      }
      if (characteristics.ContainsNoReferenceTypes) {
        var prefix = s == null ? "" : s + ",";
        s = prefix + "!new";
      }
      if (s == null) {
        return "";
      } else {
        return "(" + s + ")";
      }
    }

    bool ShowType(Type t) {
      Contract.Requires(t != null);
      return !(t is TypeProxy) || options.DafnyPrintResolvedFile != null;
    }

    // ----------------------------- PrintStatement -----------------------------

    /// <summary>
    /// Prints from the current position of the current line.
    /// If the statement requires several lines, subsequent lines are indented at "indent".
    /// No newline is printed after the statement.
    /// </summary>
    public void PrintStatement(Statement stmt, int indent) {
      Contract.Requires(stmt != null);

      if (stmt.IsGhost && printMode == PrintModes.NoGhost) { return; }
      for (LList<Label> label = stmt.Labels; label != null; label = label.Next) {
        if (label.Data.Name != null) {
          wr.WriteLine("label {0}:", label.Data.Name);
          Indent(indent);
        }
      }

      if (stmt is PredicateStmt) {
        if (printMode == PrintModes.NoGhost) { return; }
        Expression expr = ((PredicateStmt)stmt).Expr;
        var assertStmt = stmt as AssertStmt;
        var expectStmt = stmt as ExpectStmt;
        wr.Write(assertStmt != null ? "assert" :
                 expectStmt != null ? "expect" :
                 "assume");
        if (stmt.Attributes != null) {
          PrintAttributes(stmt.Attributes);
        }
        wr.Write(" ");
        if (assertStmt != null && assertStmt.Label != null) {
          wr.Write("{0}: ", assertStmt.Label.Name);
        }
        PrintExpression(expr, true);
        if (assertStmt != null && assertStmt.Proof != null) {
          wr.Write(" by ");
          PrintStatement(assertStmt.Proof, indent);
        } else if (expectStmt != null && expectStmt.Message != null) {
          wr.Write(", ");
          PrintExpression(expectStmt.Message, true);
        } else {
          wr.Write(";");
        }

      } else if (stmt is PrintStmt) {
        PrintStmt s = (PrintStmt)stmt;
        wr.Write("print");
        PrintAttributeArgs(s.Args, true);
        wr.Write(";");

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        wr.Write("reveal ");
        var sep = "";
        foreach (var e in s.Exprs) {
          wr.Write(sep);
          sep = ", ";
          if (RevealStmt.SingleName(e) != null) {
            // this will do the printing correctly for labels (or label-lookalikes) like 00_023 (which by PrintExpression below would be printed as 23)
            wr.Write(RevealStmt.SingleName(e));
          } else {
            PrintExpression(e, true);
          }
        }
        wr.Write(";");

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          wr.Write($"{s.Kind} {s.TargetLabel.val};");
        } else {
          for (int i = 0; i < s.BreakAndContinueCount - 1; i++) {
            wr.Write("break ");
          }
          wr.Write($"{s.Kind};");
        }

      } else if (stmt is ProduceStmt) {
        var s = (ProduceStmt)stmt;
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

      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        PrintExpression(s.Lhs, true);
        wr.Write(" := ");
        PrintRhs(s.Rhs);
        wr.Write(";");

      } else if (stmt is DividedBlockStmt) {
        var sbs = (DividedBlockStmt)stmt;
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
        wr.Write("if");
        PrintAttributes(s.Attributes);
        if (s.UsesOptionalBraces) {
          wr.Write(" {");
        }
        PrintAlternatives(indent + (s.UsesOptionalBraces ? IndentAmount : 0), s.Alternatives);
        if (s.UsesOptionalBraces) {
          wr.WriteLine();
          Indent(indent);
          wr.Write("}");
        }
      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        PrintWhileStatement(indent, s, false, false);
      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        wr.Write("while");
        PrintAttributes(s.Attributes);
        PrintSpec("invariant", s.Invariants, indent + IndentAmount);
        PrintDecreasesSpec(s.Decreases, indent + IndentAmount);
        PrintFrameSpecLine("modifies", s.Mod.Expressions, indent + IndentAmount, s.Mod.Attributes);
        bool hasSpecs = s.Invariants.Count != 0 || (s.Decreases.Expressions != null && s.Decreases.Expressions.Count != 0) || s.Mod.Expressions != null;
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

      } else if (stmt is ForLoopStmt) {
        var s = (ForLoopStmt)stmt;
        PrintForLoopStatement(indent, s);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        if (options.DafnyPrintResolvedFile != null && s.ForallExpressions != null) {
          foreach (var expr in s.ForallExpressions) {
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

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        PrintModifyStmt(indent, s, false);

      } else if (stmt is CalcStmt) {
        CalcStmt s = (CalcStmt)stmt;
        if (printMode == PrintModes.NoGhost) { return; }   // Calcs don't get a "ghost" attribute, but they are.
        wr.Write("calc");
        PrintAttributes(stmt.Attributes);
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
            Indent(indent);  // this lines up with the "calc"
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
      } else if (stmt is NestedMatchStmt) {
        // Print ResolvedStatement, if present, as comment
        var s = (NestedMatchStmt)stmt;

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
          wr.Write("match");
          PrintAttributes(s.Attributes);
          wr.Write(" ");
          PrintExpression(s.Source, false);
          if (s.UsesOptionalBraces) {
            wr.Write(" {");
          }
          int caseInd = indent + (s.UsesOptionalBraces ? IndentAmount : 0);
          foreach (NestedMatchCaseStmt mc in s.Cases) {
            wr.WriteLine();
            Indent(caseInd);
            wr.Write("case");
            PrintAttributes(mc.Attributes);
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
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        wr.Write("match");
        PrintAttributes(s.Attributes);
        wr.Write(" ");
        PrintExpression(s.Source, false);
        if (s.UsesOptionalBraces) {
          wr.Write(" {");
        }

        int caseInd = indent + (s.UsesOptionalBraces ? IndentAmount : 0);
        foreach (MatchCaseStmt mc in s.Cases) {
          wr.WriteLine();
          Indent(caseInd);
          wr.Write("case");
          PrintAttributes(mc.Attributes);
          wr.Write(" ");
          if (!mc.Ctor.Name.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
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

      } else if (stmt is ConcreteUpdateStatement) {
        var s = (ConcreteUpdateStatement)stmt;
        string sep = "";
        foreach (var lhs in s.Lhss) {
          wr.Write(sep);
          PrintExpression(lhs, true);
          sep = ", ";
        }
        if (s.Lhss.Count > 0) {
          wr.Write(" ");
        }
        PrintUpdateRHS(s, indent);
        wr.Write(";");

      } else if (stmt is CallStmt) {
        // Most calls are printed from their concrete syntax given in the input. However, recursive calls to
        // prefix lemmas end up as CallStmt's by the end of resolution and they may need to be printed here.
        var s = (CallStmt)stmt;
        PrintExpression(s.MethodSelect, false);
        PrintActualArguments(s.Bindings, s.Method.Name, null);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        if (s.Locals.Exists(v => v.IsGhost) && printMode == PrintModes.NoGhost) { return; }
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
            PrintAttributes(local.Attributes);
          }
          wr.Write(" {0}", local.DisplayName);
          PrintType(": ", local.OptionalType);
          sep = ",";
        }
        if (s.Update != null) {
          wr.Write(" ");
          PrintUpdateRHS(s.Update, indent);
        }
        wr.Write(";");

      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        if (s.tok is AutoGeneratedToken) {
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
        if (s.tok is AutoGeneratedToken) {
          wr.Write(" */");
        }

      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
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
          throw new cce.UnreachableException(); // unexpected skeleton statement
        }

      } else if (stmt is TryRecoverStatement haltRecoveryStatement) {
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
    /// Does not print LHS, nor the space one might want between LHS and RHS,
    /// because if there's no LHS, we don't want to start with a space
    /// </summary>
    void PrintUpdateRHS(ConcreteUpdateStatement s, int indent) {
      Contract.Requires(s != null);
      if (s is UpdateStmt) {
        var update = (UpdateStmt)s;
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
          wr.Write("assume");
          PrintAttributes(update.AssumeToken.Attrs);
          wr.Write(" ");
        }
        PrintExpression(update.Expr, true);
      } else if (s is AssignOrReturnStmt) {
        var stmt = (AssignOrReturnStmt)s;
        wr.Write(":-");
        if (stmt.KeywordToken != null) {
          wr.Write($" {stmt.KeywordToken.Token.val}");
          PrintAttributes(stmt.KeywordToken.Attrs);
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
      wr.Write("if");
      PrintAttributes(s.Attributes);
      wr.Write(" ");
      if (omitGuard) {
        wr.Write("... ");
      } else {
        PrintGuard(s.IsBindingGuard, s.Guard);
        wr.Write(" ");
      }
      PrintStatement(s.Thn, indent);
      if (s.Els != null) {
        wr.Write(" else");
        if (!(s.Els is IfStmt) && s.Els.Attributes != null) {
          PrintAttributes(s.Els.Attributes);
        }
        wr.Write(" ");
        PrintStatement(s.Els, indent);
      }
    }

    void PrintWhileStatement(int indent, WhileStmt s, bool omitGuard, bool omitBody) {
      Contract.Requires(0 <= indent);
      wr.Write("while");
      PrintAttributes(s.Attributes);
      wr.Write(" ");
      if (omitGuard) {
        wr.Write("...");
      } else {
        PrintGuard(false, s.Guard);
      }

      PrintSpec("invariant", s.Invariants, indent + IndentAmount);
      PrintDecreasesSpec(s.Decreases, indent + IndentAmount);
      PrintFrameSpecLine("modifies", s.Mod.Expressions, indent + IndentAmount, s.Mod.Attributes);
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
        wr.Write("case");
        PrintAttributes(alternative.Attributes);
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
      wr.Write("for");
      PrintAttributes(s.Attributes);
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
        PrintFrameSpecLine("modifies", s.Mod.Expressions, indent + IndentAmount, s.Mod.HasAttributes() ? s.Mod.Attributes : null);
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
        if (t.ArrayDimensions != null) {
          if (ShowType(t.EType)) {
            PrintType(t.EType);
          }
          if (options.DafnyPrintResolvedFile == null &&
            t.InitDisplay != null && t.ArrayDimensions.Count == 1 &&
            AutoGeneratedToken.Is(t.ArrayDimensions[0].tok)) {
            // elide the size
            wr.Write("[]");
          } else {
            string s = "[";
            foreach (Expression dim in t.ArrayDimensions) {
              Contract.Assume(dim != null);
              wr.Write(s);
              PrintExpression(dim, false);
              s = ", ";
            }
            wr.Write("]");
          }
          if (t.ElementInit != null) {
            wr.Write(" (");
            PrintExpression(t.ElementInit, false);
            wr.Write(")");
          } else if (t.InitDisplay != null) {
            wr.Write(" [");
            PrintExpressionList(t.InitDisplay, false);
            wr.Write("]");
          }
        } else if (t.Bindings == null) {
          PrintType(t.EType);
        } else {
          PrintType(t.Path);
          wr.Write("(");
          PrintBindings(t.Bindings, false);
          wr.Write(")");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
      }

      if (rhs.HasAttributes()) {
        PrintAttributes(rhs.Attributes);
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
            wr.Write("case");
            PrintAttributes(mc.Attributes);
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
            wr.Write("case");
            PrintAttributes(mc.Attributes);
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
        if (e.tok is AutoGeneratedToken) {
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
          PrintAttributes(e.Attributes);
          wr.Write(" :| ");
        }
        PrintExpressionList(e.RHSs, true);
        wr.Write(";");
        if (e.tok is AutoGeneratedToken) {
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

    private bool ParensNeeded(int opBindingStrength, int contextBindingStrength, bool fragileContext) {
      return opBindingStrength < contextBindingStrength ||
             (fragileContext && opBindingStrength == contextBindingStrength);
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
        wr.Write(((IdentifierExpr)expr).Name);

      } else if (expr is DatatypeValue) {
        var dtv = (DatatypeValue)expr;
        bool printParens;
        if (dtv.MemberName.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
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
        int opBindingStrength = 0x90;
        bool parensNeeded = !e.Lhs.IsImplicit && // KRML: I think that this never holds
          ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

        if (parensNeeded) { wr.Write("("); }
        if (!e.Lhs.IsImplicit) {
          PrintExpr(e.Lhs, opBindingStrength, false, false, !parensNeeded && isFollowedBySemicolon, -1, keyword);
          if (e.Lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            Contract.Assert(e.Lhs is NameSegment || e.Lhs is ExprDotName);  // these are the only expressions whose .Type can be ResolverType_Type
            if (options.DafnyPrintResolvedFile != null && options.PrintMode == PrintModes.Everything) {
              // The printing of e.Lhs printed the type arguments only if they were given explicitly in the input.
              var optionalTypeArgs = e.Lhs is NameSegment ns ? ns.OptTypeArguments : ((ExprDotName)e.Lhs).OptTypeArguments;
              if (optionalTypeArgs == null && e.Lhs.Resolved is Resolver_IdentifierExpr ri) {
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
        int opBindingStrength = 0x90;
        bool parensNeeded = !e.Lhs.IsImplicit &&  // KRML: I think that this never holds
          ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

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
        int opBindingStrength = 0x90;
        bool parensNeeded = !e.Obj.IsImplicit &&
          ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

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
        int opBindingStrength = 0x90;
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
        int opBindingStrength = 0x90;
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
        int opBindingStrength = 0x90;
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
        int opBindingStrength = 0x90;
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
        int opBindingStrength = 0x90;
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
        int opBindingStrength = 0x90;
        bool parensNeeded = !(e.Receiver.IsImplicit) &&
          ParensNeeded(opBindingStrength, contextBindingStrength, fragileContext);

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
        PrintExpression(e.E, false);
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
        } else {
          Contract.Assert(e.Op != UnaryOpExpr.Opcode.Fresh); // this is handled is "is FreshExpr" case above
          // Prefix operator.
          // determine if parens are needed
          string op;
          int opBindingStrength;
          switch (e.Op) {
            case UnaryOpExpr.Opcode.Not:
              op = "!"; opBindingStrength = 0x80; break;
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
        int opBindingStrength = 0x70;
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
            opBindingStrength = 0x48; fragileRightContext = true; break;
          case BinaryExpr.Opcode.Add: {
              opBindingStrength = 0x40;
              var t1 = e.E1.Type;
              fragileRightContext = t1 == null || !(t1.IsIntegerType || t1.IsRealType || t1.IsBigOrdinalType || t1.IsBitVectorType);
              break;
            }
          case BinaryExpr.Opcode.Sub:
            opBindingStrength = 0x40; fragileRightContext = true; break;
          case BinaryExpr.Opcode.Mul: {
              opBindingStrength = 0x50;
              var t1 = e.E1.Type;
              fragileRightContext = t1 == null || !(t1.IsIntegerType || t1.IsRealType || t1.IsBigOrdinalType || t1.IsBitVectorType);
              break;
            }
          case BinaryExpr.Opcode.Div:
          case BinaryExpr.Opcode.Mod:
            opBindingStrength = 0x50; fragileRightContext = true; break;
          case BinaryExpr.Opcode.BitwiseAnd:
            opBindingStrength = 0x60; break;
          case BinaryExpr.Opcode.BitwiseOr:
            opBindingStrength = 0x61; break;
          case BinaryExpr.Opcode.BitwiseXor:
            opBindingStrength = 0x62; break;
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
            var opBindingStrength = 0x30;
            var fragileLeftContext = true;
            var fragileRightContext = true;

            int opBS = opBindingStrength & 0xF8;
            int ctxtBS = contextBindingStrength & 0xF8;
            bool parensNeeded = opBS < ctxtBS ||
              (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

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
        int opBindingStrength = 0x30;
        int opBS = opBindingStrength & 0xF8;
        int ctxtBS = contextBindingStrength & 0xF8;
        bool parensNeeded = opBS < ctxtBS ||
          (opBS == ctxtBS && (opBindingStrength != contextBindingStrength || fragileContext));

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
        if (e.tok is AutoGeneratedToken) {
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
          PrintAttributes(e.Attributes);
          wr.Write(" :| ");
        }
        PrintExpressionList(e.RHSs, true);
        wr.Write("; ");
        if (e.tok is AutoGeneratedToken) {
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
        var readsPrefix = " reads ";
        foreach (var read in e.Reads) {
          wr.Write(readsPrefix);
          PrintExpression(read.E, false);
          readsPrefix = ", ";
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
        PrintExpression(ite.Test, false);
        wr.Write(" then ");
        PrintExpression(ite.Thn, false);
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
        int opBindingStrength = 0x80;
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
          wr.Write(" case");
          PrintAttributes(mc.Attributes);
          wr.Write(" ");
          PrintExtendedPattern(mc.Pat);
          wr.Write(" => ");
          PrintExpression(mc.Body, isRightmost && isLastCase, !parensNeeded && isFollowedBySemicolon);
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
      } else if (expr is Translator.BoogieWrapper) {
        wr.Write("[BoogieWrapper]");  // this is somewhat unexpected, but we can get here if the /trace switch is used, so it seems best to cover this case here
      } else if (expr is Translator.BoogieFunctionCall) {
        wr.Write("[BoogieFunctionCall]");  // this prevents debugger watch window crash
      } else if (expr is Resolver_IdentifierExpr) {
        wr.Write("[Resolver_IdentifierExpr]");  // we can get here in the middle of a debugging session
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
        if (pat.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
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
          if (idPat.Id.StartsWith(BuiltIns.TupleTypeCtorNamePrefix)) {
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
    void PrintExpressionPairList(List<ExpressionPair> exprs) {
      Contract.Requires(exprs != null);
      string sep = "";
      foreach (ExpressionPair p in exprs) {
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
  }
}
