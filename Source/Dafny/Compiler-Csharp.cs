//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Text;


namespace Microsoft.Dafny {
  public class CsharpCompiler : Compiler {
    public CsharpCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into C#", program.Name);
      wr.WriteLine("// To recompile, use 'csc' with: /r:System.Numerics.dll");
      wr.WriteLine("// and choosing /target:exe or /target:library");
      wr.WriteLine("// You might also want to include compiler switches like:");
      wr.WriteLine("//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168");
      wr.WriteLine();
      wr.WriteLine("using System;");
      wr.WriteLine("using System.Numerics;");
      EmitDafnySourceAttribute(program, wr);

      if (!DafnyOptions.O.UseRuntimeLib) {
        ReadRuntimeSystem(wr);
      }
    }

    void EmitDafnySourceAttribute(Program program, TextWriter wr) {
      Contract.Requires(program != null);

      wr.WriteLine("[assembly: DafnyAssembly.DafnySourceAttribute(@\"");

      var strwr = new StringWriter();
      strwr.NewLine = wr.NewLine;
      new Printer(strwr, DafnyOptions.PrintModes.Everything).PrintProgram(program, true);

      wr.Write(strwr.GetStringBuilder().Replace("\"", "\"\"").ToString());
      wr.WriteLine("\")]");
      wr.WriteLine();
    }

    void ReadRuntimeSystem(TextWriter wr) {
      string codebase = cce.NonNull(System.IO.Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
      string path = System.IO.Path.Combine(codebase, "DafnyRuntime.cs");
      using (TextReader rd = new StreamReader(new FileStream(path, System.IO.FileMode.Open, System.IO.FileAccess.Read))) {
        while (true) {
          string s = rd.ReadLine();
          if (s == null)
            return;
          wr.WriteLine(s);
        }
      }
    }

    protected override BlockTargetWriter CreateModule(TargetWriter wr, string moduleName) {
      var s = string.Format("namespace @{0}", moduleName);
      return wr.NewBigBlock(s, " // end of " + s);
    }

    protected override BlockTargetWriter CreateClass(TargetWriter wr, ClassDecl cl) {
      var w = wr.NewBlock("public partial class @{0}", cl.CompileName);
      if (cl.TypeArgs.Count != 0) {
        w.AppendHeader("<{0}>", TypeParameters(cl.TypeArgs));
      }
      string sep = " : ";
      foreach (var trait in cl.TraitsTyp) {
        w.AppendHeader("{0}{1}", sep, TypeName(trait, w, cl.tok));
        sep = ", ";
      }
      return w;
    }
    protected override BlockTargetWriter CreateInternalClass(TargetWriter wr, string className) {
      var w = wr.NewBlock("internal class {0}", className);
      return w;
    }

    string/*!*/ TypeParameters(List<TypeParameter/*!*/>/*!*/ targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      return Util.Comma(targs, tp => "@" + tp.CompileName);
    }

    protected override BlockTargetWriter CreateMethod(TargetWriter wrx, Method m) {
      var wr = wrx.NewBlock("");
      wr.SetBraceStyle(BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);

      var dllSw = new StringWriter();
      var hasDllImportAttribute = ProcessDllImport(m, dllSw);
      wr.AppendHeader(dllSw.ToString());
      string targetReturnTypeReplacement = null;
      if (hasDllImportAttribute) {
        wr.AppendHeader(wrx.IndentString);
        foreach (var p in m.Outs) {
          if (!p.IsGhost) {
            if (targetReturnTypeReplacement == null) {
              targetReturnTypeReplacement = TypeName(p.Type, wr, p.tok);
            } else if (targetReturnTypeReplacement != null) {
              // there's more than one out-parameter, so bail
              targetReturnTypeReplacement = null;
              break;
            }
          }
        }
      }

      var sw = new StringWriter();
      sw.Write("public {0}{1}{3} @{2}", m.IsStatic ? "static " : "", hasDllImportAttribute ? "extern " : "", m.CompileName, targetReturnTypeReplacement ?? "void");
      if (m.TypeArgs.Count != 0) {
        sw.Write("<{0}>", TypeParameters(m.TypeArgs));
      }
      sw.Write("(");
      int nIns = WriteFormals("", m.Ins, sw);
      if (targetReturnTypeReplacement == null) {
        WriteFormals(nIns == 0 ? "" : ", ", m.Outs, sw);
      }
      sw.Write(")");
      wr.AppendHeader(sw.ToString());

      if (hasDllImportAttribute) {
        wr.DropBody();
        wr.SetBraceStyle(BlockTargetWriter.BraceStyle.Nothing, BlockTargetWriter.BraceStyle.Newline);
      }
      return wr;
    }

    /// <summary>
    /// Process the declaration's "dllimport" attribute, if any, by emitting the corresponding .NET custom attribute.
    /// Returns "true" if the declaration has an active "dllimport" attribute; "false", otherwise.
    /// </summary>
    public bool ProcessDllImport(MemberDecl decl, TextWriter wr) {
      Contract.Requires(decl != null);
      Contract.Requires(wr != null);

      var dllimportsArgs = Attributes.FindExpressions(decl.Attributes, "dllimport");
      if (!DafnyOptions.O.DisallowExterns && dllimportsArgs != null) {
        StringLiteralExpr libName = null;
        StringLiteralExpr entryPoint = null;
        if (dllimportsArgs.Count == 2) {
          libName = dllimportsArgs[0] as StringLiteralExpr;
          entryPoint = dllimportsArgs[1] as StringLiteralExpr;
        } else if (dllimportsArgs.Count == 1) {
          libName = dllimportsArgs[0] as StringLiteralExpr;
          // use the given name, not the .CompileName (if user needs something else, the user can supply it as a second argument to :dllimport)
          entryPoint = new StringLiteralExpr(decl.tok, decl.Name, false);
        }
        if (libName == null || entryPoint == null) {
          Error(decl.tok, "Expected arguments are {{:dllimport dllName}} or {{:dllimport dllName, entryPoint}} where dllName and entryPoint are strings: {0}", wr, decl.FullName);
        } else if ((decl is Method m && m.Body != null) || (decl is Function f && f.Body != null)) {
          Error(decl.tok, "A {0} declared with :dllimport is not allowed a body: {1}", wr, decl.WhatKind, decl.FullName);
        } else if (!decl.IsStatic) {
          Error(decl.tok, "A {0} declared with :dllimport must be static: {1}", wr, decl.WhatKind, decl.FullName);
        } else {
          wr.Write("[System.Runtime.InteropServices.DllImport(");
          TrStringLiteral(libName, wr);
          wr.Write(", EntryPoint=");
          TrStringLiteral(entryPoint, wr);
          wr.WriteLine(")]");
        }
        return true;
      }
      return false;
    }

    protected override void EmitMethodBodyPrelude(BlockTargetWriter wr, Method m) {
      if (m.IsTailRecursive) {
        if (!m.IsStatic) {
          wr.Indent(); wr.WriteLine("var _this = this;");
        }
        wr.IndentExtra(-1); wr.WriteLine("TAIL_CALL_START: ;");
      }
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Indent();
      wr.Write("System.Console.Write(");
      TrExpr(arg, wr, false);
      wr.WriteLine(");");
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        var cl = (e.Type.NormalizeExpand() as UserDefinedType)?.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          wr.Write("0");
        } else {
          wr.Write("({0})null", TypeName(e.Type, wr, e.tok));
        }
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        wr.Write("'{0}'", (string)e.Value);
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        wr.Write("{0}<char>.FromString(", DafnySeqClass);
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) != null) {
        wr.Write((BigInteger)e.Value + AsNativeType(e.Type).Suffix);
      } else if (e.Value is BigInteger) {
        BigInteger i = (BigInteger)e.Value;
        if (new BigInteger(int.MinValue) <= i && i <= new BigInteger(int.MaxValue)) {
          wr.Write("new BigInteger({0})", i);
        } else {
          wr.Write("BigInteger.Parse(\"{0}\")", i);
        }
      } else if (e.Value is Basetypes.BigDec) {
        var n = (Basetypes.BigDec)e.Value;
        if (0 <= n.Exponent) {
          wr.Write("new Dafny.BigRational(new BigInteger({0}", n.Mantissa);
          for (int i = 0; i < n.Exponent; i++) {
            wr.Write("0");
          }
          wr.Write("), BigInteger.One)");
        } else {
          wr.Write("new Dafny.BigRational(new BigInteger({0}), new BigInteger(1", n.Mantissa);
          for (int i = n.Exponent; i < 0; i++) {
            wr.Write("0");
          }
          wr.Write("))");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }
  }
}
