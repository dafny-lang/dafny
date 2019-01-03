//-----------------------------------------------------------------------------
//
// Copyright (C) Amazon.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using System.Diagnostics;

namespace Microsoft.Dafny {
  public class JavaScriptCompiler : Compiler {
    public JavaScriptCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    public override string TargetLanguage => "JavaScript";

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into JavaScript", program.Name);
    }

    public override void EmitCallToMain(Method mainMethod, TextWriter wr) {
      wr.WriteLine("{0}.{1}.{2}();", mainMethod.EnclosingClass.Module.CompileName, mainMethod.EnclosingClass.CompileName, mainMethod.CompileName);
    }
      
    protected override BlockTargetWriter CreateModule(TargetWriter wr, string moduleName) {
      return wr.NewBigBlock(string.Format("var {0} =", moduleName), " // end of module " + moduleName);
    }

    protected override BlockTargetWriter CreateClass(TargetWriter wr, ClassDecl cl) {
      return CreateInternalClass(wr, cl.CompileName);
    }
    protected override BlockTargetWriter CreateInternalClass(TargetWriter wr, string className) {
      var w = wr.NewBlock("{0}:", className);
      w.Footer = ",";
      return w;
    }

    protected override BlockTargetWriter CreateMethod(TargetWriter wr, Method m) {
      return wr.NewBlock("{0}: function()", m.CompileName);
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Indent();
      wr.Write("console.log(");
      TrExpr(arg, wr, false);
      wr.WriteLine(");");
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("null");
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        wr.Write("'{0}'", v == "\\0" ? "\\u0000" : v);  // JavaScript doesn't have a \0
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        // TODO: the string should be converted to a Dafny seq<char>
        TrStringLiteral(str, wr);
      } else if (AsNativeType(e.Type) != null) {
        wr.Write((BigInteger)e.Value + AsNativeType(e.Type).Suffix);
      } else if (e.Value is BigInteger) {
        // TODO: represent numbers more correctly (JavaScript's integers are bounded)
        wr.Write((BigInteger)e.Value);
      } else if (e.Value is Basetypes.BigDec) {
        var n = (Basetypes.BigDec)e.Value;
        if (0 <= n.Exponent) {
          wr.Write(n.Mantissa);
          for (int i = 0; i < n.Exponent; i++) {
            wr.Write("0");
          }
        } else {
          wr.Write("(");
          wr.Write(n.Mantissa);
          wr.Write("/1", n.Mantissa);
          for (int i = n.Exponent; i < 0; i++) {
            wr.Write("0");
          }
          wr.Write(")");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }

    protected override void TrStringLiteral(StringLiteralExpr str, TextWriter wr) {
      var s = (string)str.Value;
      var n = s.Length;
      wr.Write("\"");
      for (int i = 0; i < n; i++) {
        if (s[i] == '\\' && s[i+1] == '0') {
          wr.Write("\\u0000");
          i++;
        } else if (s[i] == '\n') {  // may appear in a verbatim string
          wr.Write("\\n");
        } else if (s[i] == '\r') {  // may appear in a verbatim string
          wr.Write("\\r");
        } else {
          wr.Write(s[i]);
        }
      }
      wr.Write("\"");
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      string args = "";
      if (targetFilename != null) {
        args += targetFilename;
        foreach (var s in otherFileNames) {
          args += " " + s;
        }
      } else {
        Contract.Assert(otherFileNames.Count == 0);  // according to the precondition
      }
      var psi = new ProcessStartInfo("node", args) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardInput = true,
        RedirectStandardOutput = false,
        RedirectStandardError = false,
      };

      try {
        using (var nodeProcess = Process.Start(psi)) {
          if (targetFilename == null) {
            nodeProcess.StandardInput.Write(targetProgramText);
            nodeProcess.StandardInput.Flush();
            nodeProcess.StandardInput.Close();
          }
          nodeProcess.WaitForExit();
        }
      } catch (System.ComponentModel.Win32Exception e) {
        outputWriter.WriteLine("Error: Unable to start node.js ({0}): {1}", psi.FileName, e.Message);
        return false;
      }

      return true;
    }
  }
}
