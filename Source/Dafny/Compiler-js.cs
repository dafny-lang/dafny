//-----------------------------------------------------------------------------
//
// Copyright (C) Amazon.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using System.Diagnostics;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class JavaScriptCompiler : Compiler {
    public JavaScriptCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    public override string TargetLanguage => "JavaScript";

    protected override void EmitHeader(Program program, TargetWriter wr) {
      wr.WriteLine("// Dafny program {0} compiled into JavaScript", program.Name);
      wr.WriteLine(@"
let _dafny = (function() {
  let $module = {};
  $module.Tuple = class Tuple extends Array {
    constructor(...elems) {
      super(...elems);
    }
    toString() {
      return ""("" + super.toString() + "")"";
    }
  }
 return $module;
})();
");
    }

    public override void EmitCallToMain(Method mainMethod, TextWriter wr) {
      wr.WriteLine("{0}.{1}();", mainMethod.EnclosingClass.FullCompileName, IdName(mainMethod));
    }
      
    protected override BlockTargetWriter CreateModule(string moduleName, TargetWriter wr) {
      var w = wr.NewBigBlock(string.Format("let {0} = (function()", moduleName), ")(); // end of module " + moduleName);
      w.Indent();
      w.WriteLine("let $module = {};");
      w.BodySuffix = string.Format("{0}return $module;{1}", w.IndentString, w.NewLine);
      return w;
    }

    protected override BlockTargetWriter CreateClass(string name, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, out TargetWriter fieldsWriter, TargetWriter wr) {
      wr.Indent();
      var w = wr.NewBlock(string.Format("$module.{0} = class {0}", name), ";");
      w.Indent();
      fieldsWriter = w.NewBlock("constructor ()");
      return w;
    }

    protected override BlockTargetWriter CreateTrait(string name, List<Type>/*?*/ superClasses, Bpl.IToken tok, out TargetWriter fieldsWriter, out TargetWriter staticMemberWriter, TargetWriter wr) {
      wr.Indent();
      var w = wr.NewBlock(string.Format("$module.{0} = class {0}", IdProtect(name)), ";");
      w.Indent();
      fieldsWriter = w.NewBlock("constructor ()");
      staticMemberWriter = w;
      return w;
    }

    protected override void DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
      // $module.Dt = class Dt {
      //   constructor(tag) {
      //     this.$tag = tag;
      //   }
      //   static create_Ctor0(field0, field1, ...) {
      //     let $dt = new Dt(0);
      //     $dt.field0 = field0;
      //     $dt.field1 = field1;
      //     ...
      //     return $dt;
      //   }
      //   static create_Ctor1(...) {
      //     let $dt = new Dt(1);
      //     ...
      //   }
      //   ...
      //
      //   get is_Ctor0 { return this.$tag == 0; }
      //   get is_Ctor1 { return this.$tag == 1; }
      //   ...
      //
      //   toString() {
      //     ...
      //   }
      // }
      // TODO: need Default member (also for co-datatypes)
      // TODO: need equality methods
      // TODO: if HasFinitePossibleValues, need enumerator of values

      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);

      wr.Indent();
      // from here on, write everything into the new block created here:
      wr = wr.NewNamedBlock("$module.{0} = class {0}", DtT_protected);

      wr.Indent();
      wr.WriteLine("constructor(tag) { this.$tag = tag; }");


      // query properties
      var i = 0;
      foreach (var ctor in dt.Ctors) {
        // collect the names of non-ghost arguments
        var argNames = new List<string>();
        foreach (var formal in ctor.Formals) {
          if (!formal.IsGhost) {
            argNames.Add(formal.CompileName);
          }
        }
        // static create_Ctor0(params) { return {$tag:0, p0: pararms0, p1: params1, ...}; }
        wr.Indent();
        wr.Write("static create_{0}(", ctor.CompileName);
        wr.Write(Util.Comma(argNames, nm => nm));
        var w = wr.NewBlock(")");
        w.Indent();
        w.WriteLine("let $dt = new Dt({0});", i);
        foreach (var arg in argNames) {
          w.Indent();
          w.WriteLine("$dt.{0} = {0};", arg);
        }
        w.Indent();
        w.WriteLine("return $dt;");
        i++;
      }

      // query properties
      i = 0;
      foreach (var ctor in dt.Ctors) {
        // get is_Ctor0() { return _D is Dt_Ctor0; }
        wr.Indent();
        wr.WriteLine("get is_{0}() {{ return this.$tag === {1}; }}", ctor.CompileName, i);
        i++;
      }

      if (dt is IndDatatypeDecl && !(dt is TupleTypeDecl)) {
        wr.Indent();
        var w = wr.NewBlock("toString()");
        i = 0;
        foreach (var ctor in dt.Ctors) {
          w.Indent();
          var cw = w.NewBlock(string.Format("if (this.$tag == {0})", i), " else");
          cw.SetBraceStyle(BlockTargetWriter.BraceStyle.Space, BlockTargetWriter.BraceStyle.Space);
          w.SuppressIndent();
          cw.Indent();
          cw.Write("return \"{0}\"", ctor.Name);
          var sep = " + \"(\" + ";
          var anyFormals = false;
          foreach (var arg in ctor.Formals) {
            if (!arg.IsGhost) {
              anyFormals = true;
              cw.Write("{0}this.{1}.toString()", sep, arg.CompileName);
              sep = " + \", \" + ";
            }
          }
          if (anyFormals) {
            cw.Write(" + \")\"");
          }
          cw.WriteLine(";");
          i++;
        }
        w = w.NewBlock("");
        w.Indent();
        w.WriteLine("return \"<unexpected>\";");
      }
    }

    protected override BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody, TargetWriter wr) {
      if (!createBody) {
        return null;
      }
      wr.Indent();
      wr.Write("{0}{1}(", m.IsStatic ? "static " : "", IdName(m));
      int nIns = WriteFormals("", m.Ins, wr);
      var w = wr.NewBlock(")");

      if (!m.IsStatic) {
        w.Indent(); w.WriteLine("let _this = this;");
      }
      if (m.IsTailRecursive) {
        w.Indent();
        w = w.NewBlock("TAIL_CALL_START: while (true)");
      }
      var r = new TargetWriter(w.IndentLevel);
      EmitReturn(m.Outs, r);
      w.BodySuffix = r.ToString();
      return w;
    }

    protected override BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member, TargetWriter wr) {
      if (!createBody) {
        return null;
      }
      wr.Indent();
      wr.Write("{0}{1}(", isStatic ? "static " : "", name);
      int nIns = WriteFormals("", formals, wr);
      var w = wr.NewBlock(")", ";");
      if (!isStatic) {
        w.Indent(); w.WriteLine("let _this = this;");
      }
      return w;
    }

    protected override BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, TargetWriter wr) {
      if (createBody) {
        wr.Indent();
        wr.Write("{0}get {1}()", isStatic ? "static " : "", name);
        var w = wr.NewBlock("", ";");
        if (!isStatic) {
          w.Indent(); w.WriteLine("let _this = this;");
        }
        return w;
      } else {
        return null;
      }
    }

    protected override BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, out TargetWriter setterWriter, TargetWriter wr) {
      if (createBody) {
        wr.Indent();
        wr.Write("{0}get {1}()", isStatic ? "static " : "", name);
        var wGet = wr.NewBlock("", ";");
        if (!isStatic) {
          wGet.Indent(); wGet.WriteLine("let _this = this;");
        }

        wr.Indent();
        wr.Write("{0}set {1}()", isStatic ? "static " : "", name);
        var wSet = wr.NewBlock("", ";");
        if (!isStatic) {
          wSet.Indent(); wSet.WriteLine("let _this = this;");
        }

        setterWriter = wSet;
        return wGet;
      } else {
        setterWriter = null;
        return null;
      }
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("continue TAIL_CALL_START;");
    }

    public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "'D'";
      } else if (xType is IntType || xType is BigOrdinalType || xType is RealType || xType is BitvectorType) {
        return "0";
      } else if (xType is CollectionType) {
        return TypeName(xType, wr, tok) + ".Empty";
      }

      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        return "Dafny.Helpers.Default<" + TypeName_UDT(udt.FullCompileName, udt.TypeArgs, wr, udt.tok) + ">()";
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(udt.FullCompileName, udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(udt.FullCompileName, udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return string.Format("null)");
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("function () {{ return {0}; }}", rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            return "[]";
          } else {
            // non-null (non-array) type
            // even though the type doesn't necessarily have a known initializer, it could be that the the compiler needs to
            // lay down some bits to please the C#'s compiler's different definite-assignment rules.
            return string.Format("default({0})", TypeName(xType, wr, udt.tok));
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return "null";
        }
      } else if (cl is DatatypeDecl) {
        var s = "@" + udt.FullCompileName;
        var rc = cl;
        if (DafnyOptions.O.IronDafny &&
            !(xType is ArrowType) &&
            rc != null &&
            rc.Module != null &&
            !rc.Module.IsDefaultModule) {
          s = "@" + rc.FullCompileName;
        }
        if (udt.TypeArgs.Count != 0) {
          s += "<" + TypeNames(udt.TypeArgs, wr, udt.tok) + ">";
        }
        return string.Format("new {0}()", s);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Requires(fullCompileName != null);
      Contract.Requires(typeArgs != null);
      string s = IdProtect(fullCompileName);
      return s;
    }

    // ----- Declarations -------------------------------------------------------------

    protected override void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("this.{0} = {1};", name, rhs);
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      if (isInParam) {
        wr.Write("{0}{1}", prefix, name);
        return true;
      } else {
        return false;
      }
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken tok, string/*?*/ rhs, TargetWriter wr) {
      wr.Indent();
      wr.Write("let {0}", name);
      if (rhs != null) {
        wr.Write(" = {0}", rhs);
      }
      wr.WriteLine(";");
    }

    protected override void DeclareLocalVar(string name, Type type, Bpl.IToken tok, Expression rhs, bool inLetExprBody, TargetWriter wr) {
      wr.Indent();
      wr.Write("let {0} = ", name);
      TrExpr(rhs, wr, inLetExprBody);
      wr.WriteLine(";");
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override void DeclareOutCollector(string collectorVarName, TargetWriter wr) {
      wr.Write("let {0} = ", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, rhs, wr);
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, TargetWriter wr) {
      if (actualOutParamNames.Count == 1) {
        EmitAssignment(actualOutParamNames[0], outCollector, wr);
      } else {
        for (int i = 0; i < actualOutParamNames.Count; i++) {
          wr.Indent();
          wr.WriteLine("{0} = {1}[{2}];", actualOutParamNames[i], outCollector, i);
        }
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      // emit nothing
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok) {
      return "let " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Indent();
      wr.Write("process.stdout.write(");
      TrParenExpr(arg, wr, false);
      wr.WriteLine(".toString());");
    }

    protected override void EmitReturn(List<Formal> outParams, TargetWriter wr) {
      wr.Indent();
      if (outParams.Count == 0) {
        wr.WriteLine("return;");
      } else if (outParams.Count == 1) {
        wr.WriteLine("return {0};", IdName(outParams[0]));
      } else {
        wr.WriteLine("return [{0}];", Util.Comma(outParams, IdName));
      }
    }

    protected override void EmitBreak(string label, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("break {0};", label);
    }

    protected override void EmitYield(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("yield null;");
    }

    protected override void EmitAbsurd(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("throw new Error('unexpected control point');");
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr) {
      wr.Write("new {0}()", TypeName(type, wr, tok));
    }

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

    protected override void EmitThis(TargetWriter wr) {
      wr.Write("_this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string dtName, string ctorName, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      if (dt is TupleTypeDecl) {
        wr.Write("new _dafny.Tuple({0})", arguments);
      } else {
        wr.Write("{0}.{1}.create_{2}({3})", dt.Module.CompileName, dtName, ctorName, arguments);
      }
    }

    protected override void EmitMemberSelect(MemberDecl member, bool isLValue, TargetWriter wr) {
      if (isLValue && member is ConstantField) {
        wr.Write("._{0}", member.CompileName);
      } else if (member is DatatypeDestructor dtor && dtor.EnclosingClass is TupleTypeDecl) {
        wr.Write("[{0}]", dtor.Name);
      } else {
        wr.Write(".{0}", IdName(member));
      }
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
          return nodeProcess.ExitCode == 0;
        }
      } catch (System.ComponentModel.Win32Exception e) {
        outputWriter.WriteLine("Error: Unable to start node.js ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
    }
  }
}
