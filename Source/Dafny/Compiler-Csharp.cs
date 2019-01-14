//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.CodeDom.Compiler;
using System.Reflection;
using System.Collections.ObjectModel;
using Bpl = Microsoft.Boogie;



namespace Microsoft.Dafny
{
  public class CsharpCompiler : Compiler
  {
    public CsharpCompiler(ErrorReporter reporter)
    : base(reporter) {
    }

    public override string TargetLanguage => "C#";

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

    protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr) {
      wr = CreateModule("Dafny", wr);
      wr.Indent();
      wr = wr.NewNamedBlock("internal class ArrayHelpers");
      foreach (var decl in builtIns.SystemModule.TopLevelDecls) {
        if (decl is ArrayClassDecl) {
          int dims = ((ArrayClassDecl)decl).Dims;

          // Here is an overloading of the method name, where there is an initialValue parameter
          // public static T[,] InitNewArray2<T>(T z, BigInteger size0, BigInteger size1) {
          wr.Indent();
          wr.Write("public static T[");
          wr.RepeatWrite(dims, "", ",");
          wr.Write("] InitNewArray{0}<T>(T z, ", dims);
          wr.RepeatWrite(dims, "BigInteger size{0}", ", ");
          wr.Write(")");

          var w = wr.NewBlock("");
          // int s0 = (int)size0;
          for (int i = 0; i < dims; i++) {
            w.Indent();
            w.WriteLine("int s{0} = (int)size{0};", i);
          }
          // T[,] a = new T[s0, s1];
          w.Indent();
          w.Write("T[");
          w.RepeatWrite(dims, "", ",");
          w.Write("] a = new T[");
          w.RepeatWrite(dims, "s{0}", ",");
          w.WriteLine("];");
          // for (int i0 = 0; i0 < s0; i0++)
          //   for (int i1 = 0; i1 < s1; i1++)
          for (int i = 0; i < dims; i++) {
            w.IndentExtra(i);
            w.WriteLine("for (int i{0} = 0; i{0} < s{0}; i{0}++)", i);
          }
          // a[i0,i1] = z;
          w.IndentExtra(dims);
          w.Write("a[");
          w.RepeatWrite(dims, "i{0}", ",");
          w.WriteLine("] = z;");
          // return a;
          w.Indent();
          w.WriteLine("return a;");
        }
      }
    }

    protected override BlockTargetWriter CreateModule(string moduleName, TargetWriter wr) {
      var s = string.Format("namespace @{0}", moduleName);
      return wr.NewBigBlock(s, " // end of " + s);
    }

    string TypeParameters(List<TypeParameter> targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      return Util.Comma(targs, tp => "@" + tp.CompileName);
    }

    protected override BlockTargetWriter CreateClass(string name, List<TypeParameter>/*?*/ typeParameters, List<Type>/*?*/ superClasses, Bpl.IToken tok, out TargetWriter fieldsWriter, TargetWriter wr) {
      wr.Indent();
      wr.Write("public partial class {0}", name);
      if (typeParameters != null && typeParameters.Count != 0) {
        wr.Write("<{0}>", TypeParameters(typeParameters));
      }
      if (superClasses != null) {
        string sep = " : ";
        foreach (var trait in superClasses) {
          wr.Write("{0}{1}", sep, TypeName(trait, wr, tok));
          sep = ", ";
        }
      }
      var w = wr.NewBlock("");
      fieldsWriter = w;
      return w;
    }

    protected override void EmitDatatypeHeader(DatatypeDecl dt, TargetWriter wr) {
      wr.Indent();
      wr.Write("public abstract class Base_{0}", dt.CompileName);
      if (dt.TypeArgs.Count != 0) {
        wr.Write("<{0}>", TypeParameters(dt.TypeArgs));
      }
      wr.WriteLine(" { }");
    }

    protected override BlockTargetWriter/*?*/ CreateMethod(Method m, TargetWriter wr) {
      var hasDllImportAttribute = ProcessDllImport(m, wr);
      string targetReturnTypeReplacement = null;
      if (hasDllImportAttribute) {
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

      wr.Indent();
      wr.Write("public {0}{1}{3} @{2}", m.IsStatic ? "static " : "", hasDllImportAttribute ? "extern " : "", m.CompileName, targetReturnTypeReplacement ?? "void");
      if (m.TypeArgs.Count != 0) {
        wr.Write("<{0}>", TypeParameters(m.TypeArgs));
      }
      wr.Write("(");
      int nIns = WriteFormals("", m.Ins, wr);
      if (targetReturnTypeReplacement == null) {
        WriteFormals(nIns == 0 ? "" : ", ", m.Outs, wr);
      }

      if (hasDllImportAttribute) {
        wr.WriteLine(");");
        return null;
      } else {
        var w = wr.NewBlock(")");
        w.SetBraceStyle(BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        if (m.IsTailRecursive) {
          if (!m.IsStatic) {
            w.Indent(); w.WriteLine("var _this = this;");
          }
          w.IndentExtra(-1); w.WriteLine("TAIL_CALL_START: ;");
        }
        return w;
      }
    }

    protected override BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, MemberDecl member, TargetWriter wr) {
      var hasDllImportAttribute = ProcessDllImport(member, wr);

      wr.Indent();
      wr.Write("public {0}{1}{2} {3}", isStatic ? "static " : "", hasDllImportAttribute ? "extern " : "", TypeName(resultType, wr, tok), name);
      if (typeArgs != null && typeArgs.Count != 0) {
        wr.Write("<{0}>", TypeParameters(typeArgs));
      }
      wr.Write("(");
      WriteFormals("", formals, wr);
      if (hasDllImportAttribute) {
        wr.WriteLine(");");
        return null;
      } else {
        var w = wr.NewBlock(")");
        if (formals.Count > 1) {
          w.SetBraceStyle(BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        }
        return w;
      }
    }

    /// <summary>
    /// Process the declaration's "dllimport" attribute, if any, by emitting the corresponding .NET custom attribute.
    /// Returns "true" if the declaration has an active "dllimport" attribute; "false", otherwise.
    /// </summary>
    public bool ProcessDllImport(MemberDecl decl, TargetWriter wr) {
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
          wr.Indent();
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

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("goto TAIL_CALL_START;");
    }

    public override string TypeInitializationValue(Type type, TextWriter/*?*/ wr, Bpl.IToken/*?*/ tok) {
      var xType = type.NormalizeExpandKeepConstraints();

      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "'D'";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "BigInteger.Zero";
      } else if (xType is RealType) {
        return "Dafny.BigRational.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : "BigInteger.Zero";
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
            return string.Format("(({0})null)", TypeName(xType, wr, udt.tok));
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) => rangeDefaultValue)
            return string.Format("(({0}) => {1})",
              Util.Comma(", ", udt.TypeArgs.Count - 1, i => string.Format("{0} x{1}", TypeName(udt.TypeArgs[i], wr, udt.tok), i)),
              rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            string typeNameSansBrackets, brackets;
            TypeName_SplitArrayName(udt.TypeArgs[0], wr, udt.tok, out typeNameSansBrackets, out brackets);
            return string.Format("new {0}[{1}]{2}", typeNameSansBrackets, Util.Comma(arrayClass.Dims, _ => "0"), brackets);
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
          return string.Format("({0})null", TypeName(xType, wr, udt.tok));
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
      if (typeArgs.Count != 0) {
        if (typeArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }
        s += "<" + TypeNames(typeArgs, wr, tok) + ">";
      }
      return s;
    }

    // ----- Declarations -------------------------------------------------------------

    protected override void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("public {3}{4}{0} {1} = {2};", TypeName(type, wr, tok), name, rhs,
        isStatic ? "static " : "",
        isConst ? "readonly " : "");
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      wr.Write("{0}{1}{2} {3}", prefix, isInParam ? "" : "out ", TypeName(type, wr, tok), name);
      return true;
    }

    protected override void DeclareLocalVar(string name, Type/*?*/ type, Bpl.IToken tok, string/*?*/ rhs, TargetWriter wr) {
      wr.Indent();
      wr.Write("{0} {1}", type != null ? TypeName(type, wr, tok) : "var", name);
      if (rhs != null) {
        wr.Write(" = {0}", rhs);
      }
      wr.WriteLine(";");
    }

    protected override void DeclareLocalVar(string name, Type type, Bpl.IToken tok, Expression rhs, bool inLetExprBody, TargetWriter wr) {
      wr.Indent();
      wr.Write("{0} {1} = ", TypeName(type, wr, tok), name);
      TrExpr(rhs, wr, inLetExprBody);
      wr.WriteLine(";");
    }

    protected override void DeclareOutCollector(string collectorVarName, TargetWriter wr) {
      wr.Write("var {0} = ", collectorVarName);
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      EmitAssignment(name, rhs, wr);
    }

    protected override void EmitActualOutArg(string actualOutParamName, TextWriter wr) {
      wr.Write("out {0}", actualOutParamName);
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) {
      return !DafnyOptions.O.DisallowExterns && Attributes.Contains(m.Attributes, "dllimport") && nonGhostOutCount == 1;
    }

    protected override void EmitOutParameterSplits(string outCollector, List<string> actualOutParamNames, TargetWriter wr) {
      Contract.Assert(actualOutParamNames.Count == 1);
      EmitAssignment(actualOutParamNames[0], outCollector, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      wr.Write("<" + TypeNames(typeArgs, wr, tok) + ">");
    }

    protected override string GenerateLhsDecl(string target, Type/*?*/ type, TextWriter wr, Bpl.IToken tok) {
      return (type != null ? TypeName(type, wr, tok) : "var") + " " + target;
    }

    // ----- Statements -------------------------------------------------------------

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Indent();
      wr.Write("System.Console.Write(");
      TrExpr(arg, wr, false);
      wr.WriteLine(");");
    }

    protected override void EmitReturn(List<Formal> outParams, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("return;");
    }

    protected override void EmitBreak(string label, TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("goto after_{0};", label);
    }

    protected override void EmitYield(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("yield return null;");
    }

    protected override void EmitAbsurd(TargetWriter wr) {
      wr.Indent();
      wr.WriteLine("throw new System.Exception();");
    }

    // ----- Expressions -------------------------------------------------------------

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt/*?*/ initCall, TargetWriter wr) {
      var ctor = initCall == null ? null : (Constructor)initCall.Method;  // correctness of cast follows from precondition of "EmitNew"
      wr.Write("new {0}(", TypeName(type, wr, tok));
      string q, n;
      if (ctor != null && ctor.IsExtern(out q, out n)) {
        // the arguments of any external constructor are placed here
        string sep = "";
        for (int i = 0; i < ctor.Ins.Count; i++) {
          Formal p = ctor.Ins[i];
          if (!p.IsGhost) {
            wr.Write(sep);
            TrExpr(initCall.Args[i], wr, false);
            sep = ", ";
          }
        }
      }
      wr.Write(")");
    }

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

    protected override string IdProtect(string name) {
      return "@" + name;
    }

    protected override void EmitThis(TargetWriter wr) {
      wr.Write(enclosingMethod != null && enclosingMethod.IsTailRecursive ? "_this" : "this");
    }

    // ----- Target compilation and execution -------------------------------------------------------------

    private class CSharpCompilationResult
    {
      public string immutableDllFileName;
      public string immutableDllPath;
      public CompilerResults cr;
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {

      compilationResult = null;

      if (!CodeDomProvider.IsDefinedLanguage("CSharp")) {
        outputWriter.WriteLine("Error: cannot compile, because there is no provider configured for input language CSharp");
        return false;
      }

      var provider = CodeDomProvider.CreateProvider("CSharp", new Dictionary<string, string> { { "CompilerVersion", "v4.0" } });
      var cp = new System.CodeDom.Compiler.CompilerParameters();
      cp.GenerateExecutable = hasMain;
      if (DafnyOptions.O.RunAfterCompile) {
        cp.GenerateInMemory = true;
      } else if (hasMain) {
        cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "exe");
        cp.GenerateInMemory = false;
      } else {
        cp.OutputAssembly = Path.ChangeExtension(dafnyProgramName, "dll");
        cp.GenerateInMemory = false;
      }
      // The nowarn numbers are the following:
      // * CS0164 complains about unreferenced labels
      // * CS0219/CS0168 is about unused variables
      // * CS1717 is about assignments of a variable to itself
      // * CS0162 is about unreachable code
      cp.CompilerOptions = "/debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168";
      cp.ReferencedAssemblies.Add("System.Numerics.dll");
      cp.ReferencedAssemblies.Add("System.Core.dll");
      cp.ReferencedAssemblies.Add("System.dll");

      var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location) + Path.DirectorySeparatorChar;
      if (DafnyOptions.O.UseRuntimeLib) {
        cp.ReferencedAssemblies.Add(libPath + "DafnyRuntime.dll");
      }

      var crx = new CSharpCompilationResult();
      crx.immutableDllFileName = "System.Collections.Immutable.dll";
      crx.immutableDllPath = libPath + crx.immutableDllFileName;

      if (DafnyOptions.O.Optimize) {
        cp.CompilerOptions += " /optimize /define:DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE";
        cp.ReferencedAssemblies.Add(crx.immutableDllPath);
        cp.ReferencedAssemblies.Add("System.Runtime.dll");
      }

      int numOtherSourceFiles = 0;
      if (otherFileNames.Count > 0) {
        foreach (var file in otherFileNames) {
          string extension = Path.GetExtension(file);
          if (extension != null) { extension = extension.ToLower(); }
          if (extension == ".cs") {
            numOtherSourceFiles++;
          } else if (extension == ".dll") {
            cp.ReferencedAssemblies.Add(file);
          }
        }
      }

      if (numOtherSourceFiles > 0) {
        string[] sourceFiles = new string[numOtherSourceFiles + 1];
        sourceFiles[0] = targetFilename;
        int index = 1;
        foreach (var file in otherFileNames) {
          string extension = Path.GetExtension(file);
          if (extension != null) { extension = extension.ToLower(); }
          if (extension == ".cs") {
            sourceFiles[index++] = file;
          }
        }
        crx.cr = provider.CompileAssemblyFromFile(cp, sourceFiles);
      } else {
        crx.cr = provider.CompileAssemblyFromSource(cp, targetProgramText);
      }

      if (crx.cr.Errors.Count != 0) {
        if (cp.GenerateInMemory) {
          outputWriter.WriteLine("Errors compiling program");
        } else {
          var assemblyName = Path.GetFileName(crx.cr.PathToAssembly);
          outputWriter.WriteLine("Errors compiling program into {0}", assemblyName);
        }
        foreach (var ce in crx.cr.Errors) {
          outputWriter.WriteLine(ce.ToString());
          outputWriter.WriteLine();
        }
        return false;
      }

      if (cp.GenerateInMemory) {
        outputWriter.WriteLine("Program compiled successfully");
      } else {
        var assemblyName = Path.GetFileName(crx.cr.PathToAssembly);
        outputWriter.WriteLine("Compiled assembly into {0}", assemblyName);
        if (DafnyOptions.O.Optimize) {
          var outputDir = Path.GetDirectoryName(dafnyProgramName);
          if (string.IsNullOrWhiteSpace(outputDir)) {
            outputDir = ".";
          }
          var destPath = outputDir + Path.DirectorySeparatorChar + crx.immutableDllFileName;
          File.Copy(crx.immutableDllPath, destPath, true);
          outputWriter.WriteLine("Copied /optimize dependency {0} to {1}", crx.immutableDllFileName, outputDir);
        }
      }

      compilationResult = crx;
      return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      object compilationResult, TextWriter outputWriter) {

      var crx = (CSharpCompilationResult)compilationResult;
      var cr = crx.cr;

      var assemblyName = Path.GetFileName(cr.PathToAssembly);
      var entry = cr.CompiledAssembly.EntryPoint;
      try {
        object[] parameters = entry.GetParameters().Length == 0 ? new object[] { } : new object[] { new string[0] };
        entry.Invoke(null, parameters);
        return true;
      } catch (System.Reflection.TargetInvocationException e) {
        outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
        outputWriter.WriteLine(e.InnerException.ToString());
      } catch (System.Exception e) {
        outputWriter.WriteLine("Error: Execution resulted in exception: {0}", e.Message);
        outputWriter.WriteLine(e.ToString());
      }
      return false;
    }
  }
}
