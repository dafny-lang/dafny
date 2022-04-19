using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Numerics;
using JetBrains.Annotations;
using ExtensionMethods;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace ExtensionMethods {
  using Microsoft.Dafny;
  public static class PythonExtensions {
    public static ConcreteSyntaxTree NewBlockPy(this ConcreteSyntaxTree tree, string header = "", string footer = "",
      BlockStyle open = BlockStyle.Newline,
      BlockStyle close = BlockStyle.Nothing) {
      return tree.NewBlock(header, footer, open, close);
    }
  }
}

namespace Microsoft.Dafny.Compilers {
  public class PythonCompiler : SinglePassCompiler {
    public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".py" };

    public override string TargetLanguage => "Python";
    public override string TargetExtension => "py";
    public override int TargetIndentSize => 4;

    public override string TargetBaseDir(string dafnyProgramName) =>
      $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-py";

    public override bool SupportsInMemoryCompilation => false;
    public override bool TextualTargetIsExecutable => true;

    public override IReadOnlySet<string> SupportedNativeTypes =>
      new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "number", "ulong", "long" };

    private readonly List<string> Imports = new List<string> { "_module" };

    const string DafnySetClass = "_dafny.Set";
    const string DafnyMultiSetClass = "_dafny.MultiSet";
    const string DafnySeqClass = "_dafny.Seq";
    const string DafnyMapClass = "_dafny.Map";
    protected override string StmtTerminator { get => ""; }
    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine($"# Dafny program {program.Name} compiled into Python");
      ReadRuntimeSystem("DafnyRuntime.py", wr.NewFile("_dafny.py"));
      Imports.Add("_dafny");
      EmitImports(null, wr);
      wr.WriteLine();
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      Coverage.EmitSetup(wr);
      wr.WriteLine("_module._default.Main()");
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw) {
      var wr = ((ClassWriter)cw).MethodWriter;
      return wr.WriteLine("def Main():");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern,
        string libraryName, ConcreteSyntaxTree wr) {
      var file = wr.NewFile($"{moduleName}.py");
      EmitImports(moduleName, file);
      return file;
    }

    private void EmitImports(string moduleName, ConcreteSyntaxTree wr) {
      wr.WriteLine("import sys");
      wr.WriteLine("from typing import Callable, NamedTuple");
      wr.WriteLine("from math import floor");
      wr.WriteLine();
      Imports.Iter(module => wr.WriteLine($"import {module}"));
      if (moduleName != null) {
        wr.WriteLine();
        wr.WriteLine($"assert \"{moduleName}\" == __name__");
        wr.WriteLine($"{moduleName} = sys.modules[__name__]");

        Imports.Add(moduleName);
      }
    }

    protected override string GetHelperModuleName() {
      throw new NotImplementedException();
    }

    private static string MangleName(string name) {
      return name.StartsWith("__") ? name[1..] : name;
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
        List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      var methodWriter = wr.NewBlockPy(header: $"class {MangleName(name)}:");

      var needsConstructor = cls is TopLevelDeclWithMembers decl && decl.Members.Any(m => !m.IsGhost && m is Field && !m.IsStatic);
      var constructorWriter = needsConstructor
        ? methodWriter.NewBlockPy(header: "def  __init__(self):", close: BlockStyle.Newline)
        : null;
      if (cls is ClassDecl d) {
        if (!needsConstructor && d.Members.All(m => m.IsGhost)) {
          methodWriter.WriteLine("pass");
        }
      }
      return new ClassWriter(this, constructorWriter, methodWriter);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      List<Type> superClasses, IToken tok,
      ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {

      if (dt is TupleTypeDecl) {
        return null;
      }

      var DtT = dt.CompileName;

      var btw = wr.NewBlockPy($"class {DtT}:");

      foreach (var ctor in dt.Ctors) {
        // Class-level fields don't work in all python version due to metaclasses.
        var namedtuple = $"NamedTuple(\"{ctor.CompileName}\", [])";
        var header = $"class {DtCtorDeclarationName(ctor, false)}({DtT}, {namedtuple}):";
        var constructor = wr.NewBlockPy(header, close: BlockStyle.Newline);
        DatatypeFieldsAndConstructor(ctor, constructor);
      }

      return new ClassWriter(this, btw, btw);
    }

    private void DatatypeFieldsAndConstructor(DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      wr.WriteLine("pass");
    }

    private static string DtCtorDeclarationName(DatatypeCtor ctor, bool full = true) {
      var dt = ctor.EnclosingDatatype;
      return $"{(full ? dt.FullCompileName : dt.CompileName)}_{ctor.CompileName}";
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(nt.EnclosingModuleDefinition.CompileName), IdName(nt), nt, wr);
      var w = cw.MethodWriter;
      var udt = UserDefinedType.FromTopLevelDecl(nt.tok, nt);
      var d = TypeInitializationValue(udt, wr, nt.tok, false, false);

      w.WriteLine("@staticmethod");
      w.NewBlockPy("def default():", close: BlockStyle.Newline).WriteLine($"return {d}", "");

      return cw;
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
      var w = cw.MethodWriter;
      var udt = UserDefinedType.FromTopLevelDecl(sst.tok, sst);
      var d = TypeInitializationValue(udt, wr, sst.tok, false, false);

      w.WriteLine("@staticmethod");
      w.NewBlockPy("def default():").WriteLine($"return {d}", "");
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
        case NativeType.Selection.SByte:
        case NativeType.Selection.UShort:
        case NativeType.Selection.Short:
        case NativeType.Selection.UInt:
        case NativeType.Selection.Int:
        case NativeType.Selection.Number:
        case NativeType.Selection.ULong:
        case NativeType.Selection.Long:
          name = "int"; break;
        default:
          Contract.Assert(false); // unexpected native type
          throw new cce.UnreachableException(); // to please the compiler
      }
    }

    protected class ClassWriter : IClassWriter {
      public readonly PythonCompiler Compiler;
      public readonly ConcreteSyntaxTree ConstructorWriter;
      public readonly ConcreteSyntaxTree MethodWriter;

      public ClassWriter(PythonCompiler compiler, ConcreteSyntaxTree constructorWriter, ConcreteSyntaxTree methodWriter) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(constructorWriter != null);
        this.Compiler = compiler;
        this.ConstructorWriter = constructorWriter;
        this.MethodWriter = methodWriter;
      }

      public ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new NotImplementedException();
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member,
          MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok,
          bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, MethodWriter);
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool isStatic,
          bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, methodWriter: MethodWriter);
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IToken tok, string rhs, Field field) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, ConstructorWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new NotSupportedException();
      }

      public ConcreteSyntaxTree ErrorWriter() => MethodWriter;

      public void Finish() {

      }
    }

    private void DeclareField(string name, bool isStatic, bool isConst, Type type, IToken tok, string rhs,
        ConcreteSyntaxTree fieldWriter) {
      fieldWriter.Write($"self.{name}: {TypeName(type, fieldWriter, tok)}");
      if (rhs != null) {
        fieldWriter.Write($" = {rhs}");
      }
      fieldWriter.WriteLine();
    }

    private ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok, bool isStatic,
        bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree methodWriter) {
      throw new NotImplementedException();
    }

    private ConcreteSyntaxTree CreateGetter(string name, Type resultType, IToken tok, bool isStatic, bool createBody,
        ConcreteSyntaxTree methodWriter) {
      methodWriter.WriteLine(isStatic ? "@_dafny.classproperty" : "@property");
      return methodWriter.NewBlockPy(header: $"def {name}({(isStatic ? "instance" : "self")}):");
    }

    private ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (m.IsStatic) { wr.WriteLine("@staticmethod"); }
      wr.Write($"def {IdName(m)}(");
      WriteFormals(m.Ins, m.IsStatic, wr);
      return wr.NewBlockPy("):", close: BlockStyle.Newline);
    }

    protected override ConcreteSyntaxTree EmitMethodReturns(Method m, ConcreteSyntaxTree wr) {
      if (m.Outs.Any(f => !f.IsGhost)) {
        var beforeReturnBlock = wr.Fork();
        EmitReturn(m.Outs, wr);
        return beforeReturnBlock;
      }
      return wr;
    }

    private void WriteFormals(List<Formal> formals, bool isStatic, ConcreteSyntaxTree wr) {
      var self = wr.Fork();
      if (!isStatic) {
        self.Write("self");
      }
      if (WriteFormals("", formals, wr) > 0 && !isStatic) {
        self.Write(", ");
      }
    }

    private ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
        List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
        ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (isStatic || NeedsCustomReceiver(member)) { wr.WriteLine("@staticmethod"); }
      wr.Write($"def {name}(");
      WriteFormals(formals, isStatic, wr);
      return wr.NewBlockPy("):", close: BlockStyle.Newline);
    }


    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      return TypeName(type, wr, tok, boxed: false, member);
    }
    private string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, bool boxed, MemberDecl /*?*/ member = null) {
      return TypeName(type, wr, tok, boxed, false, member);
    }
    private string TypeName(Type type, ConcreteSyntaxTree wr, Bpl.IToken tok, bool boxed, bool erased, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();

      switch (xType) {
        case BoolType:
          return "bool";
        case CharType:
          return "char";
        case IntType or BigOrdinalType or BitvectorType:
          return "int";
        case RealType:
          return "_dafny.BigRational";
        case UserDefinedType udt: {
            var s = FullTypeName(udt, member);
            return TypeName_UDT(s, udt, wr, udt.tok);
          }
        case CollectionType:
          return TypeHelperName(xType);
      }

      Contract.Assert(false);
      throw new NotImplementedException();
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();

      switch (xType) {
        case BoolType:
          return "False";
        case CharType:
          return CharType.DefaultValueAsString;
        case IntType or BigOrdinalType or BitvectorType:
          return "int(0)";
        case RealType:
          return "_dafny.BigRational()";
        case CollectionType:
          return $"{TypeHelperName(xType)}({{}})";
        case UserDefinedType udt: {
            var cl = udt.ResolvedClass;
            Contract.Assert(cl != null);
            switch (cl) {
              case SubsetTypeDecl td:
                switch (td.WitnessKind) {
                  case SubsetTypeDecl.WKind.Special:
                    Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
                    var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
                    var arguments = udt.TypeArgs.Comma((ty, i) => $"x{i}");
                    return $"lambda {arguments}: {rangeDefaultValue}";
                  default:
                    return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue,
                      constructTypeParameterDefaultsFromTypeDescriptors);
                }

              case NewtypeDecl td: {
                  if (td.Witness != null) {
                    throw new NotImplementedException();
                  } else {
                    return TypeInitializationValue(td.BaseType, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
                  }
                }
            }
            break;
          }
      }

      Contract.Assert(false);
      throw new cce.UnreachableException();  // unexpected type
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok) {
      return IdProtect(fullCompileName);
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      return TypeName(type, wr, tok, member);
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      if (isInParam) {
        wr.Write("{0}{1}", prefix, name);
        return true;
      } else {
        return false;
      }
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      wr.Write(name);
      if (type != null) { wr.Write($": {TypeName(type, wr, tok)}"); }
      if (rhs != null) { wr.Write($" = {rhs}"); }
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      var w = new ConcreteSyntaxTree();
      wr.FormatLine($"{name} = {w}");
      return w;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      // emit nothing
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
      return $"{target}: {TypeName(type, wr, tok)}";
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      wr.Write("_dafny.print(");
      TrExpr(arg, wr, false, wStmts);
      wr.WriteLine(")");
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      wr.Write("return");
      if (outParams.Count > 0) {
        wr.Write($" {outParams.Comma(IdName)}");
      }
      wr.WriteLine();
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      if (createContinueLabel) { throw new NotImplementedException(); }
      return wr.NewBlockPy($"with _dafny.label(\"{label}\"):");
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      if (label != null) {
        wr.WriteLine($"_dafny._break(\"{label}\")");
      } else {
        wr.WriteLine("break");
      }
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine($"raise Exception(\"{message}\")");
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      wr.Write("if ");
      guardWriter = wr.Fork();
      return wr.NewBlockPy(":", hasElse ? "el" : "");
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      //This encoding does not provide a new scope
      return wr.NewBlockPy("if True:");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      wr.Write("while ");
      guardWriter = wr.Fork();
      var wBody = wr.NewBlockPy(":");
      return wBody;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override string GetQuantifierName(string bvType) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      collectionWriter = new ConcreteSyntaxTree();
      wr.WriteLine($"{tmpVarName}: {TypeName(collectionElementType, wr, tok)}")
        .Format($"for {tmpVarName} in {collectionWriter}:");
      return wr.NewBlockPy();
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{boundVarName}{(introduceBoundVar ? $": {TypeName(boundVarType, wr, tok)}" : "")} = {tmpVarName}");
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt _, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{TypeName(type, wr, tok)}()");
    }

    protected override void EmitNewArray(Type elmtType, IToken tok, List<Expression> dimensions, bool mustInitialize,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      switch (e) {
        case CharLiteralExpr:
          wr.Write($"'{(string)e.Value}'");
          break;
        case StringLiteralExpr str:
          TrStringLiteral(str, wr);
          break;
        case StaticReceiverExpr:
          wr.Write(TypeName(e.Type, wr, e.tok));
          break;
        default:
          switch (e.Value) {
            case bool value:
              wr.Write($"{value}");
              break;
            case BigInteger integer:
              wr.Write($"{integer}");
              break;
            case BigDec n:
              wr.Write($"_dafny.BigRational('{n.Mantissa}e{n.Exponent}')");
              break;
            default:
              throw new NotImplementedException();
          }
          break;
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      if (!isVerbatim) {
        wr.Write("\"{0}\"", str);
      } else {
        var n = str.Length;
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i + 1 < n && str[i + 1] == '\"') {
            wr.Write("\\\"");
            i++;
          } else if (str[i] == '\\') {
            wr.Write("\\\\");
          } else if (str[i] == '\n') {
            wr.Write("\\n");
          } else if (str[i] == '\r') {
            wr.Write("\\r");
          } else {
            wr.Write(str[i]);
          }
        }
        wr.Write("\"");
      }
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      var vec = wr.ForkInParens();
      wr.Write($" & ((1 << {bvType.Width}) - 1)");
      return vec;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, FCE_Arg_Translator tr) {
      // ( e0 op1 e1) | (e0 op2 (width - e1))
      EmitShift(e0, e1, isRotateLeft ? "<<" : ">>", isRotateLeft, true, wr.ForkInParens(), inLetExprBody, tr);

      wr.Write(" | ");

      EmitShift(e0, e1, isRotateLeft ? ">>" : "<<", !isRotateLeft, false, wr.ForkInParens(), inLetExprBody, tr);
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, bool firstOp, ConcreteSyntaxTree wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }
      tr(e0, wr, inLetExprBody);
      wr.Write($" {op} ");
      if (!firstOp) {
        wr = wr.ForkInParens().Write($"{bv.Width} - ");
      }

      tr(e1, wr.ForkInParens(), inLetExprBody);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }
    public override string PublicIdProtect(string name) {
      Contract.Requires(name != null);
      return name switch {
        _ => MangleName(name)
      };
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      if (udt is ArrowType) {
        //TODO: Add deeper types
        return "Callable";
      }

      var cl = udt.ResolvedClass;
      if (cl is TypeParameter) {
        return IdProtect(udt.CompileName);
      } else {
        return IdProtect(cl.FullCompileName);
      }
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      wr.Write("self");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      wr.Write($"{DtCtorDeclarationName(dtv.Ctor)}({arguments})");
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
        out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = IdProtect((string)idParam);
          break;
        case SpecialField.ID.Keys:
          compiledName = "keys";
          break;
        case SpecialField.ID.Floor:
          preString = "floor(";
          postString = ")";
          break;
        case SpecialField.ID.IsLimit:
          preString = "_dafny.BigOrdinal.is_limit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = "_dafny.BigOrdinal.is_succ(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = "_dafny.BigOrdinal.offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = "_dafny.BigOrdinal.is_nat(";
          postString = ")";
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
        List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
        string additionalCustomParameter = null, bool internalAccess = false) {
      if (internalAccess) {
        return SimpleLvalue(w => {
          w.Write($"self._{member.CompileName}");
        });
      }
      switch (member) {
        case SpecialField sf: {
            GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
            if (compiledName.Length > 0) { compiledName = "." + compiledName; }
            return SuffixLvalue(obj, compiledName);
          }
        case Field: {
            return SimpleLvalue(w => {
              if (member.IsStatic) { w.Write(TypeName_Companion(objType, w, member.tok, member)); } else { obj(w); }
              w.Write($".{IdName(member)}");
            });
          }
        case Function: {
            var param = additionalCustomParameter == null ? "" : $"({additionalCustomParameter})";
            return SuffixLvalue(obj, $".{IdName(member)}{param}");
          }
        default:
          return SimpleLvalue(w => {
            w.Write($"{TypeName_Companion(objType, w, member.tok, member)}.{IdName(member)}({additionalCustomParameter ?? ""})");
          });
      }
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      wr.Write("[");
      TrExpr(index, wr, inLetExprBody, wStmts);
      wr.Write("]");
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function,
        List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrExpr(function, wr, inLetExprBody, wStmts);
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
        List<Type> boundTypes, Type resultType, IToken resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      var wrBody = new ConcreteSyntaxTree();
      wr.Format($"(lambda {boundVars.Comma()}: {wrBody})");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      return wrBody;
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
        List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override bool TargetLambdasRestrictedToExpressions => true;
    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, bool untyped = false) {
      var wrBody = new ConcreteSyntaxTree();
      var args = inNames.Count > 0 ? $" {inNames.Comma()}" : "";
      wr.Format($"(lambda{args}: {wrBody})");
      return wrBody;
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
        ConcreteSyntaxTree wr, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      wrRhs = new ConcreteSyntaxTree();
      wrBody = new ConcreteSyntaxTree();
      wr.Format($"(lambda {bvName}: lambda: {wrBody})({wrRhs})");
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts = null) {
      Contract.Assert(wStmts != null);
      var functionName = idGenerator.FreshId("_iife");
      wr.WriteLine($"{functionName}()");
      return wStmts.NewBlockPy($"def {functionName}():");
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.Cardinality:
          TrParenExpr("len", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("~", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BoolNot:
          throw new NotImplementedException();
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, Bpl.IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.And:
          opString = "and";
          break;

        case BinaryExpr.ResolvedOpcode.Or:
          opString = "or";
          break;

        case BinaryExpr.ResolvedOpcode.LeftShift:
          opString = "<<";
          break;

        case BinaryExpr.ResolvedOpcode.RightShift:
          opString = ">>";
          break;

        case BinaryExpr.ResolvedOpcode.Add:
          if (!resultType.IsCharType) {
            truncateResult = true;
            opString = "+";
          } else {
            staticCallString = "_dafny.plus_char";
          }
          break;

        case BinaryExpr.ResolvedOpcode.Concat:
          opString = "+";
          break;

        case BinaryExpr.ResolvedOpcode.Sub:
          if (!resultType.IsCharType) {
            truncateResult = true;
            opString = "-";
          } else {
            staticCallString = "_dafny.minus_char";
          }
          break;

        case BinaryExpr.ResolvedOpcode.Mul:
          opString = "*";
          truncateResult = true;
          break;

        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsIntegerType || resultType.IsBitVectorType || resultType.AsNewtype != null) {
            staticCallString = "_dafny.euclidian_division";
          } else {
            opString = "/";
          }
          break;

        case BinaryExpr.ResolvedOpcode.Mod:
          staticCallString = "_dafny.euclidian_modulus"; break;

        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          opString = "=="; break;

        case BinaryExpr.ResolvedOpcode.NeqCommon:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
          opString = "!="; break;

        case BinaryExpr.ResolvedOpcode.Union:
          opString = "|"; break;

        case BinaryExpr.ResolvedOpcode.InSet:
          opString = "in"; break;


        default:
          base.CompileBinOp(op, e0, e1, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments,
            out truncateResult, out convertE1_to_int,
            errorWr);
          break;
      }
    }


    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Requires(guard != null);
      Contract.Requires(thn != null);
      Contract.Requires(thn.Type != null);
      Contract.Requires(els != null);
      Contract.Requires(resultType != null);
      Contract.Requires(wr != null);

      resultType = resultType.NormalizeExpand();
      var thenExpr = Expr(thn, inLetExprBody, wStmts);
      var castedThenExpr = resultType.Equals(thn.Type.NormalizeExpand()) ? thenExpr : Cast(resultType, thenExpr);
      var elseExpr = Expr(els, inLetExprBody, wStmts);
      var castedElseExpr = resultType.Equals(els.Type.NormalizeExpand()) ? elseExpr : Cast(resultType, elseExpr);
      wr.Format($"{castedThenExpr} if {Expr(guard, inLetExprBody, wStmts)} else {castedElseExpr}");
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var (pre, post) = ("", "");
      if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Int) || e.E.Type.IsBitVectorType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
          (pre, post) = ("_dafny.BigRational(", ", 1)");
        } else if (e.ToType.IsCharType) {
          (pre, post) = ("chr(", ")");
        }
      } else if (e.E.Type.IsCharType) {
        (pre, post) = ("ord(", ")");
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
        if (e.ToType.IsNumericBased(Type.NumericPersuasion.Int) || e.ToType.IsBitVectorType || e.ToType.IsBigOrdinalType) {
          (pre, post) = ("int(", ")");
        } else if (e.ToType.IsCharType) {
          (pre, post) = ("chr(floor(", "))");
        }
      }
      wr.Write(pre);
      TrExpr(e.E, wr, inLetExprBody, wStmts);
      wr.Write(post);
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var (open, close) = ct switch {
        SeqType => ("[", "]"),
        _ => ("{", "}")
      };
      wr.Write(TypeHelperName(ct));
      wr.Write("(");
      wr.Write(open);
      TrExprList(elements, wr, inLetExprBody, wStmts, parens: false);
      wr.Write(close);
      wr.Write(")");
    }

    private static string TypeHelperName(Type ct) {
      return ct switch {
        SetType => DafnySetClass,
        SeqType => DafnySeqClass,
        MapType => DafnyMapClass,
        _ => throw new NotImplementedException()
      };
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnyMapClass}({{");
      var sep = "";
      foreach (var p in elements) {
        wr.Write(sep);
        TrExpr(p.A, wr, inLetExprBody, wStmts);
        wr.Write(": ");
        TrExpr(p.B, wr, inLetExprBody, wStmts);
        sep = ", ";
      }
      wr.Write("})");
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      wr.WriteLine($"{collectionName} = {DafnySetClass}()");
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      wr.WriteLine($"{collectionName} = {DafnyMapClass}()");
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.WriteLine($"{collName}.add({Expr(elmt, inLetExprBody, wStmts)})");
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      var termLeftWriter = new ConcreteSyntaxTree();
      var wStmts = wr.Fork();
      wr.FormatLine($"{collName}[{termLeftWriter}] = {Expr(term, inLetExprBody, wStmts)}");
      return termLeftWriter;
    }

    [CanBeNull]
    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      if (boundVarType.IsRefType) {
        throw new NotImplementedException();
      }

      return "True";
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      return TypeHelperName(ct) + $"({collName})";
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
        string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
        bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      if (runAfterCompile) {
        Contract.Assert(callToMain != null); // this is part of the contract of CompileTargetProgram
        // Since the program is to be run soon, nothing further is done here. Any compilation errors (that is, any errors
        // in the emitted program--this should never happen if the compiler itself is correct) will be reported as 'python'
        // will run the program.
        return true;
      } else {
        // compile now
        return SendToNewPythonProcess(dafnyProgramName, targetProgramText, null, targetFilename, otherFileNames,
          outputWriter);
      }
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
        string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {

      return SendToNewPythonProcess(dafnyProgramName, targetProgramText, callToMain, targetFilename, otherFileNames,
        outputWriter);
    }

    bool SendToNewPythonProcess(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
        string targetFilename, ReadOnlyCollection<string> otherFileNames, TextWriter outputWriter) {
      Contract.Requires(targetFilename != null || otherFileNames.Count == 0);

      var psi = new ProcessStartInfo("python3", targetFilename) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardInput = true,
        RedirectStandardOutput = false,
        RedirectStandardError = false,
      };

      try {
        using var pythonProcess = Process.Start(psi);
        pythonProcess.StandardInput.Close();
        pythonProcess.WaitForExit();
        return pythonProcess.ExitCode == 0;
      } catch (Exception e) {
        outputWriter.WriteLine("Error: Unable to start python ({0}): {1}", psi.FileName, e.Message);
        return false;
      }
    }
  }
}
