//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using static Microsoft.Dafny.ConcreteSyntaxTreeUtils;

namespace Microsoft.Dafny.Compilers {
  class JavaCompiler : SinglePassCompiler {
    public JavaCompiler(DafnyOptions options, ErrorReporter reporter) : base(options, reporter) {
      IntSelect = ",java.math.BigInteger";
      LambdaExecute = ".apply";
    }

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.Iterators,
      Feature.SubsetTypeTests,
      Feature.MethodSynthesis,
      Feature.TuplesWiderThan20
    };

    const string DafnySetClass = "dafny.DafnySet";
    const string DafnyMultiSetClass = "dafny.DafnyMultiset";
    const string DafnySeqClass = "dafny.DafnySequence";
    const string DafnyMapClass = "dafny.DafnyMap";

    const string DafnyBigRationalClass = "dafny.BigRational";
    const string DafnyEuclideanClass = "dafny.DafnyEuclidean";
    const string DafnyHelpersClass = "dafny.Helpers";
    const string DafnyTypeDescriptor = "dafny.TypeDescriptor";
    static string FormatDefaultTypeParameterValue(TypeParameter tp) => FormatDefaultTypeParameterValueName(tp.CompileName);
    static string FormatDefaultTypeParameterValueName(string tpName) => $"_default_{tpName}";

    const string DafnyFunctionIfacePrefix = "dafny.Function";
    const string DafnyMultiArrayClassPrefix = "dafny.Array";
    const string DafnyTupleClassPrefix = "dafny.Tuple";

    string DafnyMultiArrayClass(int dim) => DafnyMultiArrayClassPrefix + dim;
    string DafnyTupleClass(int size) => DafnyTupleClassPrefix + size;

    string DafnyFunctionIface(int arity) =>
      arity == 1 ? "java.util.function.Function" : DafnyFunctionIfacePrefix + arity;

    static string FormatExternBaseClassName(string externClassName) =>
      $"_ExternBase_{externClassName}";
    static string FormatTypeDescriptorVariable(string typeVarName) =>
      $"_td_{typeVarName}";
    static string FormatTypeDescriptorVariable(TypeParameter tp) =>
      FormatTypeDescriptorVariable(tp.CompileName);

    const string TypeMethodName = "_typeDescriptor";

    private string ModuleName;
    private string ModulePath;
    private int FileCount = 0;
    private Import ModuleImport;
    private HashSet<int> tuples = new HashSet<int>();
    private HashSet<int> functions = new HashSet<int>();
    private HashSet<int> arrays = new HashSet<int>();

    private readonly List<Import> Imports = new List<Import>();

    //RootImportWriter writes additional imports to the main file.
    private ConcreteSyntaxTree RootImportWriter;

    private struct Import {
      public string Name, Path;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;


    protected override bool SupportsAmbiguousTypeDecl => false;
    protected override bool SupportsProperties => false;

    private enum JavaNativeType { Byte, Short, Int, Long }

    private static JavaNativeType AsJavaNativeType(NativeType.Selection sel) {
      switch (sel) {
        case NativeType.Selection.Byte:
        case NativeType.Selection.SByte:
          return JavaNativeType.Byte;
        case NativeType.Selection.Short:
        case NativeType.Selection.UShort:
          return JavaNativeType.Short;
        case NativeType.Selection.Int:
        case NativeType.Selection.UInt:
          return JavaNativeType.Int;
        case NativeType.Selection.Long:
        case NativeType.Selection.ULong:
          return JavaNativeType.Long;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private static bool IsUnsignedJavaNativeType(NativeType nt) {
      Contract.Requires(nt != null);
      switch (nt.Sel) {
        case NativeType.Selection.Byte:
        case NativeType.Selection.UShort:
        case NativeType.Selection.UInt:
        case NativeType.Selection.ULong:
          return true;
        default:
          return false;
      }
    }

    private static JavaNativeType AsJavaNativeType(NativeType nt) {
      return AsJavaNativeType(nt.Sel);
    }

    private JavaNativeType? AsJavaNativeType(Type type) {
      var nt = AsNativeType(type);
      if (nt == null) {
        return null;
      } else {
        return AsJavaNativeType(nt);
      }
    }

    protected override void DeclareSpecificOutCollector(string collectorVarName, ConcreteSyntaxTree wr, List<Type> formalTypes, List<Type> lhsTypes) {
      // If the method returns an array of parameter type, and we're assigning
      // to a variable with a more specific type, we need to insert a cast:
      //
      // Array<Integer> outcollector42 = obj.Method(); // <-- you are here
      // int[] out43 = (int[]) outcollector42.unwrap();
      var returnedTypes = new List<string>();
      Contract.Assert(formalTypes.Count == lhsTypes.Count);
      for (var i = 0; i < formalTypes.Count; i++) {
        var formalType = formalTypes[i];
        var lhsType = lhsTypes[i];
        if (formalType.IsArrayType && formalType.AsArrayType.Dims == 1 && UserDefinedType.ArrayElementType(formalType).IsTypeParameter) {
          returnedTypes.Add("java.lang.Object");
        } else {
          returnedTypes.Add(TypeName(lhsType, wr, Token.NoToken, boxed: formalTypes.Count > 1));
        }
      }
      if (formalTypes.Count > 1) {
        tuples.Add(formalTypes.Count);
        wr.Write($"{DafnyTupleClass(formalTypes.Count)}<{Util.Comma(returnedTypes)}> {collectorVarName} = ");
      } else {
        wr.Write($"{returnedTypes[0]} {collectorVarName} = ");
      }
    }
    protected override void EmitCastOutParameterSplits(string outCollector, List<string> lhsNames,
      ConcreteSyntaxTree wr, List<Type> formalTypes, List<Type> lhsTypes, IToken tok) {
      var wOuts = new List<ConcreteSyntaxTree>();
      for (var i = 0; i < lhsNames.Count; i++) {
        wr.Write($"{lhsNames[i]} = ");
        //
        // Suppose we have:
        //
        //   method Foo<A>(a : A) returns (arr : array<A>)
        //
        // This is compiled to:
        //
        //   public <A> Object Foo(A a)
        //
        // (There's also an argument for the type descriptor, but I'm omitting
        // it for clarity.)  Foo returns Object, not A[], since A could be
        // primitive and primitives cannot be generic parameters in Java
        // (*sigh*).  So when we call it:
        //
        //   var arr : int[] := Foo(42);
        //
        // we have to add a type cast:
        //
        //   BigInteger[] arr = (BigInteger[]) Foo(new BigInteger(42));
        //
        // Things can get more complicated than this, however.  If the method returns
        // the array as part of a tuple:
        //
        //   method Foo<A>(a : A) returns (pair : (array<A>, array<A>))
        //
        // then we get:
        //
        //   public <A> Tuple2<Object, Object> Foo(A a)
        //
        // and we have to write:
        //
        //   BigInteger[] arr = (Pair<BigInteger[], BigInteger[]>) (Object) Foo(new BigInteger(42));
        //
        // (Note the extra cast to Object, since Java doesn't allow a cast to
        // change a type parameter, as that's unsound in general.  It just
        // happens to be okay here!)
        //
        // Rather than try and exhaustively check for all the circumstances
        // where a cast is necessary, for the moment we just always cast to the
        // LHS type via Object, which is redundant 99% of the time but not
        // harmful.
        if (lhsTypes[i] == null) {
          wr.Write($"(Object) ");
        } else {
          wr.Write($"({TypeName(lhsTypes[i], wr, Token.NoToken)}) (Object) ");
        }

        if (lhsNames.Count == 1) {
          wr.Write(outCollector);
        } else {
          wr.Write($"{outCollector}.dtor__{i}()");
        }
        EndStmt(wr);
      }
    }

    protected override void EmitSeqSelect(AssignStmt s0, List<Type> tupleTypeArgsList, ConcreteSyntaxTree wr, string tup) {
      wr.Write("(");
      var lhs = (SeqSelectExpr)s0.Lhs;
      ConcreteSyntaxTree wColl, wIndex, wValue;
      EmitIndexCollectionUpdate(lhs.Seq.Type, out wColl, out wIndex, out wValue, wr, nativeIndex: true);
      var wCoerce = EmitCoercionIfNecessary(from: NativeObjectType, to: lhs.Seq.Type, tok: s0.Tok, wr: wColl);
      wCoerce.Write($"({TypeName(lhs.Seq.Type.NormalizeExpand(), wCoerce, s0.Tok)})");
      EmitTupleSelect(tup, 0, wCoerce);
      wColl.Write(")");
      var wCast = EmitCoercionToNativeInt(wIndex);
      EmitTupleSelect(tup, 1, wCast);
      wValue.Write($"({TypeName(tupleTypeArgsList[2].NormalizeExpand(), wValue, s0.Tok)})");
      EmitTupleSelect(tup, 2, wValue);
      EndStmt(wr);
    }

    protected override void EmitMultiSelect(AssignStmt s0, List<Type> tupleTypeArgsList, ConcreteSyntaxTree wr, string tup, int L) {
      var arrayType = tupleTypeArgsList[0];
      var rhsType = tupleTypeArgsList[L - 1];

      var lhs = (MultiSelectExpr)s0.Lhs;
      var indices = new List<string>();
      for (var i = 0; i < lhs.Indices.Count; i++) {
        var wIndex = new ConcreteSyntaxTree();
        wIndex.Write("((java.math.BigInteger)");
        EmitTupleSelect(tup, i + 1, wIndex);
        wIndex.Write(")");
        indices.Add(wIndex.ToString());
      }

      var (wArray, wRhs) = EmitArrayUpdate(indices, rhsType, wr);
      wArray = EmitCoercionIfNecessary(from: null, to: arrayType, tok: s0.Tok, wr: wArray);
      wArray.Write($"({TypeName(arrayType.NormalizeExpand(), wArray, s0.Tok)})");
      EmitTupleSelect(tup, 0, wArray);

      wRhs.Write($"({TypeName(rhsType, wr, s0.Tok)})");
      EmitTupleSelect(tup, L - 1, wRhs);

      EndStmt(wr);
    }

    protected override void WriteCast(string s, ConcreteSyntaxTree wr) {
      wr.Write($"({s})");
    }

    protected override ConcreteSyntaxTree EmitIngredients(ConcreteSyntaxTree wr, string ingredients, int L, string tupleTypeArgs, ForallStmt s, AssignStmt s0, Expression rhs) {
      var wStmts = wr.Fork();
      var wrVarInit = wr;
      wrVarInit.Write($"java.util.ArrayList<{DafnyTupleClass(L)}<{tupleTypeArgs}>> {ingredients} = ");
      AddTupleToSet(L);
      EmitEmptyTupleList(tupleTypeArgs, wrVarInit);
      var wrOuter = wr;
      wr = CompileGuardedLoops(s.BoundVars, s.Bounds, s.Range, wr);
      var wrTuple = EmitAddTupleToList(ingredients, tupleTypeArgs, wr);
      wrTuple.Write($"{L}<{tupleTypeArgs}>(");
      if (s0.Lhs is MemberSelectExpr lhs1) {
        wrTuple.Append(Expr(lhs1.Obj, false, wStmts));
      } else if (s0.Lhs is SeqSelectExpr lhs2) {
        wrTuple.Append(Expr(lhs2.Seq, false, wStmts));
        wrTuple.Write(", ");
        TrParenExpr(lhs2.E0, wrTuple, false, wStmts);
      } else {
        var lhs = (MultiSelectExpr)s0.Lhs;
        wrTuple.Append(Expr(lhs.Array, false, wStmts));
        foreach (var t in lhs.Indices) {
          wrTuple.Write(", ");
          TrParenExpr(t, wrTuple, false, wStmts);
        }
      }

      wrTuple.Write(", ");
      if (rhs is MultiSelectExpr) {
        Type t = rhs.Type.NormalizeExpand();
        wrTuple.Write($"({TypeName(t, wrTuple, rhs.tok)})");
      }

      wrTuple.Append(Expr(rhs, false, wStmts));
      return wrOuter;
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine($"// Dafny program {program.Name} compiled into Java");
      ModuleName = program.MainMethod != null ? "main" : Path.GetFileNameWithoutExtension(program.Name);
      wr.WriteLine();
      // Keep the import writers so that we can import subsequent modules into the main one
      EmitImports(wr, out RootImportWriter);
      wr.WriteLine();
    }

    // Only exists to make sure method is overriden
    protected override void EmitBuiltInDecls(BuiltIns builtIns, ConcreteSyntaxTree wr) {
      if (builtIns.MaxNonGhostTupleSizeUsed > 20) {
        UnsupportedFeatureError(builtIns.MaxNonGhostTupleSizeToken, Feature.TuplesWiderThan20);
      }
    }

    public static string TransformToClassName(string baseName) =>
      Regex.Replace(baseName, "[^_A-Za-z0-9$]", "_");

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      var className = TransformToClassName(baseName);
      wr = wr.NewBlock($"public class {className}");

      var companion = TypeName_Companion(UserDefinedType.FromTopLevelDeclWithAllBooleanTypeParameters(mainMethod.EnclosingClass), wr, mainMethod.tok, mainMethod);
      var wBody = wr.NewNamedBlock("public static void main(String[] args)");
      var modName = mainMethod.EnclosingClass.EnclosingModuleDefinition.CompileName == "_module" ? "_System." : "";
      companion = modName + companion;
      Coverage.EmitSetup(wBody);
      wBody.WriteLine($"{DafnyHelpersClass}.withHaltHandling(() -> {{ {companion}.__Main({DafnyHelpersClass}.{CharMethodQualifier}FromMainArguments(args)); }} );");
      Coverage.EmitTearDown(wBody);
    }

    void EmitImports(ConcreteSyntaxTree wr, out ConcreteSyntaxTree importWriter) {
      importWriter = wr.Fork();
      foreach (var import in Imports) {
        if (import.Name != ModuleName) {
          EmitImport(import, importWriter);
        }
      }
    }

    private void EmitImport(Import import, ConcreteSyntaxTree importWriter) {
      importWriter.WriteLine($"import {import.Path.Replace('/', '.')}.*;");
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern, string /*?*/ libraryName, ConcreteSyntaxTree wr) {
      if (isDefault) {
        // Fold the default module into the main module
        return wr;
      }
      var pkgName = libraryName ?? IdProtect(moduleName);
      var path = pkgName.Replace('.', '/');
      var import = new Import { Name = moduleName, Path = path };
      ModuleName = IdProtect(moduleName);
      ModulePath = path;
      ModuleImport = import;
      FileCount = 0;
      return wr;
    }

    protected override void FinishModule() {
      if (FileCount > 0) {
        AddImport(ModuleImport);
      }
      FileCount = 0;
    }

    private void AddImport(Import import) {
      if (!Imports.Contains(import)) {
        EmitImport(import, RootImportWriter);
        Imports.Add(import);
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(sst.EnclosingModuleDefinition.CompileName), IdName(sst), sst, wr);
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var sw = new ConcreteSyntaxTree(cw.InstanceMemberWriter.RelativeIndentLevel);
        var wStmts = cw.InstanceMemberWriter.Fork();
        sw.Append(Expr(sst.Witness, false, wStmts));
        var witness = sw.ToString();
        var typeName = TypeName(sst.Rhs, cw.StaticMemberWriter, sst.tok);
        if (sst.TypeArgs.Count == 0) {
          cw.DeclareField("Witness", sst, true, true, sst.Rhs, sst.tok, witness, null);
          witness = "Witness";
        }
        var w = cw.StaticMemberWriter.NewBlock($"public static {TypeParameters(sst.TypeArgs, " ")}{typeName} defaultValue()");
        w.WriteLine($"return {witness};");
      }
    }

    protected class ClassWriter : IClassWriter {
      public readonly JavaCompiler Compiler;
      public readonly ConcreteSyntaxTree InstanceMemberWriter;
      public readonly ConcreteSyntaxTree StaticMemberWriter;
      public readonly ConcreteSyntaxTree CtorBodyWriter;

      public ClassWriter(JavaCompiler compiler, ConcreteSyntaxTree instanceMemberWriter, ConcreteSyntaxTree ctorBodyWriter, ConcreteSyntaxTree staticMemberWriter = null) {
        Contract.Requires(compiler != null);
        Contract.Requires(instanceMemberWriter != null);
        this.Compiler = compiler;
        this.InstanceMemberWriter = instanceMemberWriter;
        this.CtorBodyWriter = ctorBodyWriter;
        this.StaticMemberWriter = staticMemberWriter ?? instanceMemberWriter;
      }

      public ConcreteSyntaxTree Writer(bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        if (createBody) {
          if (isStatic || (member != null && member.EnclosingClass is TraitDecl && Compiler.NeedsCustomReceiver(member))) {
            return StaticMemberWriter;
          }
        }
        return InstanceMemberWriter;
      }

      public ConcreteSyntaxTree/*?*/ CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, Writer(m.IsStatic, createBody, m), forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(m.tok, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs, List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member, bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic, createBody, member), forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree/*?*/ CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok, bool isStatic, bool isConst, bool createBody, MemberDecl/*?*/ member, bool forBodyInheritance) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic, createBody, member));
      }
      public ConcreteSyntaxTree/*?*/ CreateGetterSetter(string name, Type resultType, IToken tok, bool createBody, MemberDecl/*?*/ member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, resultType, tok, createBody, out setterWriter, Writer(false, createBody, member));
      }
      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type, IToken tok, string rhs, Field field) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, this);
      }
      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();  // InitializeField should be called only for those compilers that set ClassesRedeclareInheritedFields to false.
      }
      public ConcreteSyntaxTree/*?*/ ErrorWriter() => InstanceMemberWriter;

      public void Finish() { }
    }

    protected override bool SupportsStaticsInGenericClasses => false;

    protected ConcreteSyntaxTree CreateGetter(string name, Type resultType, IToken tok, bool isStatic,
      bool createBody, ConcreteSyntaxTree wr) {
      wr.Write("public {0}{1} {2}()", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      if (createBody) {
        var w = wr.NewBlock("", null, BlockStyle.NewlineBrace, BlockStyle.NewlineBrace);
        return w;
      } else {
        wr.WriteLine(";");
        return null;
      }
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, IToken /*?*/ tok, Expression rhs,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (type == null) {
        type = rhs.Type;
      }
      var wStmts = wr.Fork();
      var w = DeclareLocalVar(name, type, tok, wr);
      w.Append(Expr(rhs, inLetExprBody, wStmts));
    }

    public ConcreteSyntaxTree /*?*/ CreateGetterSetter(string name, Type resultType, IToken tok,
      bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree wr) {
      wr.Write($"public {TypeName(resultType, wr, tok)} {name}()");
      ConcreteSyntaxTree wGet = null;
      if (createBody) {
        wGet = wr.NewBlock("", null, BlockStyle.NewlineBrace, BlockStyle.NewlineBrace);
      } else {
        wr.WriteLine(";");
      }
      wr.Write($"public void set_{name}({TypeName(resultType, wr, tok)} value)");
      if (createBody) {
        setterWriter = wr.NewBlock("", null, BlockStyle.NewlineBrace, BlockStyle.NewlineBrace);
      } else {
        wr.WriteLine(";");
        setterWriter = null;
      }
      return wGet;
    }
    protected ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (m.IsExtern(Options, out _, out _) && (m.IsStatic || m is Constructor)) {
        // No need for an abstract version of a static method or a constructor
        return null;
      }
      string targetReturnTypeReplacement = null;
      int nonGhostOuts = 0;
      int nonGhostIndex = 0;
      for (int i = 0; i < m.Outs.Count; i++) {
        if (!m.Outs[i].IsGhost) {
          nonGhostOuts += 1;
          nonGhostIndex = i;
        }
      }
      if (nonGhostOuts == 1) {
        targetReturnTypeReplacement = TypeName(m.Outs[nonGhostIndex].Type, wr, m.Outs[nonGhostIndex].tok);
      } else if (nonGhostOuts > 1) {
        targetReturnTypeReplacement = DafnyTupleClass(nonGhostOuts);
      }
      var customReceiver = createBody && !forBodyInheritance && NeedsCustomReceiver(m);
      var receiverType = UserDefinedType.FromTopLevelDecl(m.tok, m.EnclosingClass);
      wr.Write("public {0}{1}", !createBody && !(m.EnclosingClass is TraitDecl) ? "abstract " : "", m.IsStatic || customReceiver ? "static " : "");
      wr.Write(TypeParameters(TypeArgumentInstantiation.ToFormals(ForTypeParameters(typeArgs, m, lookasideBody)), " "));
      wr.Write("{0} {1}", targetReturnTypeReplacement ?? "void", IdName(m));
      wr.Write("(");
      var sep = "";
      WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArgs, m.EnclosingClass, m, lookasideBody), wr, ref sep, tp => $"{DafnyTypeDescriptor}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)}");
      if (customReceiver) {
        DeclareFormal(sep, "_this", receiverType, m.tok, true, wr);
        sep = ", ";
      }
      WriteFormals(sep, m.Ins, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      } else {
        return wr.NewBlock(")", null, BlockStyle.NewlineBrace, BlockStyle.NewlineBrace);
      }
    }

    protected override ConcreteSyntaxTree EmitMethodReturns(Method m, ConcreteSyntaxTree wr) {
      int nonGhostOuts = 0;
      foreach (var t in m.Outs) {
        if (t.IsGhost) {
          continue;
        }

        nonGhostOuts += 1;
        break;
      }
      if (!m.Body.Body.OfType<ReturnStmt>().Any() && (nonGhostOuts > 0 || m.IsTailRecursive)) { // If method has out parameters or is tail-recursive but no explicit return statement in Dafny
        var beforeReturn = wr.NewBlock("if(true)"); // Ensure no unreachable error is thrown for the return statement
        EmitReturn(m.Outs, wr);
        return beforeReturn;
      }
      return wr;
    }

    protected ConcreteSyntaxTree/*?*/ CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
      List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
      ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      if (member.IsExtern(Options, out _, out _) && isStatic) {
        // No need for abstract version of static method
        return null;
      }
      var customReceiver = createBody && !forBodyInheritance && NeedsCustomReceiver(member);
      var receiverType = UserDefinedType.FromTopLevelDecl(member.tok, member.EnclosingClass);
      wr.Write("public {0}{1}", !createBody && !(member.EnclosingClass is TraitDecl) ? "abstract " : "", isStatic || customReceiver ? "static " : "");
      wr.Write(TypeParameters(TypeArgumentInstantiation.ToFormals(ForTypeParameters(typeArgs, member, lookasideBody)), " "));
      wr.Write($"{TypeName(resultType, wr, tok)} {name}(");
      var sep = "";
      var argCount = WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, lookasideBody), wr, ref sep, tp => $"{DafnyTypeDescriptor}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)}");
      if (customReceiver) {
        DeclareFormal(sep, "_this", receiverType, tok, true, wr);
        sep = ", ";
        argCount++;
      }
      argCount += WriteFormals(sep, formals, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      } else {
        ConcreteSyntaxTree w;
        if (argCount > 1) {
          w = wr.NewBlock(")", null, BlockStyle.NewlineBrace, BlockStyle.NewlineBrace);
        } else {
          w = wr.NewBlock(")");
        }
        return w;
      }
    }

    protected void DeclareField(string name, bool isStatic, bool isConst, Type type, IToken tok, string rhs, ClassWriter cw) {
      if (isStatic) {
        var r = rhs ?? DefaultValue(type, cw.StaticMemberWriter, tok);
        var t = StripTypeParameters(TypeName(type, cw.StaticMemberWriter, tok));
        cw.StaticMemberWriter.WriteLine($"public static {t} {name} = {r};");
      } else {
        Contract.Assert(cw.CtorBodyWriter != null, "Unexpected instance field");
        cw.InstanceMemberWriter.WriteLine("public {0} {1};", TypeName(type, cw.InstanceMemberWriter, tok), name);
        cw.CtorBodyWriter.WriteLine("this.{0} = {1};", name, rhs ?? PlaceboValue(type, cw.CtorBodyWriter, tok));
      }
    }

    private string StripTypeParameters(string s) {
      Contract.Requires(s != null);
      return Regex.Replace(s, @"<.+>", "");
    }

    private void EmitSuppression(ConcreteSyntaxTree wr) {
      wr.WriteLine("@SuppressWarnings({\"unchecked\", \"deprecation\"})");
    }

    string TypeParameters(List<TypeParameter>/*?*/ targs, string suffix = "") {
      Contract.Requires(targs == null || cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      if (targs == null || targs.Count == 0) {
        return "";  // ignore suffix
      }
      return $"<{Util.Comma(targs, IdName)}>{suffix}";
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      return TypeName(type, wr, tok, boxed: false, member);
    }

    private string BoxedTypeName(Type type, ConcreteSyntaxTree wr, IToken tok) {
      return TypeName(type, wr, tok, boxed: true);
    }

    private string ActualTypeArgument(Type type, TypeParameter.TPVariance variance, ConcreteSyntaxTree wr, IToken tok) {
      Contract.Requires(type != null);
      Contract.Requires(wr != null);
      Contract.Requires(tok != null);
      var typeName = BoxedTypeName(type, wr, tok);
      if (variance == TypeParameter.TPVariance.Co) {
        return "? extends " + typeName;
      } else if (variance == TypeParameter.TPVariance.Contra) {
        if (type.IsRefType) {
          return "? super " + typeName;
        }
      }
      return typeName;
    }

    private string BoxedTypeNames(List<Type> types, ConcreteSyntaxTree wr, IToken tok) {
      return Util.Comma(types, t => BoxedTypeName(t, wr, tok));
    }

    protected override string TypeArgumentName(Type type, ConcreteSyntaxTree wr, IToken tok) {
      return BoxedTypeName(type, wr, tok);
    }

    private string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, bool boxed, MemberDecl /*?*/ member = null) {
      return TypeName(type, wr, tok, boxed, false, member);
    }

    private string CharTypeName(bool boxed) {
      if (UnicodeCharEnabled) {
        return boxed ? "dafny.CodePoint" : "int";
      } else {
        return boxed ? "Character" : "char";
      }
    }

    private string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, bool boxed, bool erased, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = DatatypeWrapperEraser.SimplifyType(Options, type);
      if (xType is BoolType) {
        return boxed ? "Boolean" : "boolean";
      } else if (xType is CharType) {
        return CharTypeName(boxed);
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "java.math.BigInteger";
      } else if (xType is RealType) {
        return DafnyBigRationalClass;
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType, boxed) : "java.math.BigInteger";
      } else if (member == null && xType.AsNewtype != null) {
        var nativeType = xType.AsNewtype.NativeType;
        if (nativeType != null) {
          return GetNativeTypeName(nativeType, boxed);
        }
        return TypeName(xType.AsNewtype.BaseType, wr, tok, boxed);
      } else if (xType.IsObjectQ) {
        return "Object";
      } else if (xType.IsArrayType) {
        ArrayClassDecl at = xType.AsArrayType;
        Contract.Assert(at != null);  // follows from type.IsArrayType
        Type elType = UserDefinedType.ArrayElementType(xType);
        return ArrayTypeName(elType, at.Dims, wr, tok, erased);
      } else if (xType is UserDefinedType udt) {
        if (udt.ResolvedClass is TypeParameter tp) {
          if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(tp, out var instantiatedTypeParameter)) {
            return TypeName(instantiatedTypeParameter, wr, tok, true, member);
          }
        }
        var s = FullTypeName(udt, member);
        if (s.Equals("string")) {
          return "String";
        }
        var cl = udt.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return boxed ? "java.lang.Long" : "long";
        } else if (cl is TupleTypeDecl tupleDecl) {
          s = DafnyTupleClass(tupleDecl.NonGhostDims);
        }

        // When accessing a static member, leave off the type arguments
        if (member != null) {
          return TypeName_UDT(s, new List<TypeParameter.TPVariance>(), new List<Type>(), wr, udt.tok, erased);
        } else {
          return TypeName_UDT(s, udt, wr, udt.tok, erased);
        }
      } else if (xType is SetType) {
        var argType = ((SetType)xType).Arg;
        if (erased) {
          return DafnySetClass;
        }
        return $"{DafnySetClass}<{ActualTypeArgument(argType, TypeParameter.TPVariance.Co, wr, tok)}>";
      } else if (xType is SeqType) {
        var argType = ((SeqType)xType).Arg;
        if (erased) {
          return DafnySeqClass;
        }
        return $"{DafnySeqClass}<{ActualTypeArgument(argType, TypeParameter.TPVariance.Co, wr, tok)}>";
      } else if (xType is MultiSetType) {
        var argType = ((MultiSetType)xType).Arg;
        if (erased) {
          return DafnyMultiSetClass;
        }
        return $"{DafnyMultiSetClass}<{ActualTypeArgument(argType, TypeParameter.TPVariance.Co, wr, tok)}>";
      } else if (xType is MapType) {
        var domType = ((MapType)xType).Domain;
        var ranType = ((MapType)xType).Range;
        if (erased) {
          return DafnyMapClass;
        }
        return $"{DafnyMapClass}<{ActualTypeArgument(domType, TypeParameter.TPVariance.Co, wr, tok)}, {ActualTypeArgument(ranType, TypeParameter.TPVariance.Co, wr, tok)}>";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    string ArrayTypeName(Type elType, int dims, ConcreteSyntaxTree wr, IToken tok, bool erased) {
      elType = DatatypeWrapperEraser.SimplifyType(Options, elType);
      if (dims > 1) {
        arrays.Add(dims);
        if (erased) {
          return DafnyMultiArrayClass(dims);
        } else {
          return $"{DafnyMultiArrayClass(dims)}<{ActualTypeArgument(elType, TypeParameter.TPVariance.Non, wr, tok)}>";
        }
      } else if (elType.IsTypeParameter) {
        return "java.lang.Object";
      } else {
        return $"{TypeName(elType, wr, tok, false, erased)}[]";
      }
    }

    protected string CollectionTypeUnparameterizedName(CollectionType ct) {
      if (ct is SeqType) {
        return DafnySeqClass;
      } else if (ct is SetType) {
        return DafnySetClass;
      } else if (ct is MultiSetType) {
        return DafnyMultiSetClass;
      } else if (ct is MapType) {
        return DafnyMapClass;
      } else {
        Contract.Assert(false);  // unexpected collection type
        throw new cce.UnreachableException();  // to please the compiler
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl /*?*/ member = null) {
      return FullTypeName(udt, member, false);
    }

    protected string FullTypeName(UserDefinedType udt, MemberDecl member, bool useCompanionName) {
      Contract.Requires(udt != null);
      if (udt.IsBuiltinArrowType) {
        functions.Add(udt.TypeArgs.Count - 1);
        return DafnyFunctionIface(udt.TypeArgs.Count - 1);
      }
      string qualification;
      if (member != null && member.IsExtern(Options, out qualification, out _) && qualification != null) {
        return qualification;
      }
      var cl = udt.ResolvedClass;
      if (cl is NonNullTypeDecl nntd) {
        cl = nntd.Class;
      }
      if (cl is TypeParameter) {
        return IdProtect(udt.CompileName);
      } else if (cl is TupleTypeDecl tupleDecl) {
        return DafnyTupleClass(tupleDecl.NonGhostDims);
      } else if (cl is TraitDecl && useCompanionName) {
        return IdProtect(udt.FullCompanionCompileName);
      } else if (cl.EnclosingModuleDefinition.CompileName == ModuleName || cl.EnclosingModuleDefinition.IsDefaultModule) {
        return IdProtect(cl.CompileName);
      } else {
        return IdProtect(cl.EnclosingModuleDefinition.CompileName) + "." + IdProtect(cl.CompileName);
      }
    }

    protected override void TypeName_SplitArrayName(Type type, out Type innermostElementType, out string brackets) {
      Contract.Requires(type != null);

      type = DatatypeWrapperEraser.SimplifyType(Options, type);
      var at = type.AsArrayType;
      if (at != null && at.Dims == 1 && !DatatypeWrapperEraser.SimplifyType(Options, type.TypeArgs[0]).IsTypeParameter) {
        TypeName_SplitArrayName(type.TypeArgs[0], out innermostElementType, out brackets);
        brackets = TypeNameArrayBrackets(at.Dims) + brackets;
      } else {
        innermostElementType = type;
        brackets = "";
      }
    }

    protected override string TypeNameArrayBrackets(int dims) {
      return Util.Repeat(dims, "[]");
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      if (!isInParam) {
        return false;
      }

      wr.Write($"{prefix}{TypeName(type, wr, tok)} {name}");
      return true;
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs,
      ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(variance != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(variance.Count == typeArgs.Count);
      string s = IdProtect(fullCompileName);
      if (typeArgs.Count != 0 && !omitTypeArguments) {
        s += "<" + BoxedTypeNames(typeArgs, wr, tok) + ">";
      }
      return s;
    }

    // We write an extern class as a base class that the actual extern class
    // needs to extend, so the extern methods and functions need to be abstract
    // in the base class
    protected override bool IncludeExternMembers { get => true; }

    //
    // An example to show how type parameters are dealt with:
    //
    //   class Class<T /* needs auto-initializer */, U /* does not */> {
    //     private String sT; // type descriptor for T
    //
    //     // Fields are assigned in the constructor because some will
    //     // depend on a type parameter
    //     public T t;
    //     public U u;
    //
    //     public Class(String sT) {
    //       this.sT = sT;
    //       this.t = dafny.Helpers.getDefault(sT);
    //       // Note: The field must be assigned a real value before being read!
    //       this.u = null;
    //     }
    //
    //     public __ctor(U u) {
    //       this.u = u;
    //     }
    //   }
    //
    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string /*?*/ fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> /*?*/ superClasses, IToken tok, ConcreteSyntaxTree wr) {
      var javaName = isExtern ? FormatExternBaseClassName(name) : name;
      var filename = $"{ModulePath}/{javaName}.java";
      var w = wr.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Class {javaName}");
      w.WriteLine($"// Dafny class {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      EmitImports(w, out _);
      w.WriteLine();
      //TODO: Fix implementations so they do not need this suppression
      EmitSuppression(w);
      var abstractness = isExtern ? "abstract " : "";
      w.Write($"public {abstractness}class {javaName}{TypeParameters(typeParameters)}");
      string sep;
      // Since Java does not support multiple inheritance, we are assuming a list of "superclasses" is a list of interfaces
      if (superClasses != null) {
        sep = " implements ";
        foreach (var trait in superClasses) {
          if (!trait.IsObject) {
            w.Write($"{sep}{TypeName(trait, w, tok)}");
            sep = ", ";
          }
        }
      }
      var wBody = w.NewBlock("");
      var wTypeFields = wBody.Fork();

      wBody.Write($"public {javaName}(");
      var wCtorParams = wBody.Fork();
      var wCtorBody = wBody.NewBlock(")", "");

      if (typeParameters != null) {
        sep = "";
        foreach (var ta in TypeArgumentInstantiation.ListFromFormals(typeParameters)) {
          if (NeedsTypeDescriptor(ta.Formal)) {
            var fieldName = FormatTypeDescriptorVariable(ta.Formal.CompileName);
            var decl = $"{DafnyTypeDescriptor}<{BoxedTypeName(ta.Actual, wTypeFields, ta.Formal.tok)}> {fieldName}";
            wTypeFields.WriteLine($"private {decl};");
            if (ta.Formal.Parent == cls) {
              wCtorParams.Write($"{sep}{decl}");
            }
            wCtorBody.WriteLine($"this.{fieldName} = {TypeDescriptor(ta.Actual, wCtorBody, ta.Formal.tok)};");
            sep = ", ";
          }
        }
      }

      // make sure the (static fields associated with the) type method come after the Witness static field
      var wTypeMethod = wBody;
      var wRestOfBody = wBody.Fork();
      var targetTypeName = BoxedTypeName(UserDefinedType.FromTopLevelDecl(cls.tok, cls, null), wTypeMethod, cls.tok);
      EmitTypeMethod(cls, javaName, typeParameters, typeParameters, targetTypeName, null, wTypeMethod);

      if (fullPrintName != null) {
        // By emitting a toString() method, printing an object will give the same output as with other target languages.
        EmitToString(fullPrintName, wBody);
      }

      return new ClassWriter(this, wRestOfBody, wCtorBody);
    }

    private void EmitToString(string fullPrintName, ConcreteSyntaxTree wr) {
      wr.WriteLine("@Override");
      wr.NewBlock("public java.lang.String toString()")
        .WriteLine($"return \"{fullPrintName}\";");
    }

    /// <summary>
    /// Generate the "_typeDescriptor" method for a generated class.
    /// "enclosingType" is allowed to be "null", in which case the target values are assumed to be references.
    /// </summary>
    private void EmitTypeMethod(TopLevelDecl/*?*/ enclosingTypeDecl, string typeName, List<TypeParameter> typeParams, List<TypeParameter> usedTypeParams, string targetTypeName, string/*?*/ initializer, ConcreteSyntaxTree wr) {
      string typeDescriptorExpr = null;
      if (enclosingTypeDecl == null) {
        // use reference type
        typeDescriptorExpr = $"{DafnyTypeDescriptor}.referenceWithInitializer({StripTypeParameters(targetTypeName)}.class, () -> {initializer ?? "null"})";
      } else {
        var targetType = DatatypeWrapperEraser.SimplifyType(Options, UserDefinedType.FromTopLevelDecl(enclosingTypeDecl.tok, enclosingTypeDecl), true);
        var w = (enclosingTypeDecl as RedirectingTypeDecl)?.Witness != null ? "Witness" : null;
        switch (AsJavaNativeType(targetType)) {
          case JavaNativeType.Byte:
            typeDescriptorExpr = $"{DafnyTypeDescriptor}.byteWithDefault({w ?? "(byte)0"})";
            break;
          case JavaNativeType.Short:
            typeDescriptorExpr = $"{DafnyTypeDescriptor}.shortWithDefault({w ?? "(short)0"})";
            break;
          case JavaNativeType.Int:
            typeDescriptorExpr = $"{DafnyTypeDescriptor}.intWithDefault({w ?? "0"})";
            break;
          case JavaNativeType.Long:
            typeDescriptorExpr = $"{DafnyTypeDescriptor}.longWithDefault({w ?? "0L"})";
            break;
          case null:
            if (targetType.IsBoolType) {
              typeDescriptorExpr = $"{DafnyTypeDescriptor}.booleanWithDefault({w ?? "false"})";
            } else if (targetType.IsCharType) {
              if (UnicodeCharEnabled) {
                typeDescriptorExpr = $"{DafnyTypeDescriptor}.unicodeCharWithDefault((int){w ?? CharType.DefaultValueAsString})";
              } else {
                typeDescriptorExpr = $"{DafnyTypeDescriptor}.charWithDefault({w ?? CharType.DefaultValueAsString})";
              }
            } else if (targetType.IsTypeParameter) {
              typeDescriptorExpr = TypeDescriptor(targetType, wr, enclosingTypeDecl.tok);
            } else {
              var d = initializer ?? DefaultValue(targetType, wr, enclosingTypeDecl.tok);
              typeDescriptorExpr = $"{DafnyTypeDescriptor}.referenceWithInitializer({StripTypeParameters(targetTypeName)}.class, () -> {d})";
            }
            break;
        }
      }

      if (typeParams.Count == 0) {
        // a static context in Java does not see the enclosing type parameters
        wr.WriteLine($"private static final {DafnyTypeDescriptor}<{StripTypeParameters(targetTypeName)}> _TYPE = {typeDescriptorExpr};");
        typeDescriptorExpr = "_TYPE";
      }
      wr.Write($"public static {TypeParameters(typeParams, " ")}{DafnyTypeDescriptor}<{targetTypeName}> {TypeMethodName}(");
      if (typeParams.Count != 0) {
        var typeDescriptorParams = typeParams.Where(tp => NeedsTypeDescriptor(tp)).ToList();
        wr.Write(typeDescriptorParams.Comma(tp => $"{DafnyTypeDescriptor}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp.CompileName)}"));
      }
      var wTypeMethodBody = wr.NewBlock(")", "");
      var typeDescriptorCast = $"({DafnyTypeDescriptor}<{targetTypeName}>) ({DafnyTypeDescriptor}<?>)";
      wTypeMethodBody.WriteLine($"return {typeDescriptorCast} {typeDescriptorExpr};");
    }

    private string CastIfSmallNativeType(Type t) {
      var nt = AsNativeType(t);
      return nt == null ? "" : CastIfSmallNativeType(nt);
    }

    private string CastIfSmallNativeType(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return "(byte) ";
        case JavaNativeType.Short: return "(short) ";
        default: return "";
      }
    }

    private static string TranslateEscapes(string s) {
      s = Util.ReplaceNullEscapesWithCharacterEscapes(s);

      s = Util.UnicodeEscapesToUtf16Escapes(s);

      // Java \u escapes are translated before parsing, so we need to convert to escapes
      // that aren't for characters that will mess up paring the string or character literal.
      s = Util.ReplaceTokensWithEscapes(s, Util.Utf16Escape, match => {
        return match.Value switch {
          "\\u000a" => "\\n",
          "\\u000d" => "\\r",
          "\\u0022" => "\\\"",
          "\\u0027" => "\\\'",
          "\\u005c" => "\\\\",
          _ => match.Value
        };
      });

      return s;
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write($"({TypeName(e.Type, wr, e.tok)}) null");
      } else if (e.Value is bool value) {
        wr.Write(value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        var v = (string)e.Value;
        if (UnicodeCharEnabled && Util.MightContainNonAsciiCharacters(v, false)) {
          wr.Write($"{Util.UnescapedCharacters(Options, v, false).Single()}");
        } else {
          wr.Write($"'{TranslateEscapes(v)}'");
        }
      } else if (e is StringLiteralExpr str) {
        wr.Write(UnicodeCharEnabled ? $"{DafnySeqClass}.asUnicodeString(" : $"{DafnySeqClass}.asString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) is NativeType nt) {
        EmitNativeIntegerLiteral((BigInteger)e.Value, nt, wr);
      } else if (e.Value is BigInteger i) {
        if (i.IsZero) {
          wr.Write("java.math.BigInteger.ZERO");
        } else if (i.IsOne) {
          wr.Write("java.math.BigInteger.ONE");
        } else if (long.MinValue <= i && i <= long.MaxValue) {
          wr.Write($"java.math.BigInteger.valueOf({i}L)");
        } else {
          wr.Write($"new java.math.BigInteger(\"{i}\")");
        }
      } else if (e.Value is BaseTypes.BigDec n) {
        if (0 <= n.Exponent) {
          wr.Write($"new {DafnyBigRationalClass}(new java.math.BigInteger(\"{n.Mantissa}");
          for (int j = 0; j < n.Exponent; j++) {
            wr.Write("0");
          }
          wr.Write("\"), java.math.BigInteger.ONE)");
        } else {
          wr.Write($"new {DafnyBigRationalClass}(");
          wr.Write($"new java.math.BigInteger(\"{n.Mantissa}\")");
          wr.Write(", new java.math.BigInteger(\"1");
          for (int j = n.Exponent; j < 0; j++) {
            wr.Write("0");
          }
          wr.Write("\"))");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      if (!isVerbatim) {
        wr.Write($"\"{TranslateEscapes(str)}\"");
      } else {
        //TODO: This is taken from Go and JS since Java doesn't have raw string literals, modify and make better if possible.
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

    void EmitNativeIntegerLiteral(BigInteger value, NativeType nt, ConcreteSyntaxTree wr) {
      GetNativeInfo(nt.Sel, out var name, out var literalSuffix, out _);
      var intValue = value;
      if (intValue > long.MaxValue) {
        // The value must be a 64-bit unsigned integer, since it has a native
        // type and unsigned long is the biggest native type
        Contract.Assert(intValue <= ulong.MaxValue);

        // Represent the value as a signed 64-bit integer
        intValue -= ulong.MaxValue + BigInteger.One;
      } else if (nt.Sel == NativeType.Selection.UInt && intValue > int.MaxValue) {
        // Represent the value as a signed 32-bit integer
        intValue -= uint.MaxValue + BigInteger.One;
      }
      wr.Write($"{CastIfSmallNativeType(nt)}{intValue}{literalSuffix}");
    }

    protected string GetNativeDefault(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return "(byte) 0";
        case JavaNativeType.Short: return "(short) 0";
        case JavaNativeType.Int: return "0";
        case JavaNativeType.Long: return "0L";
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix,
      out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (AsJavaNativeType(sel)) {
        case JavaNativeType.Byte: name = "byte"; needsCastAfterArithmetic = true; break;
        case JavaNativeType.Short: name = "short"; needsCastAfterArithmetic = true; break;
        case JavaNativeType.Int: name = "int"; break;
        case JavaNativeType.Long: name = "long"; literalSuffix = "L"; break;
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    private string GetNativeTypeName(NativeType nt, bool boxed = false) {
      return boxed ? GetBoxedNativeTypeName(nt) : base.GetNativeTypeName(nt);
    }

    private string GetBoxedNativeTypeName(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return "java.lang.Byte";
        case JavaNativeType.Short: return "java.lang.Short";
        case JavaNativeType.Int: return "java.lang.Integer";
        case JavaNativeType.Long: return "java.lang.Long";
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    // Note the (semantically iffy) distinction between a *primitive type*,
    // being one of the eight Java primitive types, and a NativeType, which can
    // only be one of the integer types.
    // Note also that in --unicode-char mode, we have our own CodePoint boxing type
    // that boxes int values that are actually Dafny char values.
    private bool IsJavaPrimitiveType(Type type) {
      return type.IsBoolType || type.IsCharType || AsNativeType(type) != null;
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      var custom =
        (enclosingMethod != null && (enclosingMethod.IsTailRecursive || NeedsCustomReceiver(enclosingMethod))) ||
        (enclosingFunction != null && (enclosingFunction.IsTailRecursive || NeedsCustomReceiver(enclosingFunction))) ||
        thisContext is NewtypeDecl ||
        thisContext is TraitDecl;
      wr.Write(custom ? "_this" : "this");
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, ConcreteSyntaxTree wr) {
      // Note that type can be null to represent the native object type.
      // See comment on NativeObjectType.
      if (type is { AsArrayType: { } }) {
        arrays.Add(type.AsArrayType.Dims);
      }
      if (type is { IsDatatype: true, AsDatatype: TupleTypeDecl tupleDecl }) {
        tuples.Add(tupleDecl.NonGhostDims);
      }
      if (type is { IsTypeParameter: true }) {
        EmitSuppression(wr);
      }
      wr.Write("{0} {1}", type != null ? TypeName(type, wr, tok) : "Object", name);
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null); // follows from precondition
      } else if (rhs != null) {
        wr.WriteLine($" = {rhs};");
      } else if (type is { IsIntegerType: true }) {
        wr.WriteLine(" = java.math.BigInteger.ZERO;");
      } else {
        wr.WriteLine(";");
      }
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, ConcreteSyntaxTree wr, Type t) {
      DeclareLocalVar(name, t, tok, leaveRoomForRhs, rhs, wr);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (elements.Count == 0) {
        wr.Write($"{CollectionTypeUnparameterizedName(ct)}.<{BoxedTypeName(ct.Arg, wr, tok)}> empty(");
        if (ct is SeqType) {
          wr.Write(TypeDescriptor(ct.Arg, wr, tok));
        }
        wr.Write(")");
        return;
      }
      wr.Write($"{CollectionTypeUnparameterizedName(ct)}.of(");
      string sep = "";
      if (ct is SeqType && (!IsJavaPrimitiveType(ct.Arg) || (UnicodeCharEnabled && ct.Arg.IsCharType))) {
        wr.Write(TypeDescriptor(ct.Arg, wr, tok));
        sep = ", ";
      }

      foreach (Expression e in elements) {
        wr.Write(sep);
        var elementWriter = wr.Fork();
        elementWriter = EmitCoercionIfNecessary(e.Type, NativeObjectType, Token.NoToken, elementWriter);
        elementWriter.Append(Expr(e, inLetExprBody, wStmts));
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnyMapClass}.fromElements");
      wr.Write("(");
      string sep = "";
      foreach (ExpressionPair p in elements) {
        wr.Write(sep);
        wr.Write($"new {DafnyTupleClass(2)}(");
        wr.Append(Expr(p.A, inLetExprBody, wStmts));
        wr.Write(", ");
        wr.Append(Expr(p.B, inLetExprBody, wStmts));
        wr.Write(")");
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType, out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = IdProtect((string)idParam);
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          if (idParam == null) {
            // Works on both fixed array types like array<int> (=> BigInteger[])
            // or generic array types like array<A> (=> Object) and (unlike most
            // of java.lang.reflect.Array) is fast
            preString = "java.lang.reflect.Array.getLength(";
            postString = ")";
          } else {
            compiledName = "dim" + (int)idParam;
          }
          if (id == SpecialField.ID.ArrayLength) {
            preString = "java.math.BigInteger.valueOf(" + preString;
            postString = postString + ")";
          }
          break;
        case SpecialField.ID.Floor:
          compiledName = "ToBigInteger()";
          break;
        case SpecialField.ID.IsLimit:
          preString = "dafny.BigOrdinal.IsLimit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = "dafny.BigOrdinal.IsSucc(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = "dafny.BigOrdinal.Offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = "dafny.BigOrdinal.IsNat(";
          postString = ")";
          break;
        case SpecialField.ID.Keys:
          compiledName = "keySet()";
          break;
        case SpecialField.ID.Values:
          compiledName = "valueSet()";
          break;
        case SpecialField.ID.Items:
          var mapType = receiverType.AsMapType;
          Contract.Assert(mapType != null);
          var errorWr = new ConcreteSyntaxTree();
          compiledName = $"<{BoxedTypeName(mapType.Domain, errorWr, Token.NoToken)}, {BoxedTypeName(mapType.Range, errorWr, Token.NoToken)}>entrySet()";
          break;
        case SpecialField.ID.Reads:
          compiledName = "_reads";
          break;
        case SpecialField.ID.Modifies:
          compiledName = "_modifies";
          break;
        case SpecialField.ID.New:
          compiledName = "_new";
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
      Type expectedType, string/*?*/ additionalCustomParameter, bool internalAccess = false) {
      var memberStatus = DatatypeWrapperEraser.GetMemberStatus(Options, member);
      if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.Identity) {
        return SimpleLvalue(obj);
      } else if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue) {
        return SimpleLvalue(w => w.Write("true"));
      } else if (member is SpecialField sf && !(member is ConstantField)) {
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
        if (compiledName.Length != 0) {
          if (member.EnclosingClass is DatatypeDecl) {
            if (member.EnclosingClass is TupleTypeDecl && sf.Type.Subst(typeMap).IsCharType && UnicodeCharEnabled) {
              return SuffixLvalue(obj, $".{compiledName}().value()");
            } else {
              return SuffixLvalue(obj, $".{compiledName}()");
            }
          } else {
            return SuffixLvalue(obj, $".{compiledName}");
          }
        } else {
          // Assume it's already handled by the caller
          return SimpleLvalue(obj);
        }
      } else if (member is Function fn) {
        var wr = new ConcreteSyntaxTree();
        EmitNameAndActualTypeArgs(IdName(member), TypeArgumentInstantiation.ToActuals(ForTypeParameters(typeArgs, member, false)), member.tok, wr);
        var needsEtaConversion = typeArgs.Any()
               || additionalCustomParameter != null
               || (UnicodeCharEnabled &&
                  (fn.ResultType.IsCharType || fn.Formals.Any(f => f.Type.IsCharType)));
        if (!needsEtaConversion) {
          var nameAndTypeArgs = wr.ToString();
          return SuffixLvalue(obj, $"::{nameAndTypeArgs}");
        } else {
          // We need an eta conversion to adjust for the difference in arity or coerce inputs/outputs.
          // (T0 a0, T1 a1, ...) -> obj.F(rtd0, rtd1, ..., additionalCustomParameter, a0, a1, ...)
          wr.Write("(");
          var sep = "";
          EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), fn.tok, wr, ref sep);
          if (additionalCustomParameter != null) {
            wr.Write("{0}{1}", sep, additionalCustomParameter);
            sep = ", ";
          }
          var prefixWr = new ConcreteSyntaxTree();
          var prefixSep = "";
          prefixWr.Write("(");
          foreach (var arg in fn.Formals) {
            if (!arg.IsGhost) {
              var name = idGenerator.FreshId("_eta");
              var ty = arg.Type.Subst(typeMap);
              prefixWr.Write($"{prefixSep}{BoxedTypeName(ty, prefixWr, arg.tok)} {name}");
              wr.Write(sep);
              var coercedWr = EmitCoercionIfNecessary(NativeObjectType, ty, arg.tok, wr);
              coercedWr.Write(name);
              sep = ", ";
              prefixSep = ", ";
            }
          }
          prefixWr.Write(") -> ");
          wr.Write(")");

          if (fn.ResultType.IsCharType && UnicodeCharEnabled) {
            prefixWr.Write("dafny.CodePoint.valueOf(");
            wr.Write(")");
          }

          return EnclosedLvalue(prefixWr.ToString(), obj, $".{wr}");
        }
      } else {
        var field = (Field)member;
        ILvalue lvalue;
        if (member.IsStatic) {
          lvalue = SimpleLvalue(w => {
            w.Write("{0}.{1}(", TypeName_Companion(objType, w, member.tok, member), IdName(member));
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.tok, w);
            w.Write(")");
          });
        } else if (NeedsCustomReceiver(member) && !(member.EnclosingClass is TraitDecl)) {
          // instance const in a newtype
          Contract.Assert(typeArgs.Count == 0);
          lvalue = SimpleLvalue(w => {
            w.Write("{0}.{1}(", TypeName_Companion(objType, w, member.tok, member), IdName(member));
            obj(w);
            w.Write(")");
          });
        } else if (internalAccess && (member is ConstantField || member.EnclosingClass is TraitDecl)) {
          lvalue = SuffixLvalue(obj, $"._{member.CompileName}");
        } else if (internalAccess) {
          lvalue = SuffixLvalue(obj, $".{IdName(member)}");
        } else if (member is ConstantField) {
          lvalue = SimpleLvalue(w => {
            obj(w);
            w.Write(".{0}(", IdName(member));
            EmitTypeDescriptorsActuals(ForTypeDescriptors(typeArgs, member.EnclosingClass, member, false), member.tok, w);
            w.Write(")");
          });
        } else if (member.EnclosingClass is TraitDecl) {
          lvalue = GetterSetterLvalue(obj, IdName(member), $"set_{IdName(member)}");
        } else {
          lvalue = SuffixLvalue(obj, $".{IdName(member)}");
        }
        return CoercedLvalue(lvalue, field.Type, expectedType);
      }
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      wr.Write($"{source}.is_{ctor.CompileName}()");
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      if (type is UserDefinedType udt) {
        var name = udt.ResolvedClass is TraitDecl ? udt.FullCompanionCompileName : FullTypeName(udt, member, true);
        return TypeName_UDT(name, udt, wr, tok, true);
      } else {
        return TypeName(type, wr, tok, member);
      }
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      List<ConcreteSyntaxTree> wIndices;
      var w = EmitArraySelect(indices.Count, out wIndices, elmtType, wr);
      for (int i = 0; i < indices.Count; i++) {
        if (!int.TryParse(indices[i], out _)) {
          wIndices[i].Write($"{DafnyHelpersClass}.toInt({indices[i]})");
        } else {
          wIndices[i].Write(indices[i]);
        }
      }
      return w;
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      List<ConcreteSyntaxTree> wIndices;
      var w = EmitArraySelect(indices.Count, out wIndices, elmtType, wr);

      for (int i = 0; i < indices.Count; i++) {
        TrParenExprAsInt(indices[i], wIndices[i], inLetExprBody, wStmts);
      }

      return w;
    }

    private ConcreteSyntaxTree EmitArraySelect(int dimCount, out List<ConcreteSyntaxTree> wIndices, Type elmtType, ConcreteSyntaxTree wr) {
      elmtType = DatatypeWrapperEraser.SimplifyType(Options, elmtType);
      wIndices = new List<ConcreteSyntaxTree>();
      ConcreteSyntaxTree w;
      if (dimCount == 1) {
        if (elmtType.IsTypeParameter) {
          wr.Write($"{FormatTypeDescriptorVariable(elmtType.AsTypeParameter)}.getArrayElement(");
          w = wr.Fork();
          wr.Write(", ");
          wIndices.Add(wr.Fork());
          wr.Write(")");
        } else {
          w = wr.Fork();
          wr.Write("[");
          wIndices.Add(wr.Fork());
          wr.Write("]");
        }
      } else {
        if (elmtType.IsTypeParameter) {
          w = wr.Fork();
          wr.Write(".get(");
          for (int i = 0; i < dimCount; i++) {
            if (i > 0) {
              wr.Write(", ");
            }
            wIndices.Add(wr.Fork());
          }
          wr.Write(")");
        } else {
          wr.Write($"(({TypeName(elmtType, wr, Token.NoToken)}{Repeat("[]", dimCount)}) ((");
          w = wr.Fork();
          wr.Write(").elmts))");
          for (int i = 0; i < dimCount; i++) {
            wr.Write("[");
            wIndices.Add(wr.Fork());
            wr.Write("]");
          }
        }
      }
      return w;
    }

    protected override (ConcreteSyntaxTree/*array*/, ConcreteSyntaxTree/*rhs*/) EmitArrayUpdate(List<string> indices, Type elementType, ConcreteSyntaxTree wr) {
      elementType = DatatypeWrapperEraser.SimplifyType(Options, elementType);
      ConcreteSyntaxTree wArray, wRhs;
      if (indices.Count == 1) {
        if (elementType.IsTypeParameter) {
          wr.Write($"{FormatTypeDescriptorVariable(elementType.AsTypeParameter)}.setArrayElement(");
          wArray = wr.Fork();
          wr.Write($", {DafnyHelpersClass}.toInt({indices[0]}), ");
          wRhs = wr.Fork();
          wr.Write(")");
        } else {
          wArray = wr.Fork();
          wr.Write($"[{DafnyHelpersClass}.toInt({indices[0]})] = ");
          wRhs = wr.Fork();
        }
      } else {
        if (elementType.IsTypeParameter) {
          wArray = wr.Fork();
          wr.Write($".set({indices.Comma(ix => $"{DafnyHelpersClass}.toInt({ix})")}, ");
          wRhs = wr.Fork();
          wr.Write(")");
        } else {
          wr.Write($"(({TypeName(elementType, wr, Token.NoToken)}{Repeat("[]", indices.Count)}) (");
          wArray = wr.Fork();
          wr.Write($").elmts){Util.Comma("", indices, ix => $"[{DafnyHelpersClass}.toInt({ix})]")} = ");
          wRhs = wr.Fork();
        }
      }
      return (wArray, wRhs);
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
        bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (fromArray) {
        wr.Write($"{DafnySeqClass}.fromRawArrayRange({TypeDescriptor(source.Type.NormalizeExpand().TypeArgs[0], wr, source.tok)}, ");
      }
      TrParenExpr(source, wr, inLetExprBody, wStmts);
      if (fromArray) {
        wr.Write(", ");
        if (lo != null) {
          TrExprAsInt(lo, wr, inLetExprBody, wStmts);
        } else {
          wr.Write("0");
        }
        wr.Write(", ");
        if (hi != null) {
          TrExprAsInt(hi, wr, inLetExprBody, wStmts);
        } else {
          wr.Write("java.lang.reflect.Array.getLength");
          TrParenExpr(source, wr, inLetExprBody, wStmts);
        }
        wr.Write(")");
      } else {
        if (lo != null && hi != null) {
          wr.Write(".subsequence(");
          TrExprAsInt(lo, wr, inLetExprBody, wStmts);
          wr.Write(", ");
          TrExprAsInt(hi, wr, inLetExprBody, wStmts);
          wr.Write(")");
        } else if (lo != null) {
          wr.Write(".drop");
          TrParenExpr(lo, wr, inLetExprBody, wStmts);
        } else if (hi != null) {
          wr.Write(".take");
          TrParenExpr(hi, wr, inLetExprBody, wStmts);
        }
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      // Taken from C# compiler, assuming source is a DafnySequence type.
      if (source.Type.AsMultiSetType != null) {
        wr = EmitCoercionIfNecessary(from: NativeObjectType, to: Type.Int, tok: source.tok, wr: wr);
        wr.Write($"{DafnyMultiSetClass}.<{BoxedTypeName(source.Type.AsMultiSetType.Arg, wr, Token.NoToken)}>multiplicity(");
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(", ");
        wr.Append(Expr(index, inLetExprBody, wStmts));
        wr.Write(")");
      } else if (source.Type.AsMapType != null) {
        wr = EmitCoercionIfNecessary(from: NativeObjectType, to: source.Type.AsMapType.Range, tok: source.tok, wr: wr);
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        TrParenExpr(".get", index, wr, inLetExprBody, wStmts);
      } else {
        wr = EmitCoercionIfNecessary(from: NativeObjectType, to: source.Type.AsCollectionType.Arg, tok: source.tok, wr: wr);
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".select");
        TrParenExprAsInt(index, wr, inLetExprBody, wStmts);
      }
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      TrParenExpr(expr.E, wr, inLetExprBody, wStmts);
      wr.Write(".asDafnyMultiset()");
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
        CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (source.Type.AsSeqType != null) {
        wr.Write($"{DafnySeqClass}.<{BoxedTypeName(resultCollectionType.Arg, wr, Token.NoToken)}>update(");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(", ");
        TrExprAsInt(index, wr, inLetExprBody, wStmts);
      } else if (source.Type.AsMapType != null) {
        var mapType = (MapType)resultCollectionType;
        wr.Write($"{DafnyMapClass}.<{BoxedTypeName(mapType.Domain, wr, Token.NoToken)}, {BoxedTypeName(mapType.Range, wr, Token.NoToken)}>update(");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(", ");
        wr.Append(Expr(index, inLetExprBody, wStmts));
      } else if (source.Type.AsMultiSetType != null) {
        wr.Write($"{DafnyMultiSetClass}.<{BoxedTypeName(resultCollectionType.Arg, wr, Token.NoToken)}>update(");
        wr.Append(Expr(source, inLetExprBody, wStmts));
        wr.Write(", ");
        wr.Append(Expr(index, inLetExprBody, wStmts));
      } else {
        TrParenExpr(source, wr, inLetExprBody, wStmts);
        wr.Write(".update(");
        wr.Append(Expr(index, inLetExprBody, wStmts));
      }
      wr.Write(", ");
      var inner = Expr(value, inLetExprBody, wStmts);
      wr.Append(CoercionIfNecessary(value.Type, NativeObjectType, Token.NoToken, inner));
      wr.Write(")");
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
      bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      string nativeName = null, literalSuffix = null;
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
      }
      var leftShift = nativeType == null ? ".shiftLeft" : "<<";
      var rightShift = nativeType == null ? ".shiftRight" : ">>>";
      // ( e0 op1 e1) | (e0 op2 (width - e1))
      if (needsCast) {
        wr.Write("(" + nativeName + ")(" + CastIfSmallNativeType(e0.Type) + "(");
      }
      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? leftShift : rightShift, isRotateLeft, nativeType, true, wr, inLetExprBody, wStmts, tr);
      wr.Write(")");
      if (nativeType == null) {
        wr.Write(".or");
      } else {
        wr.Write("|");
      }
      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? rightShift : leftShift, !isRotateLeft, nativeType, false, wr, inLetExprBody, wStmts, tr);
      wr.Write(")))");
      if (needsCast) {
        wr.Write("))");
      }
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, NativeType nativeType /*?*/, bool firstOp,
        ConcreteSyntaxTree wr, bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }
      tr(e0, wr, inLetExprBody, wStmts);
      wr.Write($" {op} ");
      if (!firstOp) {
        wr.Write($"({bv.Width} - ");
      }
      wr.Write("((");
      tr(e1, wr, inLetExprBody, wStmts);
      wr.Write(")");
      if (AsNativeType(e1.Type) == null) {
        wr.Write(".intValue()");
      }
      if (!firstOp) {
        wr.Write(")");
      }
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }
      // --- Before
      if (bvType.NativeType == null) {
        wr.Write("((");
      } else {
        wr.Write($"({nativeName}) {CastIfSmallNativeType(bvType)}((");
      }
      // --- Middle
      var middle = wr.Fork();
      // --- After
      // do the truncation, if needed
      if (bvType.NativeType == null) {
        wr.Write($").and((java.math.BigInteger.ONE.shiftLeft({bvType.Width})).subtract(java.math.BigInteger.ONE)))");
      } else {
        if (bvType.NativeType.Bitwidth != bvType.Width) {
          // print in hex, because that looks nice
          wr.Write($") & {CastIfSmallNativeType(bvType)}0x{(1UL << bvType.Width) - 1:X}{literalSuffix})");
        } else {
          wr.Write("))");  // close the parentheses for the cast
        }
      }
      return middle;
    }

    protected override bool CompareZeroUsingSign(Type type) {
      // Everything is boxed, so everything benefits from avoiding explicit 0
      return true;
    }

    protected override ConcreteSyntaxTree EmitSign(Type type, ConcreteSyntaxTree wr) {
      ConcreteSyntaxTree w;
      var nt = AsNativeType(type);
      if (nt == null) {
        w = wr.Fork();
        wr.Write(".signum()");
      } else if (nt.LowerBound >= 0) {
        wr.Write("(");
        w = wr.Fork();
        wr.Write(" == 0 ? 0 : 1)");
      } else {
        wr.Write($"{HelperClass(nt)}.signum(");
        w = wr.Fork();
        wr.Write(")");
      }
      return w;
    }

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      var w = CompileDatatypeBase(dt, wr);
      CompileDatatypeConstructors(dt, wr);
      return w;
    }

    IClassWriter CompileDatatypeBase(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      var DtT_TypeArgs = TypeParameters(dt.TypeArgs);
      var justTypeArgs = dt.TypeArgs.Count == 0 ? "" : " " + DtT_TypeArgs;
      var DtT_protected = IdName(dt) + DtT_TypeArgs;
      var simplifiedType = DatatypeWrapperEraser.SimplifyType(Options, UserDefinedType.FromTopLevelDecl(dt.tok, dt));
      var simplifiedTypeName = TypeName(simplifiedType, wr, dt.tok);

      var filename = $"{ModulePath}/{IdName(dt)}.java";
      wr = wr.NewFile(filename);
      FileCount += 1;
      wr.WriteLine($"// Class {DtT_protected}");
      wr.WriteLine($"// Dafny class {DtT_protected} compiled into Java");
      wr.WriteLine($"package {ModuleName};");
      wr.WriteLine();
      EmitImports(wr, out _);
      wr.WriteLine();
      //TODO: Figure out how to resolve type checking warnings
      // from here on, write everything into the new block created here:
      EmitSuppression(wr);
      var btw = wr.NewNamedBlock("public{0} class {1}", dt.IsRecordType ? "" : " abstract", DtT_protected);
      wr = btw;

      // constructor
      if (dt.IsRecordType) {
        DatatypeFieldsAndConstructor(dt.Ctors[0], 0, wr);
      } else {
        wr.WriteLine($"public {IdName(dt)}() {{ }}");
      }

      var usedTypeArgs = UsedTypeParameters(dt);
      ConcreteSyntaxTree wDefault;
      wr.WriteLine();
      if (dt.TypeArgs.Count == 0) {
        wr.Write($"private static final {simplifiedTypeName} theDefault = ");
        wDefault = wr.Fork();
        wr.WriteLine(";");
        var w = wr.NewBlock($"public static {simplifiedTypeName} Default()");
        w.WriteLine("return theDefault;");
      } else {
        wr.Write($"public static{justTypeArgs} {simplifiedTypeName} Default(");
        var typeParameters = Util.Comma(usedTypeArgs, tp => $"{tp.CompileName} {FormatDefaultTypeParameterValue(tp)}");
        wr.Write(typeParameters);
        var w = wr.NewBlock(")");
        var sep = "";
        var typeArguments = TypeArgumentInstantiation.ListFromFormals(dt.TypeArgs);
        WriteRuntimeTypeDescriptorsFormals(ForTypeDescriptors(typeArguments, dt, null, false), w, ref sep,
          tp => {
            sep = "";
            return
              $"{DafnyTypeDescriptor}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)} = ({DafnyTypeDescriptor}<{tp.CompileName}>)dafny.TypeDescriptor.OBJECT;\n    ";
          });

        w.Write("return ");
        wDefault = w.Fork();
        w.WriteLine(";");
      }
      var groundingCtor = dt.GetGroundingCtor();
      if (groundingCtor.IsGhost) {
        wDefault.Write(ForcePlaceboValue(simplifiedType, wDefault, dt.tok));
      } else if (DatatypeWrapperEraser.GetInnerTypeOfErasableDatatypeWrapper(Options, dt, out var innerType)) {
        wDefault.Write(DefaultValue(innerType, wDefault, dt.tok));
      } else {
        var nonGhostFormals = groundingCtor.Formals.Where(f => !f.IsGhost).ToList();
        var args = nonGhostFormals.Comma(f => DefaultValue(f.Type, wDefault, f.tok));
        EmitDatatypeValue(dt, groundingCtor,
          dt.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(dt.tok, tp)),
          dt is CoDatatypeDecl, args, wDefault);
      }

      var targetTypeName = BoxedTypeName(UserDefinedType.FromTopLevelDecl(dt.tok, dt, null), wr, dt.tok);
      var arguments = usedTypeArgs.Comma(tp => DefaultValue(new UserDefinedType(tp), wDefault, dt.tok, true));
      EmitTypeMethod(dt, IdName(dt), dt.TypeArgs, usedTypeArgs, targetTypeName, $"Default({arguments})", wr);

      // create methods
      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        wr.Write($"public static{justTypeArgs} {DtT_protected} {DtCreateName(ctor)}(");
        WriteFormals("", ctor.Formals, wr);
        wr.NewBlock(")")
          .WriteLine($"return new {DtCtorDeclarationName(ctor, dt.TypeArgs)}({ctor.Formals.Where(f => !f.IsGhost).Comma(FormalName)});");
      }

      if (dt.IsRecordType) {
        // Also emit a "create_<ctor_name>" method that thunks to "create",
        // to provide a more uniform interface.

        var ctor = dt.Ctors[0];
        wr.Write($"public static{justTypeArgs} {DtT_protected} create_{ctor.CompileName}(");
        WriteFormals("", ctor.Formals, wr);
        wr.NewBlock(")")
          .WriteLine($"return create({ctor.Formals.Where(f => !f.IsGhost).Comma(FormalName)});");
      }

      // query properties
      foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        if (dt.IsRecordType) {
          wr.WriteLine($"public boolean is_{ctor.CompileName}() {{ return true; }}");
        } else {
          wr.WriteLine($"public boolean is_{ctor.CompileName}() {{ return this instanceof {dt.CompileName}_{ctor.CompileName}; }}");
        }
      }
      if (dt is CoDatatypeDecl) {
        wr.WriteLine($"public abstract {DtT_protected} Get();");
      }
      if (dt.HasFinitePossibleValues) {
        Contract.Assert(dt.TypeArgs.Count == 0);
        var w = wr.NewNamedBlock($"public static java.util.ArrayList<{DtT_protected}> AllSingletonConstructors()");
        string arraylist = "singleton_iterator";
        w.WriteLine($"java.util.ArrayList<{DtT_protected}> {arraylist} = new java.util.ArrayList<>();");
        foreach (var ctor in dt.Ctors) {
          Contract.Assert(ctor.Formals.Count == 0);
          if (ctor.IsGhost) {
            w.WriteLine("{0}.add({1});", arraylist, ForcePlaceboValue(UserDefinedType.FromTopLevelDecl(dt.tok, dt), w, dt.tok));
          } else {
            w.WriteLine("{0}.add(new {1}{2}());", arraylist, DtT_protected, dt.IsRecordType ? "" : $"_{ctor.CompileName}");
          }
        }
        w.WriteLine($"return {arraylist};");
      }
      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors.Where(dtor => dtor.EnclosingCtors[0] == ctor)) {
          var compiledConstructorCount = dtor.EnclosingCtors.Count(constructor => !constructor.IsGhost);
          if (compiledConstructorCount != 0) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              var wDtor = wr.NewNamedBlock($"public {TypeName(arg.Type, wr, arg.tok)} dtor_{arg.CompileName}()");
              if (dt.IsRecordType) {
                wDtor.WriteLine($"return this.{FieldName(arg, 0)};");
              } else {
                wDtor.WriteLine("{0} d = this{1};", DtT_protected, dt is CoDatatypeDecl ? ".Get()" : "");
                var compiledConstructorsProcessed = 0;
                for (var i = 0; i < dtor.EnclosingCtors.Count; i++) {
                  var ctor_i = dtor.EnclosingCtors[i];
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                  if (ctor_i.IsGhost) {
                    continue;
                  }
                  if (compiledConstructorsProcessed < compiledConstructorCount - 1) {
                    wDtor.WriteLine("if (d instanceof {0}_{1}) {{ return (({0}_{1}{2})d).{3}; }}", dt.CompileName,
                      ctor_i.CompileName, DtT_TypeArgs, FieldName(arg, i));
                  } else {
                    wDtor.WriteLine($"return (({dt.CompileName}_{ctor_i.CompileName}{DtT_TypeArgs})d).{FieldName(arg, 0)};");
                  }
                  compiledConstructorsProcessed++;
                }
              }
            }
          }
        }
      }

      // FIXME: This is dodgy.  We can set the constructor body writer to null
      // only because we don't expect to use it, which is only because we don't
      // expect there to be fields.
      return new ClassWriter(this, btw, ctorBodyWriter: null);
    }

    void CompileDatatypeConstructors(DatatypeDecl dt, ConcreteSyntaxTree wrx) {
      Contract.Requires(dt != null);
      string typeParams = TypeParameters(dt.TypeArgs);
      if (dt.IsRecordType) {
        // There is only one constructor, and it is populated by CompileDatatypeBase
        return;
      }
      int constructorIndex = 0; // used to give each constructor a different name
      foreach (DatatypeCtor ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
        var filename = $"{ModulePath}/{DtCtorDeclarationName(ctor)}.java";
        var wr = wrx.NewFile(filename);
        FileCount += 1;
        wr.WriteLine($"// Class {DtCtorDeclarationName(ctor, dt.TypeArgs)}");
        wr.WriteLine($"// Dafny class {DtCtorDeclarationName(ctor, dt.TypeArgs)} compiled into Java");
        wr.WriteLine($"package {ModuleName};");
        wr.WriteLine();
        EmitImports(wr, out _);
        wr.WriteLine();
        EmitSuppression(wr);
        var w = wr.NewNamedBlock($"public class {DtCtorDeclarationName(ctor, dt.TypeArgs)} extends {IdName(dt)}{typeParams}");
        DatatypeFieldsAndConstructor(ctor, constructorIndex, w);
        constructorIndex++;
      }
      if (dt is CoDatatypeDecl) {
        var filename = $"{ModulePath}/{dt.CompileName}__Lazy.java";
        var wr = wrx.NewFile(filename);
        FileCount += 1;
        wr.WriteLine($"// Class {dt.CompileName}__Lazy");
        wr.WriteLine($"// Dafny class {dt.CompileName}__Lazy compiled into Java");
        wr.WriteLine($"package {ModuleName};");
        wr.WriteLine();
        EmitImports(wr, out _);
        wr.WriteLine();
        EmitSuppression(wr); //TODO: Fix implementations so they do not need this suppression
        var w = wr.NewNamedBlock($"public class {dt.CompileName}__Lazy{typeParams} extends {IdName(dt)}{typeParams}");
        w.WriteLine($"public interface Computer {{ {dt.CompileName} run(); }}");
        w.WriteLine("Computer c;");
        w.WriteLine($"{dt.CompileName}{typeParams} d;");
        w.WriteLine($"public {dt.CompileName}__Lazy(Computer c) {{ this.c = c; }}");
        w.WriteLine($"public {dt.CompileName}{typeParams} Get() {{ if (c != null) {{ d = c.run(); c = null; }} return d; }}");
        w.WriteLine("public String toString() { return Get().toString(); }");
      }
    }

    void DatatypeFieldsAndConstructor(DatatypeCtor ctor, int constructorIndex, ConcreteSyntaxTree wr) {
      Contract.Requires(ctor != null);
      Contract.Requires(0 <= constructorIndex && constructorIndex < ctor.EnclosingDatatype.Ctors.Count);
      Contract.Requires(wr != null);
      var dt = ctor.EnclosingDatatype;
      var i = 0;
      foreach (Formal arg in ctor.Formals) {
        if (!arg.IsGhost) {
          wr.WriteLine($"public {TypeName(arg.Type, wr, arg.tok)} {FieldName(arg, i)};");
          i++;
        }
      }
      wr.Write($"public {DtCtorDeclarationName(ctor)} (");
      WriteFormals("", ctor.Formals, wr);
      {
        var w = wr.NewBlock(")");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            w.WriteLine($"this.{FieldName(arg, i)} = {FormalName(arg, i)};");
            i++;
          }
        }
      }
      if (dt is CoDatatypeDecl) {
        string typeParams = TypeParameters(dt.TypeArgs);
        wr.WriteLine($"public {dt.CompileName}{typeParams} Get() {{ return this; }}");
      }
      // Equals method
      wr.WriteLine();
      wr.WriteLine("@Override");
      {
        var w = wr.NewBlock("public boolean equals(Object other)");
        w.WriteLine("if (this == other) return true;");
        w.WriteLine("if (other == null) return false;");
        w.WriteLine("if (getClass() != other.getClass()) return false;");
        string typeParams = TypeParameters(dt.TypeArgs);
        w.WriteLine("{0} o = ({0})other;", DtCtorDeclarationName(ctor, dt.TypeArgs));
        w.Write("return true");
        i = 0;
        foreach (var arg in ctor.Formals) {
          if (!arg.IsGhost) {
            var nm = FieldName(arg, i);
            w.Write(" && ");
            if (IsDirectlyComparable(DatatypeWrapperEraser.SimplifyType(Options, arg.Type))) {
              w.Write($"this.{nm} == o.{nm}");
            } else {
              w.Write($"java.util.Objects.equals(this.{nm}, o.{nm})");
            }
            i++;
          }
        }
        w.WriteLine(";");
      }
      // GetHashCode method (Uses the djb2 algorithm)
      wr.WriteLine("@Override");
      {
        var w = wr.NewBlock("public int hashCode()");
        w.WriteLine("long hash = 5381;");
        w.WriteLine($"hash = ((hash << 5) + hash) + {constructorIndex};");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FieldName(arg, i);
            w.Write("hash = ((hash << 5) + hash) + ");
            if (IsJavaPrimitiveType(arg.Type)) {
              w.WriteLine($"{BoxedTypeName(arg.Type, w, Token.NoToken)}.hashCode(this.{nm});");
            } else {
              w.WriteLine($"java.util.Objects.hashCode(this.{nm});");
            }
            i++;
          }
        }
        w.WriteLine("return (int)hash;");
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      {
        var w = wr.NewBlock("public String toString()");
        string nm;
        if (dt is TupleTypeDecl) {
          nm = "";
        } else {
          nm = (dt.EnclosingModuleDefinition.IsDefaultModule ? "" : dt.EnclosingModuleDefinition.Name + ".") + dt.Name + "." + ctor.Name;
        }
        if (dt is TupleTypeDecl && ctor.Formals.Count == 0) {
          // here we want parentheses and no name
          w.WriteLine("return \"()\";");
        } else if (dt is CoDatatypeDecl) {
          w.WriteLine($"return \"{nm}\";");
        } else {
          var tempVar = GenVarName("s", ctor.Formals);
          w.WriteLine($"StringBuilder {tempVar} = new StringBuilder();");
          w.WriteLine($"{tempVar}.append(\"{nm}\");");
          if (ctor.Formals.Count != 0) {
            w.WriteLine($"{tempVar}.append(\"(\");");
            i = 0;
            foreach (var arg in ctor.Formals) {
              if (!arg.IsGhost) {
                if (i != 0) {
                  w.WriteLine($"{tempVar}.append(\", \");");
                }
                w.Write($"{tempVar}.append(");
                var memberName = FieldName(arg, i);
                if (UnicodeCharEnabled && arg.Type.IsCharType) {
                  w.Write($"{DafnyHelpersClass}.ToCharLiteral(this.{memberName})");
                } else if (UnicodeCharEnabled && arg.Type.IsStringType) {
                  w.Write($"{DafnyHelpersClass}.ToStringLiteral(this.{memberName})");
                } else if (IsJavaPrimitiveType(arg.Type)) {
                  w.Write($"this.{memberName}");
                } else {
                  w.Write($"{DafnyHelpersClass}.toString(this.{memberName})");
                }
                w.WriteLine(");");
                i++;
              }
            }
            w.WriteLine($"{tempVar}.append(\")\");");
          }
          w.WriteLine($"return {tempVar}.toString();");
        }
      }
    }

    string DtCtorDeclarationName(DatatypeCtor ctor, List<TypeParameter>/*?*/ typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return DtCtorDeclarationName(ctor) + TypeParameters(typeParams);
    }
    string DtCtorDeclarationName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
      return dt.IsRecordType ? IdName(dt) : dt.CompileName + "_" + ctor.CompileName;
    }
    string DtCtorName(DatatypeCtor ctor, List<Type> typeArgs, ConcreteSyntaxTree wr) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeArgs != null && typeArgs.Count != 0) {
        s += "<" + BoxedTypeNames(typeArgs, wr, ctor.tok) + ">";
      }
      return s;
    }
    string DtCtorName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
      if (dt is TupleTypeDecl tupleDecl) {
        return DafnyTupleClass(tupleDecl.NonGhostDims);
      }
      var dtName = IdProtect(dt.FullCompileName);
      return dt.IsRecordType ? dtName : dtName + "_" + ctor.CompileName;
    }
    string DtCreateName(DatatypeCtor ctor) {
      Contract.Assert(!ctor.IsGhost); // there should never be an occasion to ask for a ghost constructor
      if (ctor.EnclosingDatatype.IsRecordType) {
        return "create";
      }
      return "create_" + ctor.CompileName;
    }

    private string FieldName(Formal formal, int i) {
      Contract.Requires(formal != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return IdProtect("_" + (formal.HasName ? formal.CompileName : "a" + i));
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      wr.Write("System.out.print(");
      EmitToString(wr, arg, wStmts);
      wr.WriteLine(");");
    }

    protected void EmitToString(ConcreteSyntaxTree wr, Expression arg, ConcreteSyntaxTree wStmts) {
      if (arg.Type.IsArrowType) {
        var expr = arg.Resolved;
        if (expr is IdentifierExpr id) {
          wr.Write(IdName(id.Var) + " == null ? null : \"Function\"");
        } else {
          wr.Write("\"Function\"");
        }
      } else if (AsNativeType(arg.Type) != null && AsNativeType(arg.Type).LowerBound >= 0) {
        var nativeName = GetNativeTypeName(AsNativeType(arg.Type));
        switch (AsNativeType(arg.Type).Sel) {
          case NativeType.Selection.Byte:
            wr.Write("java.lang.Integer.toUnsignedString(java.lang.Byte.toUnsignedInt(");
            wr.Append(Expr(arg, false, wStmts));
            wr.Write("))");
            break;
          case NativeType.Selection.UShort:
            wr.Write("java.lang.Integer.toUnsignedString(java.lang.Short.toUnsignedInt(");
            wr.Append(Expr(arg, false, wStmts));
            wr.Write("))");
            break;
          case NativeType.Selection.UInt:
            wr.Write("java.lang.Integer.toUnsignedString(");
            wr.Append(Expr(arg, false, wStmts));
            wr.Write(")");
            break;
          case NativeType.Selection.ULong:
            wr.Write("java.lang.Long.toUnsignedString(");
            wr.Append(Expr(arg, false, wStmts));
            wr.Write(")");
            break;
          default:
            // Should be an unsigned type by assumption
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      } else {
        bool isGeneric = arg.Type.AsSeqType != null &&
                         arg.Type.AsSeqType.Arg.IsTypeParameter;
        if (arg.Type.IsStringType) {
          TrParenExpr(arg, wr, false, wStmts);
          wr.Write(".verbatimString()");
        } else if (arg.Type.IsCharType && UnicodeCharEnabled) {
          wr.Write($"{DafnyHelpersClass}.ToCharLiteral(");
          wr.Append(Expr(arg, false, wStmts));
          wr.Write(")");
        } else if (isGeneric && !UnicodeCharEnabled) {
          wr.Write($"((java.util.function.Function<{DafnySeqClass}<?>,String>)(_s -> (_s.elementType().defaultValue().getClass() == java.lang.Character.class ? _s.verbatimString() : String.valueOf(_s)))).apply(");
          wr.Append(Expr(arg, false, wStmts));
          wr.Write(")");
        } else {
          wr.Write("java.lang.String.valueOf(");
          wr.Append(Expr(arg, false, wStmts));
          wr.Write(")");
        }
      }
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public override string PublicIdProtect(string name) {
      name = name.Replace("_module", "_System");
      if (name == "" || name.First() == '_') {
        return name; // no need to further protect this name
      }

      // TODO: Finish with all the public IDs that need to be protected
      switch (name) {
        // keywords Java 8 and before
        // https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html
        case "abstract":
        case "assert":
        case "break":
        case "byte":
        case "case":
        case "catch":
        case "char":
        case "class":
        case "continue":
        case "default":
        case "do":
        case "double":
        case "else":
        case "enum":
        case "extends":
        case "final":
        case "finally":
        case "float":
        case "for":
        case "if":
        case "implements":
        case "import":
        case "instanceof":
        case "int":
        case "interface":
        case "long":
        case "native":
        case "new":
        case "package":
        case "private":
        case "public":
        case "return":
        case "short":
        case "static":
        case "strictfp":
        case "super":
        case "switch":
        case "synchronized":
        case "this":
        case "throw":
        case "throws":
        case "transient":
        case "try":
        case "void":
        case "volatile":
        case "while":
        // keywords since Java 9
        case "exports":
        case "module":
        case "requires":
        // no longer used in Java but still reserved as keywords
        case "const":
        case "goto":
        // special identifiers since Java 10
        case "var":
        // literal values
        case "false":
        case "null":
        case "true":
        case "toString":
        case "equals":
        case "hashCode":
          return name + "_"; // TODO: figure out what to do here (C# uses @, Go uses _, JS uses _$$_)
        default:
          return name; // Package name is not a keyword, so it can be used
      }
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      if (outParams.Count == 0) {
        wr.WriteLine("return;");
      } else if (outParams.Count == 1) {
        wr.WriteLine($"return {IdName(outParams[0])};");
      } else {
        tuples.Add(outParams.Count);
        wr.WriteLine($"return new {DafnyTupleClass(outParams.Count)}<>({Util.Comma(outParams, IdName)});");
      }
    }

    // TODO: See if more types need to be added
    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || t.IsRefType || AsJavaNativeType(t) != null;
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      if (typeArgs.Count != 0) {
        wr.Write("<" + BoxedTypeNames(typeArgs, wr, tok) + ">");
      }
    }

    protected override void EmitNameAndActualTypeArgs(string protectedName, List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      EmitActualTypeArgs(typeArgs, tok, wr);
      wr.Write(protectedName);
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
      return TypeName(type, wr, tok) + " " + target;
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var ctor = (Constructor)initCall?.Method; // correctness of cast follows from precondition of "EmitNew"
      wr.Write($"new {TypeName(type, wr, tok)}(");
      var sep = "";
      if (type is UserDefinedType definedType) {
        var typeArguments = TypeArgumentInstantiation.ListFromClass(definedType.ResolvedClass, definedType.TypeArgs);
        EmitTypeDescriptorsActuals(typeArguments, tok, wr, ref sep);
      }
      wr.Write(ConstructorArguments(initCall, wStmts, ctor, sep));
      wr.Write(")");
    }

    /// <summary>
    /// Returns whether or not there is a run-time type descriptor corresponding to "tp".
    ///
    /// Note, one might think that this method should return "tp.Characteristics.HasCompiledValue".
    /// However, currently, all built-in collection types in Java use type descriptors for their arguments.
    /// To get this threaded through everywhere, all type arguments must always be passed with a
    /// corresponding type descriptor. :(  Thus, this method returns "true".
    /// </summary>
    protected override bool NeedsTypeDescriptor(TypeParameter tp) {
      return true;
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      if (cl is DatatypeDecl dt) {
        needsTypeParameter = isStatic || DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _);
        needsTypeDescriptor = true;
      } else if (cl is TraitDecl) {
        needsTypeParameter = isStatic || lookasideBody;
        needsTypeDescriptor = isStatic || lookasideBody;
      } else {
        Contract.Assert(cl is ClassDecl);
        needsTypeParameter = isStatic;
        needsTypeDescriptor = isStatic;
      }
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      type = DatatypeWrapperEraser.SimplifyType(Options, type, true);
      if (type is BoolType) {
        return $"{DafnyTypeDescriptor}.BOOLEAN";
      } else if (type is CharType) {
        return UnicodeCharEnabled ? $"{DafnyTypeDescriptor}.UNICODE_CHAR" : $"{DafnyTypeDescriptor}.CHAR";
      } else if (type is IntType) {
        return $"{DafnyTypeDescriptor}.BIG_INTEGER";
      } else if (type is BigOrdinalType) {
        return $"{DafnyTypeDescriptor}.BIG_INTEGER";
      } else if (type is RealType) {
        return $"{DafnyTypeDescriptor}.BIG_RATIONAL";
      } else if (type is BitvectorType) {
        var t = (BitvectorType)type;
        if (t.NativeType != null) {
          return GetNativeTypeDescriptor(AsNativeType(type));
        } else {
          return $"{DafnyTypeDescriptor}.BIG_INTEGER";
        }
      } else if (type.IsObjectQ || type.IsObject) {
        return $"{DafnyTypeDescriptor}.OBJECT";
      } else if (type.IsArrayType) {
        ArrayClassDecl at = type.AsArrayType;
        var elType = UserDefinedType.ArrayElementType(type);
        var elTypeName = TypeName(elType, wr, tok, true);
        if (at.Dims > 1) {
          arrays.Add(at.Dims);
          return $"{DafnyMultiArrayClass(at.Dims)}.<{elTypeName}>{TypeMethodName}()";
        } else if (elType.IsBoolType) {
          return $"{DafnyTypeDescriptor}.BOOLEAN_ARRAY";
        } else if (elType.IsCharType) {
          return $"{DafnyTypeDescriptor}.CHAR_ARRAY";
        } else if (AsNativeType(elType) != null) {
          switch (AsJavaNativeType(elType)) {
            case JavaNativeType.Byte: return $"{DafnyTypeDescriptor}.BYTE_ARRAY";
            case JavaNativeType.Short: return $"{DafnyTypeDescriptor}.SHORT_ARRAY";
            case JavaNativeType.Int: return $"{DafnyTypeDescriptor}.INT_ARRAY";
            case JavaNativeType.Long: return $"{DafnyTypeDescriptor}.LONG_ARRAY";
            default:
              Contract.Assert(false);
              throw new cce.UnreachableException();
          }
        } else {
          return $"(({DafnyTypeDescriptor}<{BoxedTypeName(type, wr, tok)}>)({TypeDescriptor(elType, wr, tok)}).arrayType())";
        }
      } else if (type.IsTypeParameter) {
        var tp = type.AsTypeParameter;
        Contract.Assert(tp != null);
        if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(tp, out var instantiatedTypeParameter)) {
          return TypeDescriptor(instantiatedTypeParameter, wr, tok);
        }
        return FormatTypeDescriptorVariable(type.AsTypeParameter.CompileName);
      } else if (type.IsBuiltinArrowType && type.AsArrowType.Arity == 1) {
        // Can't go the usual route because java.util.function.Function doesn't have a _typeDescriptor() method
        var arrowType = type.AsArrowType;
        return $"{DafnyTypeDescriptor}.function({TypeDescriptor(arrowType.Args[0], wr, tok)}, {TypeDescriptor(arrowType.Result, wr, tok)})";
      } else if (type is UserDefinedType udt) {
        var s = FullTypeName(udt, null, true);
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return $"{DafnyTypeDescriptor}.LONG";
        }

        if (cl.IsExtern(Options, out _, out _)) {
          var td = $"{DafnyTypeDescriptor}.<{BoxedTypeName(type, wr, tok)}> findType({s}.class";
          if (udt.TypeArgs != null && udt.TypeArgs.Count > 0) {
            td += $", {Util.Comma(udt.TypeArgs, arg => TypeDescriptor(arg, wr, tok))}";
          }
          return td + ")";
        }

        List<Type> relevantTypeArgs;
        if (type.IsBuiltinArrowType) {
          relevantTypeArgs = type.TypeArgs;
        } else if (cl is DatatypeDecl dt) {
          relevantTypeArgs = udt.TypeArgs;
        } else {
          relevantTypeArgs = new List<Type>();
          for (int i = 0; i < cl.TypeArgs.Count; i++) {
            if (NeedsTypeDescriptor(cl.TypeArgs[i])) {
              relevantTypeArgs.Add(udt.TypeArgs[i]);
            }
          }
        }

        return AddTypeDescriptorArgs(s, udt.TypeArgs, relevantTypeArgs, wr, udt.tok);
      } else if (type is SetType setType) {
        return AddTypeDescriptorArgs(DafnySetClass, setType.TypeArgs, setType.TypeArgs, wr, tok);
      } else if (type is SeqType seqType) {
        return AddTypeDescriptorArgs(DafnySeqClass, seqType.TypeArgs, seqType.TypeArgs, wr, tok);
      } else if (type is MultiSetType multiSetType) {
        return AddTypeDescriptorArgs(DafnyMultiSetClass, multiSetType.TypeArgs, multiSetType.TypeArgs, wr, tok);
      } else if (type is MapType mapType) {
        return AddTypeDescriptorArgs(DafnyMapClass, mapType.TypeArgs, mapType.TypeArgs, wr, tok);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private string GetNativeTypeDescriptor(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return $"{DafnyTypeDescriptor}.BYTE";
        case JavaNativeType.Short: return $"{DafnyTypeDescriptor}.SHORT";
        case JavaNativeType.Int: return $"{DafnyTypeDescriptor}.INT";
        case JavaNativeType.Long: return $"{DafnyTypeDescriptor}.LONG";
        default: Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private string AddTypeDescriptorArgs(string fullCompileName, List<Type> typeArgs, List<Type> relevantTypeArgs, ConcreteSyntaxTree wr, IToken tok) {
      Contract.Requires(fullCompileName != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(relevantTypeArgs != null);
      Contract.Requires(wr != null);
      Contract.Requires(tok != null);

      string s = $"{IdProtect(fullCompileName)}.";
      if (typeArgs != null && typeArgs.Count != 0) {
        s += $"<{BoxedTypeNames(typeArgs, wr, tok)}>";
      }
      s += $"{TypeMethodName}(";
      s += Util.Comma(relevantTypeArgs, arg => TypeDescriptor(arg, wr, tok));
      return s + ")";
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      wr.WriteLine($"java.util.ArrayList<{BoxedTypeName(e.Type.AsSetType.Arg, wr, e.tok)}> {collectionName} = new java.util.ArrayList<>();");
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      var mt = e.Type.AsMapType;
      var domType = mt.Domain;
      var ranType = mt.Range;
      wr.WriteLine($"java.util.HashMap<{BoxedTypeName(domType, wr, e.tok)}, {BoxedTypeName(ranType, wr, e.tok)}> {collectionName} = new java.util.HashMap<>();");
    }

    protected override void OrganizeModules(Program program, out List<ModuleDefinition> modules) {
      modules = new List<ModuleDefinition>();
      foreach (var m in program.CompileModules) {
        if (!m.IsDefaultModule && !m.Name.Equals("_System")) {
          modules.Add(m);
        }
      }
      foreach (var m in program.CompileModules) {
        if (m.Name.Equals("_System")) {
          modules.Add(m);
        }
      }
      foreach (var m in program.CompileModules) {
        if (m.IsDefaultModule) {
          modules.Add(m);
        }
      }
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      var typeArgs = SelectNonGhost(dt, dtv.InferredTypeArgs);
      EmitDatatypeValue(dt, dtv.Ctor, typeArgs, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, List<Type> typeArgs, bool isCoCall, string arguments, ConcreteSyntaxTree wr) {
      var dtName = dt is TupleTypeDecl tupleDecl ? DafnyTupleClass(tupleDecl.NonGhostDims) : dt.FullCompileName;
      var typeParams = typeArgs.Count == 0 ? "" : $"<{BoxedTypeNames(typeArgs, wr, dt.tok)}>";
      if (!isCoCall) {
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   Dt.<T>create_Cons( args )
        wr.Write($"{dtName}.{typeParams}{DtCreateName(ctor)}({arguments})");
      } else {
        wr.Write($"new {dt.CompileName}__Lazy(");
        wr.Write("() -> { return ");
        wr.Write($"new {DtCtorName(ctor)}{typeParams}({arguments})");
        wr.Write("; })");
      }
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      // TODO: there may be an opportunity to share code with CreateIIFE,
      // which may be worth it given all the necessary coercions.

      if (inTypes.Count != 1) {
        functions.Add(inTypes.Count);
      }
      wr.Write('(');
      if (!untyped) {
        wr.Write("({0}<{1}{2}>)", DafnyFunctionIface(inTypes.Count), Util.Comma("", inTypes, t => BoxedTypeName(t, wr, tok) + ", "), BoxedTypeName(resultType, wr, tok));
      }
      var boxedInNames = inNames.Select(inName => ProtectedFreshId(inName + "_boxed")).ToList();
      wr.Write($"({boxedInNames.Comma(nm => nm)}) ->");
      var w = wr.NewExprBlock("");
      wr.Write(")");

      for (var i = 0; i < inNames.Count; i++) {
        w.Write($"{TypeName(inTypes[i], w, tok)} {inNames[i]} = ");
        var coercedW = EmitCoercionIfNecessary(NativeObjectType, inTypes[i], tok, w);
        coercedW.Write(boxedInNames[i]);
        w.WriteLine(";");
      }

      return w;
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      functions.Add(0);
      wr.Write($"(({DafnyFunctionIface(0)}<{BoxedTypeName(resultType, wr, resultTok)}>)(() ->");
      var w = wr.NewBigExprBlock("", ")).apply()");
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody, wStmts);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          if (AsNativeType(expr.Type) != null) {
            TrParenExpr(CastIfSmallNativeType(expr.Type) + "~", expr, wr, inLetExprBody, wStmts);
          } else {
            TrParenExpr("", expr, wr, inLetExprBody, wStmts);
            wr.Write(".not()");
          }
          break;
        case ResolvedUnaryOp.Cardinality:
          if (expr.Type.AsCollectionType is MultiSetType) {
            TrParenExpr("", expr, wr, inLetExprBody, wStmts);
            wr.Write(".cardinality()");
          } else if (expr.Type.AsCollectionType is SetType || expr.Type.AsCollectionType is MapType) {
            TrParenExpr("java.math.BigInteger.valueOf(", expr, wr, inLetExprBody, wStmts);
            wr.Write(".size())");
          } else if (expr.Type.IsArrayType) {
            TrParenExpr("java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength", expr, wr, inLetExprBody, wStmts);
            wr.Write(")");
          } else {
            TrParenExpr("java.math.BigInteger.valueOf(", expr, wr, inLetExprBody, wStmts);
            wr.Write(".length())");
          }
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    // Find the class with static methods like "divideUnsigned" for the type
    private string HelperClass(NativeType nt) {
      return AsJavaNativeType(nt) == JavaNativeType.Long ? "java.lang.Long" : "java.lang.Integer";
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op, Expression e0, Expression e1, IToken tok,
      Type resultType, out string opString,
      out string preOpString, out string postOpString, out string callString, out string staticCallString,
      out bool reverseArguments, out bool truncateResult, out bool convertE1_to_int, out bool coerceE1, ConcreteSyntaxTree errorWr) {
      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;
      coerceE1 = false;

      void doPossiblyNativeBinOp(string o, string name, out string preOpS, out string opS,
        out string postOpS, out string callS) {
        if (AsNativeType(resultType) != null) {
          var nativeName = GetNativeTypeName(AsNativeType(resultType));
          preOpS = $"({nativeName}) {CastIfSmallNativeType(resultType)} (";
          opS = o;
          postOpS = ")";
          callS = null;
        } else {
          callS = name;
          preOpS = "";
          opS = null;
          postOpS = "";
        }
      }

      switch (op) {
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          doPossiblyNativeBinOp("&", "and", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          doPossiblyNativeBinOp("|", "or", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          doPossiblyNativeBinOp("^", "xor", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.EqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(Options, e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "==";
            } else if (eqType.IsRefType) {
              opString = "== (Object) ";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "==";
            } else {
              staticCallString = "java.util.Objects.equals";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
            var eqType = DatatypeWrapperEraser.SimplifyType(Options, e0.Type);
            if (IsHandleComparison(tok, e0, e1, errorWr)) {
              opString = "!=";
            } else if (eqType.IsRefType) {
              opString = "!= (Object) ";
            } else if (IsDirectlyComparable(eqType)) {
              opString = "!=";
            } else {
              preOpString = "!";
              staticCallString = "java.util.Objects.equals";
            }
            break;
          }
        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Gt:
          var call = false;
          var argNative = AsNativeType(e0.Type);
          if (argNative != null && argNative.LowerBound >= 0) {
            staticCallString = HelperClass(argNative) + ".compareUnsigned";
            call = true;
          } else if (argNative == null) {
            callString = "compareTo";
            call = true;
          }
          if (call) {
            switch (op) {
              case BinaryExpr.ResolvedOpcode.Lt:
                postOpString = " < 0";
                break;
              case BinaryExpr.ResolvedOpcode.Le:
                postOpString = " <= 0";
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
                postOpString = " >= 0";
                break;
              case BinaryExpr.ResolvedOpcode.Gt:
                postOpString = " > 0";
                break;
              default:
                Contract.Assert(false);
                throw new cce.UnreachableException();
            }
          } else {
            switch (op) {
              case BinaryExpr.ResolvedOpcode.Lt:
                opString = "<";
                break;
              case BinaryExpr.ResolvedOpcode.Le:
                opString = "<=";
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
                opString = ">=";
                break;
              case BinaryExpr.ResolvedOpcode.Gt:
                opString = ">";
                break;
              default:
                Contract.Assert(false);
                throw new cce.UnreachableException();
            }
          }
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          doPossiblyNativeBinOp("<<", "shiftLeft", out preOpString, out opString, out postOpString, out callString);
          truncateResult = true;
          convertE1_to_int = AsNativeType(e1.Type) == null;
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          doPossiblyNativeBinOp(">>>", "shiftRight", out preOpString, out opString, out postOpString, out callString);
          convertE1_to_int = AsNativeType(e1.Type) == null;
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = $"({CharTypeName(false)}) (";
            postOpString = ")";
            opString = "+";
          } else {
            doPossiblyNativeBinOp("+", "add", out preOpString, out opString, out postOpString, out callString);
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = $"({CharTypeName(false)}) (";
            opString = "-";
            postOpString = ")";
          } else {
            doPossiblyNativeBinOp("-", "subtract", out preOpString, out opString, out postOpString, out callString);
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          doPossiblyNativeBinOp("*", "multiply", out preOpString, out opString, out postOpString, out callString);
          truncateResult = true;
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (NeedsEuclideanDivision(resultType)) {
            staticCallString = $"{DafnyEuclideanClass}.EuclideanDivision";
          } else if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.Sel == NativeType.Selection.Byte) {
              staticCallString = $"{DafnyHelpersClass}.divideUnsignedByte";
            } else if (nt.Sel == NativeType.Selection.UShort) {
              staticCallString = $"{DafnyHelpersClass}.divideUnsignedShort";
            } else {
              preOpString = CastIfSmallNativeType(resultType);
              staticCallString = HelperClass(AsNativeType(resultType)) + ".divideUnsigned";
            }
          } else {
            callString = "divide";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (NeedsEuclideanDivision(resultType)) {
            staticCallString = $"{DafnyEuclideanClass}.EuclideanModulus";
          } else if (AsNativeType(resultType) != null) {
            var nt = AsNativeType(resultType);
            if (nt.Sel == NativeType.Selection.Byte) {
              staticCallString = $"{DafnyHelpersClass}.remainderUnsignedByte";
            } else if (nt.Sel == NativeType.Selection.UShort) {
              staticCallString = $"{DafnyHelpersClass}.remainderUnsignedShort";
            } else {
              preOpString = CastIfSmallNativeType(resultType);
              staticCallString = HelperClass(AsNativeType(resultType)) + ".remainderUnsigned";
            }
          } else {
            callString = "mod";
          }
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          callString = "equals";
          break;
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "isProperSubsetOf";
          break;
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "isSubsetOf";
          break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          callString = $"<{BoxedTypeName(e1.Type.AsCollectionType.Arg, errorWr, tok)}>disjoint";
          break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = $"<{BoxedTypeName(e0.Type, errorWr, tok)}>contains";
          reverseArguments = true;
          coerceE1 = true;
          break;

        case BinaryExpr.ResolvedOpcode.Union:
          staticCallString = $"{DafnySetClass}.<{BoxedTypeName(resultType.AsSetType.Arg, errorWr, tok)}>union";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          staticCallString = $"{DafnyMultiSetClass}.<{BoxedTypeName(resultType.AsMultiSetType.Arg, errorWr, tok)}>union";
          break;
        case BinaryExpr.ResolvedOpcode.MapMerge:
          staticCallString = $"{DafnyMapClass}.<{BoxedTypeName(resultType.AsMapType.Domain, errorWr, tok)}, {BoxedTypeName(resultType.AsMapType.Range, errorWr, tok)}>merge";
          break;
        case BinaryExpr.ResolvedOpcode.Intersection:
          staticCallString = $"{DafnySetClass}.<{BoxedTypeName(resultType.AsSetType.Arg, errorWr, tok)}>intersection";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          staticCallString = $"{DafnyMultiSetClass}.<{BoxedTypeName(resultType.AsMultiSetType.Arg, errorWr, tok)}>intersection";
          break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
          staticCallString = $"{DafnySetClass}.<{BoxedTypeName(resultType.AsSetType.Arg, errorWr, tok)}>difference";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          staticCallString = $"{DafnyMultiSetClass}.<{BoxedTypeName(resultType.AsMultiSetType.Arg, errorWr, tok)}>difference";
          break;
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          staticCallString = $"{DafnyMapClass}.<{BoxedTypeName(resultType.AsMapType.Domain, errorWr, tok)}, {BoxedTypeName(resultType.AsMapType.Range, errorWr, tok)}>subtract";
          break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          callString = "isProperPrefixOf";
          break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "isPrefixOf";
          break;
        case BinaryExpr.ResolvedOpcode.Concat:
          staticCallString = $"{DafnySeqClass}.<{BoxedTypeName(resultType.AsSeqType.Arg, errorWr, tok)}>concatenate";
          break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "contains";
          reverseArguments = true;
          coerceE1 = true;
          break;
        default:
          base.CompileBinOp(op, e0, e1, tok, resultType,
            out opString, out preOpString, out postOpString, out callString, out staticCallString, out reverseArguments, out truncateResult, out convertE1_to_int, out coerceE1,
            errorWr);
          break;
      }
    }

    protected override void EmitFooter(Program program, ConcreteSyntaxTree wr) {
      // Emit tuples
      foreach (int i in tuples) {
        if (i == 2 || i == 3) {
          continue; // Tuple2 and Tuple3 already exist in DafnyRuntime.jar, so don't remake these files.
        }
        CreateTuple(i, wr);
      }

      // Emit function interfaces
      foreach (var i in functions) {
        CreateLambdaFunctionInterface(i, wr);
      }

      // Emit arrays
      foreach (var i in arrays) {
        CreateDafnyArrays(i, wr);
      }
    }

    private void CreateTuple(int i, ConcreteSyntaxTree outputWr) {
      Contract.Requires(0 <= i);
      Contract.Requires(outputWr != null);

      var wrTop = outputWr.NewFile(Path.Combine("dafny", $"Tuple{i}.java"));

      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();
      EmitSuppression(wrTop);
      wrTop.Write($"public class Tuple{i}");
      if (i != 0) {
        wrTop.Write("<{0}>", Util.Comma(i, j => $"T{j}"));
      }

      var wr = wrTop.NewBlock("");
      for (var j = 0; j < i; j++) {
        wr.WriteLine("private T{0} _{0};", j);
      }
      wr.WriteLine();

      wr.Write("public Tuple{0}({1}", i, Util.Comma(i, j => $"T{j} _{j}"));
      var wrCtor = wr.NewBlock(")");
      for (var j = 0; j < i; j++) {
        wrCtor.WriteLine("this._{0} = _{0};", j);
      }

      wr.WriteLine();
      var typeParams = new List<TypeParameter>();
      for (var j = 0; j < i; j++) {
        typeParams.Add(new TypeParameter(RangeToken.NoToken, new Name($"T{j}"), TypeParameter.TPVarianceSyntax.Covariant_Permissive));
      }
      var typeParamString = TypeParameters(typeParams);
      var initializer = string.Format("Default({0})", Util.Comma(i, j => $"_td_T{j}.defaultValue()"));
      EmitTypeMethod(null, $"Tuple{i}", typeParams, typeParams, $"Tuple{i}{typeParamString}", initializer, wr);

      // public static Tuple4<T0, T1, T2, T3> Default(dafny.TypeDescriptor<T0> _td_T0, dafny.TypeDescriptor<T1> _td_T1, dafny.TypeDescriptor<T2> _td_T2, dafny.TypeDescriptor<T3> _td_T3) {
      //   return new Tuple4<>(_td_T0.defaultValue(), _td_T1.defaultValue(), _td_T2.defaultValue(), _td_T3.defaultValue());
      // }
      wr.WriteLine();
      if (i == 0) {
        wr.Write("public static Tuple0");
      } else {
        wr.Write("public static <{1}> Tuple{0}<{1}>", i, Util.Comma(i, j => $"T{j}"));
      }
      wr.Write(" Default({0})", Util.Comma(i, j => $"T{j} {FormatDefaultTypeParameterValueName($"T{j}")}"));
      {
        var w = wr.NewBlock("");
        w.WriteLine("return create({0});", Util.Comma(i, j => $"{FormatDefaultTypeParameterValueName($"T{j}")}"));
      }

      // create method
      wr.WriteLine();
      if (i == 0) {
        wr.Write("public static Tuple0");
      } else {
        wr.Write("public static <{1}> Tuple{0}<{1}>", i, Util.Comma(i, j => $"T{j}"));
      }
      wr.Write(" create({0})", Util.Comma(i, j => $"T{j} _{j}"));
      {
        var w = wr.NewBlock("");
        w.WriteLine("return new Tuple{0}({1});", i, Util.Comma(i, j => $"_{j}"));
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      var wrEquals = wr.NewBlock("public boolean equals(Object obj)");
      wrEquals.WriteLine("if (this == obj) return true;");
      wrEquals.WriteLine("if (obj == null) return false;");
      wrEquals.WriteLine("if (getClass() != obj.getClass()) return false;");
      wrEquals.WriteLine($"Tuple{i} o = (Tuple{i}) obj;");
      if (i != 0) {
        wrEquals.WriteLine("return {0};", Util.Comma(" && ", i, j => $"java.util.Objects.equals(this._{j}, o._{j})"));
      } else {
        wrEquals.WriteLine("return true;");
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      var wrToString = wr.NewBlock("public String toString()");
      wrToString.WriteLine("StringBuilder sb = new StringBuilder();");
      wrToString.WriteLine("sb.append(\"(\");");
      for (int j = 0; j < i; j++) {
        wrToString.WriteLine($"sb.append(_{j} == null ? \"null\" : _{j}.toString());");
        if (j != i - 1) {
          wrToString.WriteLine("sb.append(\", \");");
        }
      }

      wrToString.WriteLine("sb.append(\")\");");
      wrToString.WriteLine("return sb.toString();");

      wr.WriteLine();
      wr.WriteLine("@Override");
      var wrHashCode = wr.NewBlock("public int hashCode()");
      wrHashCode.WriteLine("// GetHashCode method (Uses the djb2 algorithm)");
      wrHashCode.WriteLine(
        "// https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm");
      wrHashCode.WriteLine("long hash = 5381;");
      wrHashCode.WriteLine(
        "hash = ((hash << 5) + hash) + 0;"); // this is constructor 0 (in fact, it's the only constructor)
      for (int j = 0; j < i; j++) {
        wrHashCode.WriteLine("hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._" + j + ");");
      }

      wrHashCode.WriteLine("return (int)hash;");

      for (int j = 0; j < i; j++) {
        wr.WriteLine();
        wr.WriteLine("public T" + j + " dtor__" + j + "() { return this._" + j + "; }");
      }
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok, bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return UnicodeCharEnabled ? $"((int){CharType.DefaultValueAsString})" : CharType.DefaultValueAsString;
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "java.math.BigInteger.ZERO";
      } else if (xType is RealType) {
        return $"{DafnyBigRationalClass}.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? $"{CastIfSmallNativeType(t)}0" : "java.math.BigInteger.ZERO";
      } else if (xType is CollectionType collType) {
        string collName = CollectionTypeUnparameterizedName(collType);
        string argNames = BoxedTypeName(collType.Arg, wr, tok);
        if (xType is MapType mapType) {
          argNames += "," + BoxedTypeName(mapType.Range, wr, tok);
        }
        string td = "";
        if (xType is SeqType) {
          td = TypeDescriptor(collType.Arg, wr, tok);
        }
        return $"{collName}.<{argNames}> empty({td})";
      }

      var udt = (UserDefinedType)xType;
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is TypeParameter tp) {
        if (usePlaceboValue && !tp.Characteristics.HasCompiledValue) {
          return "null";
        } else if (constructTypeParameterDefaultsFromTypeDescriptors) {
          return $"{FormatTypeDescriptorVariable(tp.CompileName)}.defaultValue()";
        } else {
          return FormatDefaultTypeParameterValue(tp);
        }
      } else if (cl is OpaqueTypeDecl opaque) {
        return FormatDefaultTypeParameterValueName(opaque.CompileName);
      } else if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return FullTypeName(udt) + ".Witness";
        } else if (td.NativeType != null) {
          return GetNativeDefault(td.NativeType);
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          return FullTypeName(udt) + ".defaultValue()";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return $"(({BoxedTypeName(xType, wr, udt.tok)}) null)";
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) -> rangeDefaultValue)
            return $"(({Util.Comma(udt.TypeArgs.Count - 1, i => $"{BoxedTypeName(udt.TypeArgs[i], wr, udt.tok)} x{i}")}) -> {rangeDefaultValue})";
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl arrayClass) {
            // non-null array type; we know how to initialize them
            var elType = udt.TypeArgs[0];
            TypeName_SplitArrayName(elType, out var innermostElementType, out var brackets);
            string bareArray;
            brackets += Util.Repeat(arrayClass.Dims - 1, "[]");
            if (innermostElementType.IsTypeParameter) {
              var cast = $"(java.lang.Object{brackets})";
              bareArray = $"{cast}{FormatTypeDescriptorVariable(innermostElementType.AsTypeParameter)}.newArray({Util.Comma(arrayClass.Dims, _ => "0")})";
            } else {
              var typeNameSansBrackets = TypeName(innermostElementType, wr, udt.tok, false, true);
              bareArray = $"new {typeNameSansBrackets}[0]{brackets}";
            }
            if (arrayClass.Dims == 1) {
              return bareArray;
            } else {
              var zeros = Util.Repeat(arrayClass.Dims, "0, ");
              return $"new {DafnyMultiArrayClass(arrayClass.Dims)}<>({TypeDescriptor(elType, wr, tok)}, {zeros}{bareArray})";
            }
          } else {
            return "null";
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
        }
      } else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        } else {
          return $"({BoxedTypeName(xType, wr, udt.tok)}) null";
        }
      } else if (cl is DatatypeDecl dt) {
        var s = FullTypeName(udt);
        var typeargs = "";
        var nonGhostTypeArgs = SelectNonGhost(cl, udt.TypeArgs);
        if (nonGhostTypeArgs.Count != 0) {
          typeargs = $"<{BoxedTypeNames(nonGhostTypeArgs, wr, udt.tok)}>";
        }
        // In an auto-init context (like a field initializer), we may not have
        // access to all the type descriptors, so we can't construct the
        // default value, but then null is an acceptable default, since
        // Dafny proves the value won't be accessed.
        if (usePlaceboValue) {
          return $"({s}{typeargs})null";
        }
        var relevantTypeArgs = UsedTypeParameters(dt, udt.TypeArgs);
        return $"{s}.{typeargs}Default({Util.Comma(relevantTypeArgs, ta => DefaultValueCoercedIfNecessary(ta.Actual, wr, tok, constructTypeParameterDefaultsFromTypeDescriptors))})";
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected type
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      wr.Write("{0} {1} = ", type != null ? TypeName(type, wr, tok, false, false, null) : "var", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts, ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters /*?*/,
      TopLevelDecl trait, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      var filename = $"{ModulePath}/{IdProtect(name)}.java";
      var w = wr.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Interface {name}");
      w.WriteLine($"// Dafny trait {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      EmitImports(w, out _);
      w.WriteLine();
      EmitSuppression(w); //TODO: Fix implementations so they do not need this suppression
      var typeParamString = TypeParameters(typeParameters);
      w.Write($"public interface {IdProtect(name)}{typeParamString}");
      if (superClasses != null) {
        string sep = " extends ";
        foreach (var tr in superClasses) {
          if (!tr.IsObject) {
            w.Write($"{sep}{TypeName(tr, w, tok)}");
            sep = ", ";
          }
        }
      }
      var instanceMemberWriter = w.NewBlock("");
      //writing the _Companion class
      filename = $"{ModulePath}/_Companion_{name}.java";
      w = w.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Interface {name}");
      w.WriteLine($"// Dafny trait {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      EmitImports(w, out _);
      w.WriteLine();
      EmitSuppression(w); //TODO: Fix implementations so they do not need this suppression
      w.Write($"public class _Companion_{name}{typeParamString}");
      var staticMemberWriter = w.NewBlock("");
      var ctorBodyWriter = staticMemberWriter.NewBlock($"public _Companion_{name}()");

      EmitTypeMethod(null, name, typeParameters, typeParameters, name + typeParamString, initializer: null, staticMemberWriter);
      return new ClassWriter(this, instanceMemberWriter, ctorBodyWriter, staticMemberWriter);
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, ctor.EnclosingDatatype, out var coreDtor)) {
        Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
        Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
        wr.Write(source);
        return;
      }
      string dtorName;
      if (ctor.EnclosingDatatype is TupleTypeDecl tupleTypeDecl) {
        Contract.Assert(tupleTypeDecl.NonGhostDims != 1); // such a tuple is an erasable-wrapper type, handled above
        dtorName = $"dtor__{dtor.NameForCompilation}()";
        wr = EmitCoercionIfNecessary(NativeObjectType, bvType, dtor.tok, wr);
      } else {
        dtorName = FieldName(dtor, formalNonGhostIndex);
      }
      wr.Write("(({0}){1}{2}).{3}", DtCtorName(ctor, typeArgs, wr), source, ctor.EnclosingDatatype is CoDatatypeDecl ? ".Get()" : "", dtorName);
    }

    private void CreateLambdaFunctionInterface(int i, ConcreteSyntaxTree outputWr) {
      Contract.Requires(0 <= i);
      Contract.Requires(outputWr != null);

      var functionName = $"Function{i}";
      var wr = outputWr.NewFile(Path.Combine("dafny", $"{functionName}.java"));

      var typeArgs = "<" + Util.Comma(i + 1, j => $"T{j}") + ">";

      wr.WriteLine("package dafny;");
      wr.WriteLine();
      wr.WriteLine("@FunctionalInterface");
      wr.Write($"public interface {functionName}{typeArgs}");
      var wrMembers = wr.NewBlock("");
      wrMembers.Write($"public T{i} apply(");
      wrMembers.Write(Util.Comma(i, j => $"T{j} t{j}"));
      wrMembers.WriteLine(");");

      EmitSuppression(wrMembers);
      wrMembers.Write($"public static {typeArgs} {DafnyTypeDescriptor}<{functionName}{typeArgs}> {TypeMethodName}(");
      wrMembers.Write(Util.Comma(i + 1, j => $"{DafnyTypeDescriptor}<T{j}> t{j}"));
      var wrTypeBody = wrMembers.NewBlock(")", "");
      // XXX This seems to allow non-nullable types to have null values (since
      // arrow types are allowed as "(0)"-constrained type arguments), but it's
      // consistent with other backends.
      wrTypeBody.Write($"return ({DafnyTypeDescriptor}<{functionName}{typeArgs}>) ({DafnyTypeDescriptor}<?>) {DafnyTypeDescriptor}.reference({functionName}.class);");
    }

    private void CreateDafnyArrays(int i, ConcreteSyntaxTree outputWr) {
      Contract.Requires(0 <= i);
      Contract.Requires(outputWr != null);

      var wrTop = outputWr.NewFile(Path.Combine("dafny", $"Array{i}.java"));

      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();

      // All brackets on the underlying "real" array type, minus the innermost
      // pair.  The innermost array must be represented as an Object since it
      // could be of primitive type.
      var outerBrackets = Repeat("[]", i - 1);

      var dims = Enumerable.Range(0, i);
      var outerDims = Enumerable.Range(0, i - 1);

      var wr = wrTop.NewBlock($"public final class Array{i}<T>");

      wr.WriteLine($"public final Object{outerBrackets} elmts;");
      wr.WriteLine($"private final {DafnyTypeDescriptor}<T> elmtType;");

      foreach (var j in dims) {
        wr.WriteLine($"public final int dim{j};");
      }
      {
        var wrBody = wr.NewBlock($"public Array{i}({DafnyTypeDescriptor}<T> elmtType, {Util.Comma(dims, j => $"int dim{j}")}, Object{outerBrackets} elmts)");
        wrBody.WriteLine("assert elmts.getClass().isArray();");
        wrBody.WriteLine("this.elmtType = elmtType;");
        foreach (var j in dims) {
          wrBody.WriteLine($"this.dim{j} = dim{j};");
        }
        wrBody.WriteLine("this.elmts = elmts;");
      }

      {
        var wrBody = wr.NewBlock($"public T get({Util.Comma(dims, j => $"int i{j}")})");
        wrBody.Write("return elmtType.getArrayElement(elmts");
        foreach (var j in outerDims) {
          wrBody.Write($"[i{j}]");
        }
        wrBody.WriteLine($", i{i - 1});");
      }

      {
        var wrBody = wr.NewBlock($"public void set({Util.Comma(dims, j => $"int i{j}")}, T value)");
        wrBody.Write("elmtType.setArrayElement(elmts");
        foreach (var j in outerDims) {
          wrBody.Write($"[i{j}]");
        }
        wrBody.WriteLine($", i{i - 1}, value);");
      }

      {
        var body = wr.NewBlock("public void fill(T z)");
        var forBodyWr = body;
        for (int j = 0; j < i - 1; j++) {
          forBodyWr = forBodyWr.NewBlock($"for(int i{j} = 0; i{j} < dim{j}; i{j}++)");
        }
        forBodyWr.Write($"elmtType.fillArray(elmts");
        for (int j = 0; j < i - 1; j++) {
          forBodyWr.Write($"[i{j}]");
        }
        forBodyWr.WriteLine(", z);");
      }

      {
        var body = wr.NewBlock($"public Array{i} fillThenReturn(T z)");
        body.WriteLine("fill(z);");
        body.WriteLine("return this;");
      }

      EmitSuppression(wr);
      wr.WriteLine($"private static final {DafnyTypeDescriptor}<Array{i}<?>> TYPE = ({DafnyTypeDescriptor}<Array{i}<?>>) ({DafnyTypeDescriptor}<?>) {DafnyTypeDescriptor}.reference(Array{i}.class);");
      EmitSuppression(wr);
      var wrTypeMethod = wr.NewBlock($"public static <T> {DafnyTypeDescriptor}<Array{i}<T>> {TypeMethodName}()");
      wrTypeMethod.WriteLine($"return ({DafnyTypeDescriptor}<Array{i}<T>>) ({DafnyTypeDescriptor}<?>) TYPE;");
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      if (!member.IsStatic && !NeedsCustomReceiver(member)) {
        var receiverType = UserDefinedType.FromTopLevelDecl(member.tok, member.EnclosingClass);
        var receiverTypeName = TypeName(receiverType, wr, member.tok);
        if (member.EnclosingClass.IsExtern(Options, out _, out _)) {
          receiverTypeName = FormatExternBaseClassName(receiverTypeName);
        }
        wr.WriteLine("{0} _this = this;", receiverTypeName);
      }
      return wr.NewBlock("TAIL_CALL_START: while (true)");
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      wr.WriteLine("continue TAIL_CALL_START;");
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(
      string tmpVarName, Type collectionElementType, IToken tok, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {

      // We may have to coerce from the boxed type used in collections
      var needsCoercion = IsCoercionNecessary(NativeObjectType, collectionElementType);
      var boxedType = BoxedTypeName(collectionElementType, wr, tok);
      var loopVarName = needsCoercion ? ProtectedFreshId(tmpVarName + "_boxed") : tmpVarName;
      wr.Write($"for ({boxedType} {loopVarName} : ");
      collectionWriter = wr.Fork();
      var wwr = wr.NewBlock(")");
      if (needsCoercion) {
        wwr.Write($"{TypeName(collectionElementType, wr, tok)} {tmpVarName} = ");
        var coercedWwr = EmitCoercionIfNecessary(NativeObjectType, collectionElementType, tok, wwr);
        coercedWwr.Write(loopVarName);
        wwr.WriteLine(";");
      }
      return wwr;
    }

    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      string typeTest;

      if (boundVarType.IsRefType) {
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          typeTest = "true";
        } else {
          typeTest = $"{tmpVarName} instanceof {TypeName(boundVarType, wPreconditions, tok)}";
        }
        if (boundVarType.IsNonNullRefType) {
          typeTest = $"{tmpVarName} != null && {typeTest}";
        } else {
          typeTest = $"{tmpVarName} == null || {typeTest}";
        }
      } else {
        typeTest = "true";
      }
      return typeTest;
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {

      var typeName = TypeName(boundVarType, wr, tok);
      wr.WriteLine("{0}{1} = ({2}){3};", introduceBoundVar ? typeName + " " : "", boundVarName, typeName, tmpVarName);
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs, out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      wr.Write($"for ({DafnyTupleClass(L)}<{tupleTypeArgs}> {boundVarName} : ");
      collectionWriter = wr.Fork();
      return wr.NewBlock(")");
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (ct is SetType) {
        var wStmts = wr.Fork();
        wr.Write($"{collName}.add(");
        var coercedWr = EmitCoercionIfNecessary(elmt.Type, NativeObjectType, elmt.tok, wr);
        coercedWr.Append(Expr(elmt, inLetExprBody, wStmts));
        wr.WriteLine(");");
      } else {
        Contract.Assume(false);  // unexpected collection type
      }
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      if (ct is SetType) {
        var typeName = BoxedTypeName(ct.Arg, wr, tok);
        return $"new {DafnySetClass}<{typeName}>({collName})";
      } else if (ct is MapType) {
        var mt = (MapType)ct;
        var domtypeName = BoxedTypeName(mt.Domain, wr, tok);
        var rantypeName = BoxedTypeName(mt.Range, wr, tok);
        return $"new {DafnyMapClass}<{domtypeName},{rantypeName}>({collName})";
      } else {
        Contract.Assume(false);  // unexpected collection type
        throw new cce.UnreachableException();  // please compiler
      }
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      var prefix = createContinueLabel ? "continue_" : "goto_";
      return wr.NewNamedBlock($"{prefix}{label}:");
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine(label == null ? "break;" : $"break goto_{label};");
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      wr.WriteLine($"break continue_{label};");
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      if (message == null) {
        message = "unexpected control point";
      }

      wr.WriteLine($"throw new IllegalArgumentException(\"{message}\");");
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr, bool needIterLimit) {
      if (!needIterLimit) {
        EmitAbsurd(message, wr);
      }
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write("throw new dafny.DafnyHaltException(");
      if (tok != null) {
        wr.Write("\"" + Dafny.ErrorReporter.TokenToString(tok) + ": \" + ");
      }

      EmitToString(wr, messageExpr, wStmts);
      wr.WriteLine(");");
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      var cw = (ClassWriter)CreateClass(IdProtect(nt.EnclosingModuleDefinition.CompileName), IdName(nt), nt, wr);
      var w = cw.StaticMemberWriter;
      if (nt.NativeType != null) {
        var nativeType = GetBoxedNativeTypeName(nt.NativeType);
        var wEnum = w.NewNamedBlock($"public static java.util.ArrayList<{nativeType}> IntegerRange(java.math.BigInteger lo, java.math.BigInteger hi)");
        wEnum.WriteLine($"java.util.ArrayList<{nativeType}> arr = new java.util.ArrayList<>();");
        var numberval = $"{GetNativeTypeName(nt.NativeType)}Value()";
        wEnum.WriteLine($"for (java.math.BigInteger j = lo; j.compareTo(hi) < 0; j = j.add(java.math.BigInteger.ONE)) {{ arr.add({nativeType}.valueOf(j.{numberval})); }}");
        wEnum.WriteLine("return arr;");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var wStmts = w.Fork();
        var witness = new ConcreteSyntaxTree(w.RelativeIndentLevel);
        witness.Append(Expr(nt.Witness, false, wStmts));
        if (nt.NativeType == null) {
          cw.DeclareField("Witness", nt, true, true, nt.BaseType, nt.tok, witness.ToString(), null);
        } else {
          var nativeType = GetNativeTypeName(nt.NativeType);
          // Hacky way of doing the conversion from any (including BigInteger) to any
          w.Write("public static {0} Witness = ((java.lang.Number) (", nativeType);
          w.Append(witness);
          w.WriteLine($")).{nativeType}Value();");
        }
      }
      return cw;
    }

    protected override string ArrayIndexToNativeInt(string s, Type type) {
      var nt = AsNativeType(type);
      if (nt == null) {
        return $"({s}).intValue()";
      } else if (nt.Sel == NativeType.Selection.Int || nt.Sel == NativeType.Selection.UInt) {
        return s;
      } else if (IsUnsignedJavaNativeType(nt)) {
        return $"{DafnyHelpersClass}.unsignedToInt({s})";
      } else {
        return $"{DafnyHelpersClass}.toInt({s})";
      }
    }

    // if checkRange is false, msg is ignored
    // if checkRange is true and msg is null and the value is out of range, a generic message is emitted
    // if checkRange is true and msg is not null and the value is out of range, msg is emitted in the error message
    private void TrExprAsInt(Expression expr, ConcreteSyntaxTree wr, bool inLetExprBody, ConcreteSyntaxTree wStmts,
      bool checkRange = false, string msg = null) {
      var wrExpr = new ConcreteSyntaxTree();
      wrExpr.Append(Expr(expr, inLetExprBody, wStmts));
      TrExprAsInt(wrExpr.ToString(), expr.Type, wr, checkRange, msg);
    }

    // if checkRange is false, msg is ignored
    // if checkRange is true and msg is null and the value is out of range, a generic message is emitted
    // if checkRange is true and msg is not null and the value is out of range, msg is emitted in the error message
    private void TrExprAsInt(string expr, Type type, ConcreteSyntaxTree wr, bool checkRange = false, string msg = null) {
      var nt = AsNativeType(type);
      if (nt == null) {
        wr.Write($"{DafnyHelpersClass}.toInt" + (checkRange ? "Checked(" : "("));
        wr.Write($"({expr})");
        if (checkRange) {
          wr.Write(msg == null ? ", null" : $", \"{msg}\"");
        }

        wr.Write(")");
      } else if (nt.Sel == NativeType.Selection.Int || nt.Sel == NativeType.Selection.UInt) {
        wr.Write(expr);
      } else if (IsUnsignedJavaNativeType(nt)) {
        wr.Write($"{DafnyHelpersClass}.unsignedToInt" + (checkRange ? "Checked(" : "("));
        wr.Write(expr);
        if (checkRange) {
          wr.Write(msg == null ? ", null" : $", \"{msg}\"");
        }

        wr.Write(")");
      } else {
        wr.Write($"{DafnyHelpersClass}.toInt" + (checkRange ? "Checked(" : "("));
        wr.Write(expr);
        if (checkRange) {
          wr.Write(msg == null ? ", null" : $", \"{msg}\"");
        }

        wr.Write(")");
      }
    }

    private void TrParenExprAsInt(Expression expr, ConcreteSyntaxTree wr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
      wr.Write("(");
      TrExprAsInt(expr, wr, inLetExprBody, wStmts);
      wr.Write(")");
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<string> dimensions,
        bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      // Where to put the array to be wrapped
      ConcreteSyntaxTree wBareArray;
      if (dimensions.Count > 1) {
        arrays.Add(dimensions.Count);
        wr.Write($"new {DafnyMultiArrayClass(dimensions.Count)}<>({TypeDescriptor(elementType, wr, tok)}, ");
        foreach (var dim in dimensions) {
          TrExprAsInt(dim, Type.Int, wr, checkRange: true, msg: "Java arrays may be no larger than the maximum 32-bit signed int");
          wr.Write(", ");
        }
        wBareArray = wr.Fork();
        wr.Write(")");
        if (mustInitialize) {
          wr.Write($".fillThenReturn({DefaultValueCoercedIfNecessary(elementType, wr, tok, true)})");
        }
      } else {
        wr.Write($"({ArrayTypeName(elementType, dimensions.Count, wr, tok, false)}) ");
        if (mustInitialize) {
          wr.Write($"{TypeDescriptor(elementType, wr, tok)}.fillThenReturnArray(");
        }
        wBareArray = wr.Fork();
        if (mustInitialize) {
          wr.Write($", {DefaultValueCoercedIfNecessary(elementType, wr, tok, true)})");
        }
      }

      if (dimensions.Count > 1) {
        wBareArray.Write($"(Object{Repeat("[]", dimensions.Count - 1)}) ");
      }
      wBareArray.Write($"{TypeDescriptor(elementType, wr, tok)}.newArray(");
      var sep = "";
      foreach (var dim in dimensions) {
        wBareArray.Write(sep);
        TrExprAsInt(dim, Type.Int, wBareArray, checkRange: true, msg: "Java arrays may be no larger than the maximum 32-bit signed int");
        sep = ", ";
      }
      wBareArray.Write(")");
    }

    protected override bool TargetLambdaCanUseEnclosingLocals => false;

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      if (boundTypes.Count != 1) {
        functions.Add(boundTypes.Count);
      }
      wr.Write("(({0}<{1}{2}>)", DafnyFunctionIface(boundTypes.Count), Util.Comma("", boundTypes, t => BoxedTypeName(t, wr, resultTok) + ", "), BoxedTypeName(resultType, wr, resultTok));
      wr.Write($"({Util.Comma(boundVars)}) -> ");
      var w = wr.Fork();
      wr.Write(").apply");
      TrExprList(arguments, wr, inLetExprBody, wStmts);
      return w;
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr, string start = null) {
      start = start ?? "java.math.BigInteger.ZERO";
      return wr.NewNamedBlock($"for (java.math.BigInteger {indexVar} = {start}; {indexVar}.compareTo({bound}) < 0; {indexVar} = {indexVar}.add(java.math.BigInteger.ONE))");
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string /*?*/ endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {

      var nativeType = AsNativeType(loopIndex.Type);

      wr.Write($"for ({TypeName(loopIndex.Type, wr, tok)} {loopIndex.CompileName} = ");
      var startWr = wr.Fork();
      wr.Write($"; ");

      ConcreteSyntaxTree bodyWr;
      if (goingUp) {
        if (endVarName == null) {
          wr.Write("");
        } else if (nativeType == null) {
          wr.Write($"{loopIndex.CompileName}.compareTo({endVarName}) < 0");
        } else if (0 <= nativeType.LowerBound) {
          wr.Write($"{HelperClass(nativeType)}.compareUnsigned({loopIndex.CompileName}, {endVarName}) < 0");
        } else {
          wr.Write($"{loopIndex.CompileName} < {endVarName}");
        }
        if (nativeType == null) {
          bodyWr = wr.NewBlock($"; {loopIndex.CompileName} = {loopIndex.CompileName}.add(java.math.BigInteger.ONE))");
        } else {
          bodyWr = wr.NewBlock($"; {loopIndex.CompileName}++)");
        }
      } else {
        if (endVarName == null) {
          wr.Write("");
        } else if (nativeType == null) {
          wr.Write($"{endVarName}.compareTo({loopIndex.CompileName}) < 0");
        } else if (0 <= nativeType.LowerBound) {
          wr.Write($"{HelperClass(nativeType)}.compareUnsigned({endVarName}, {loopIndex.CompileName}) < 0");
        } else {
          wr.Write($"{endVarName} < {loopIndex.CompileName}");
        }
        bodyWr = wr.NewBlock($"; )");
        if (nativeType == null) {
          bodyWr.WriteLine($"{loopIndex.CompileName} = {loopIndex.CompileName}.subtract(java.math.BigInteger.ONE);");
        } else {
          bodyWr.WriteLine($"{loopIndex.CompileName}--;");
        }
      }
      bodyWr = EmitContinueLabel(labels, bodyWr);
      TrStmtList(body, bodyWr);

      return startWr;
    }

    protected override string GetHelperModuleName() => DafnyHelpersClass;

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      wr.WriteLine("new java.util.ArrayList<>();");
    }

    protected override void AddTupleToSet(int i) {
      tuples.Add(i);
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      // FIXME: tupleTypeArgs is wrong because it already got generated from
      // TypeName (with unboxed being the default)  :-(
      wr.Write($"{ingredients}.add(new {DafnyTupleClassPrefix}");
      var wrTuple = wr.Fork();
      wr.Write("));");
      return wrTuple;
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      TrParenExpr(expr, wr, inLetExprBody, wStmts);
      wr.Write(".intValue()");
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      wr.Write($"{prefix}.dtor__{i}()");
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr = EmitCoercionIfNecessary(NativeObjectType, functionType.AsArrowType.Result, tok, wr);
      TrParenExpr(function, wr, inLetExprBody, wStmts);
      wr.Write(".apply");
      TrExprList(arguments, wr, inLetExprBody, wStmts, typeAt: _ => NativeObjectType);
    }

    protected override bool NeedsCastFromTypeParameter => true;

    protected override bool TargetSubtypingRequiresEqualTypeArguments(Type type) {
      return type.AsCollectionType == null;
    }

    protected override bool IsCoercionNecessary(Type/*?*/ from, Type/*?*/ to) {
      from = from == null ? null : DatatypeWrapperEraser.SimplifyType(Options, from);
      to = to == null ? null : DatatypeWrapperEraser.SimplifyType(Options, to);

      if (to == NativeObjectType) {
        return false;
      }
      if (from == NativeObjectType) {
        return true;
      }

      if (UnicodeCharEnabled && ((IsNativeObjectType(from) && to.IsCharType) || (from.IsCharType && IsNativeObjectType(to)))) {
        // Need to box from int to CodePoint, or unbox from CodePoint to int
        return true;
      }

      if (from.IsArrayType && to.IsArrayType) {
        var dims = from.AsArrayType.Dims;
        Contract.Assert(dims == to.AsArrayType.Dims);
        if (dims > 1) {
          return false;
        }

        var udtFrom = (UserDefinedType)from.NormalizeExpand();
        var udtTo = (UserDefinedType)to.NormalizeExpand();
        return udtFrom.TypeArgs[0].IsTypeParameter && !udtTo.TypeArgs[0].IsTypeParameter;
      }

      return false;
    }

    protected override Type TypeForCoercion(Type type) {
      return NativeObjectType;
    }

    // We use null to represent java.lang.Object, as that's a decent
    // default native type for "no type information".
    // We don't use the SpecialNativeType approach that the Go compiler
    // uses for string because that kind of compiler-specific Type implementation
    // doesn't fit well into the generic logic on Types
    // (see for example https://github.com/dafny-lang/dafny/issues/2989).
    private static readonly Type NativeObjectType = null;

    private bool IsNativeObjectType(Type type) {
      return type == NativeObjectType || type.IsTypeParameter;
    }

    protected override ConcreteSyntaxTree EmitCoercionIfNecessary(Type/*?*/ from, Type/*?*/ to, IToken tok, ConcreteSyntaxTree wr) {
      from = from == null ? null : DatatypeWrapperEraser.SimplifyType(Options, from);
      to = to == null ? null : DatatypeWrapperEraser.SimplifyType(Options, to);

      if (UnicodeCharEnabled) {
        // Need to box from int to CodePoint, or unbox from CodePoint to int

        if (IsNativeObjectType(from) && to is { IsCharType: true }) {
          wr.Write("((dafny.CodePoint)(");
          var w = wr.Fork();
          wr.Write(")).value()");
          return w;
        }

        if (from is { IsCharType: true } && IsNativeObjectType(to)) {
          wr.Write("dafny.CodePoint.valueOf(");
          var w = wr.Fork();
          wr.Write(")");
          return w;
        }
      }

      if (IsCoercionNecessary(from, to)) {
        return EmitDowncast(from, to, tok, wr);
      }

      return wr;
    }

    protected override ConcreteSyntaxTree EmitDowncast(Type from, Type to, IToken tok, ConcreteSyntaxTree wr) {
      wr.Write($"(({TypeName(to, wr, tok)})(java.lang.Object)(");
      var w = wr.Fork();
      wr.Write("))");
      return w;
    }

    protected override ConcreteSyntaxTree EmitCoercionToNativeInt(ConcreteSyntaxTree wr) {
      wr.Write("((java.math.BigInteger)");
      var w = wr.Fork();
      wr.Write(").intValue()");
      return w;
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      return wr.NewNamedBlock($"for (java.math.BigInteger {indexVar} = java.math.BigInteger.valueOf({start}); ; {indexVar} = {indexVar}.multiply(new java.math.BigInteger(\"2\")))");
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      wr.Write($"{varName}.equals(java.math.BigInteger.ZERO)");
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{varName} = {varName}.subtract(java.math.BigInteger.ONE);");
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      wr.WriteLine($"{varName} = {varName}.add(java.math.BigInteger.ONE);");
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write("java.util.Arrays.asList");
      TrParenExpr(e, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"((java.util.function.Function<java.math.BigInteger, {BoxedTypeName(resultType, wr, resultTok)}>)(({bvName}) ->");
      var w = wr.NewBigExprBlock("", $")).apply(java.math.BigInteger.valueOf({source}))");
      return w;
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term, bool inLetExprBody, ConcreteSyntaxTree wr) {
      var wStmts = wr.Fork();
      wr.Write($"{collName}.put(");
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      wr.Append(Expr(term, inLetExprBody, wStmts));
      wr.WriteLine(");");
      return termLeftWriter;
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write($"{DafnySeqClass}.Create({TypeDescriptor(expr.Type.AsCollectionType.Arg, wr, expr.tok)}, ");
      wr.Append(Expr(expr.N, inLetExprBody, wStmts));
      wr.Write(", ");
      wr.Append(Expr(expr.Initializer, inLetExprBody, wStmts));
      wr.Write(")");
    }

    // Warning: NOT the same as NativeType.Bitwidth, which is zero except for
    // bitvector types
    private static int NativeTypeSize(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return 8;
        case JavaNativeType.Short: return 16;
        case JavaNativeType.Int: return 32;
        case JavaNativeType.Long: return 64;
        default: Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      Expression arg = e.E;
      Type fromType = e.E.Type;
      Type toType = e.ToType;
      if (fromType.IsNumericBased(Type.NumericPersuasion.Int) || fromType.IsBitVectorType || fromType.IsCharType) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // (int or bv or char) -> real
          Contract.Assert(AsNativeType(toType) == null);
          wr.Write($"new {DafnyBigRationalClass}(");
          if (AsNativeType(fromType) != null) {
            wr.Write("java.math.BigInteger.valueOf");
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
            wr.Write(", java.math.BigInteger.ONE)");
          } else if (fromType.IsCharType) {
            wr.Append(Expr(arg, inLetExprBody, wStmts));
            wr.Write(", 1)");
          } else {
            wr.Append(Expr(arg, inLetExprBody, wStmts));
            wr.Write(", java.math.BigInteger.ONE)");
          }
        } else if (toType.IsCharType) {
          // (int or bv or char) -> char
          // Painfully, Java sign-extends bytes when casting to chars ...
          if (fromType.IsCharType) {
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
          } else {
            var fromNative = AsNativeType(fromType);
            wr.Write($"({CharTypeName(false)})");
            if (fromNative != null && fromNative.Sel == NativeType.Selection.Byte) {
              wr.Write("java.lang.Byte.toUnsignedInt");
              TrParenExpr(arg, wr, inLetExprBody, wStmts);
            } else {
              TrExprAsInt(arg, wr, inLetExprBody, wStmts);
            }
          }
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative == null && toNative == null) {
            if (fromType.IsCharType) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("java.math.BigInteger.valueOf");
              TrParenExpr(arg, wr, inLetExprBody, wStmts);
            } else {
              // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
              wr.Append(Expr(arg, inLetExprBody, wStmts));
            }
          } else if (fromNative != null && toNative == null) {
            // native (int or bv) -> big-integer (int or bv)
            if (fromNative.Sel == NativeType.Selection.ULong) {
              // Can't just use .longValue() because that may return a negative
              wr.Write($"{DafnyHelpersClass}.unsignedLongToBigInteger");
              TrParenExpr(arg, wr, inLetExprBody, wStmts);
            } else {
              wr.Write("java.math.BigInteger.valueOf(");
              if (fromNative.LowerBound >= 0) {
                TrParenExpr($"{GetBoxedNativeTypeName(fromNative)}.toUnsignedLong", arg, wr, inLetExprBody, wStmts);
              } else {
                TrParenExpr(arg, wr, inLetExprBody, wStmts);
              }
              wr.Write(")");
            }
          } else if (fromNative != null && NativeTypeSize(toNative) == NativeTypeSize(fromNative)) {
            // native (int or bv) -> native (int or bv)
            // Cast between signed and unsigned, which have the same Java type
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
          } else {
            GetNativeInfo(toNative.Sel, out var toNativeName, out var toNativeSuffix, out var toNativeNeedsCast);
            // any (int or bv) -> native (int or bv)
            // A cast would do, but we also consider some optimizations
            var literal = PartiallyEvaluate(arg);
            UnaryOpExpr u = arg.Resolved as UnaryOpExpr;
            MemberSelectExpr m = arg.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              EmitNativeIntegerLiteral((BigInteger)literal, toNative, wr);
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize || to avoid intermediate BigInteger
              wr.Write(CastIfSmallNativeType(toType));
              TrParenExpr("", u.E, wr, inLetExprBody, wStmts);
              wr.Write(".cardinalityInt()");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .length to avoid intermediate BigInteger
              wr.Write(CastIfSmallNativeType(toType));
              var elmtType = UserDefinedType.ArrayElementType(m.Obj.Type);
              ConcreteSyntaxTree w;
              if (elmtType.IsTypeParameter) {
                wr.Write($"{FormatTypeDescriptorVariable(elmtType.AsTypeParameter)}.getArrayLength(");
                w = wr.Fork();
                wr.Write(")");
              } else {
                w = wr.Fork();
                wr.Write(".length");
              }
              TrParenExpr(m.Obj, w, inLetExprBody, wStmts);
            } else {
              // no optimization applies; use the standard translation
              if (fromNative != null && fromNative.LowerBound >= 0 && NativeTypeSize(fromNative) < NativeTypeSize(toNative)) {
                // Widening an unsigned value; careful!!
                wr.Write($"{CastIfSmallNativeType(e.ToType)}{GetBoxedNativeTypeName(fromNative)}");
                if (NativeTypeSize(toNative) == 64) {
                  wr.Write(".toUnsignedLong");
                } else {
                  wr.Write(".toUnsignedInt");
                }
                TrParenExpr(arg, wr, inLetExprBody, wStmts);
              } else {
                if (fromNative == null && !fromType.IsCharType) {
                  TrParenExpr(arg, wr, inLetExprBody, wStmts);
                  wr.Write($".{toNativeName}Value()");
                } else {
                  wr.Write($"(({toNativeName}) ");
                  TrParenExpr(arg, wr, inLetExprBody, wStmts);
                  wr.Write(")");
                }
              }
            }
          }
        }
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
        Contract.Assert(AsNativeType(fromType) == null);
        if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(toType) == null);
          wr.Append(Expr(arg, inLetExprBody, wStmts));
        } else if (toType.IsCharType) {
          // real -> char
          // Painfully, Java sign-extends bytes when casting to chars ...
          wr.Write($"({CharTypeName(false)})");
          TrParenExpr(arg, wr, inLetExprBody, wStmts);
          wr.Write(".ToBigInteger().intValue()");
        } else if (toType.IsBigOrdinalType) {
          TrParenExpr(arg, wr, inLetExprBody, wStmts);
          wr.Write(".ToBigInteger()");
        } else {
          // real -> (int or bv)
          TrParenExpr(arg, wr, inLetExprBody, wStmts);
          wr.Write(".ToBigInteger()");
          if (AsNativeType(toType) != null) {
            wr.Write($".{GetNativeTypeName(AsNativeType(toType))}Value()");
          }
        }
      } else if (fromType.IsBigOrdinalType) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Int) || toType.IsCharType) {
          // ordinal -> int, char
          if (AsNativeType(toType) != null) {
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
            wr.Write($".{GetNativeTypeName(AsNativeType(toType))}Value()");
          } else if (toType.IsCharType) {
            wr.Write($"({CharTypeName(false)})");
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
            wr.Write(".intValue()");
          } else {
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
          }
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // ordinal -> real
          wr.Write($"new {DafnyBigRationalClass}(");
          wr.Append(Expr(arg, inLetExprBody, wStmts));
          wr.Write(", java.math.BigInteger.ONE)");
        } else if (toType.IsBitVectorType) {
          // ordinal -> bv
          if (AsNativeType(toType) != null) {
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
            wr.Write($".{GetNativeTypeName(AsNativeType(toType))}Value()");
          } else {
            TrParenExpr(arg, wr, inLetExprBody, wStmts);
          }
        } else if (toType.IsBigOrdinalType) {
          TrParenExpr(arg, wr, inLetExprBody, wStmts);
        } else {
          Contract.Assert(false, $"not implemented for java: {fromType} -> {toType}");
        }
      } else {
        Contract.Assert(false, $"not implemented for java: {fromType} -> {toType}");
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      Contract.Requires(fromType.IsRefType);
      Contract.Requires(toType.IsRefType);

      // from T to U:   t instanceof U && ...
      // from T to U?:  t instanceof U && ...                 // since t is known to be non-null, this is fine
      // from T? to U:  t instanceof U && ...                 // note, "instanceof" implies non-null, so no need for explicit null check
      // from T? to U?: t == null || (t instanceof U && ...)
      if (!fromType.IsNonNullRefType && !toType.IsNonNullRefType) {
        wr.Write($"{localName} == null || (");
      }

      if (toType.IsObjectQ) {
        wr.Write("true");
      } else {
        var typeName = toType.IsObject ? "Object" : FullTypeName((UserDefinedType)toType.NormalizeExpand());
        wr.Write($"{localName} instanceof {typeName}");
        localName = $"(({typeName}){localName})";
      }

      var udtTo = (UserDefinedType)toType.NormalizeExpandKeepConstraints();
      if (udtTo.ResolvedClass is SubsetTypeDecl && !(udtTo.ResolvedClass is NonNullTypeDecl)) {
        // TODO: test constraints
        throw new UnsupportedFeatureException(tok, Feature.SubsetTypeTests);
      }

      if (!fromType.IsNonNullRefType && !toType.IsNonNullRefType) {
        wr.Write(")");
      }
    }

    protected override bool IssueCreateStaticMain(Method m) {
      return true;
    }
    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      var wr = ((ClassWriter)cw).StaticMemberWriter;
      return wr.NewBlock($"public static void __Main(dafny.DafnySequence<? extends dafny.DafnySequence<? extends {CharTypeName(true)}>> {argsParameterName})");
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      wr = EmitCoercionIfNecessary(NativeObjectType, bodyType, bvTok, wr);
      var boxedBvType = BoxedTypeName(bvType, wr, bvTok);
      wr.Write("{0}.<{1}, {2}>Let(", DafnyHelpersClass, boxedBvType, BoxedTypeName(bodyType, wr, bodyTok));
      wrRhs = wr.Fork();
      wrRhs = EmitCoercionIfNecessary(bvType, NativeObjectType, bvTok, wrRhs);

      var boxedBvName = idGenerator.FreshId("boxed");
      wr.Write($", {boxedBvName} ->");
      var wrBodyWithCoercion = wr.NewBlock();
      wrBodyWithCoercion.Write($"{TypeName(bvType, wr, bvTok)} {bvName} = ");
      var wrUnboxed = EmitCoercionIfNecessary(NativeObjectType, bvType, bvTok, wrBodyWithCoercion.Fork());
      wrUnboxed.Write(boxedBvName);
      wrBodyWithCoercion.WriteLine(";");

      wrBodyWithCoercion.Write("return ");
      wrBody = wrBodyWithCoercion.Fork();
      wrBody = EmitCoercionIfNecessary(bodyType, NativeObjectType, bodyTok, wrBody);
      wrBodyWithCoercion.WriteLine(";");
      wr.Write(")");
    }

    protected override string GetQuantifierName(string bvType) {
      return $"{DafnyHelpersClass}.Quantifier";
    }

    // ABSTRACT METHOD DECLARATIONS FOR THE SAKE OF BUILDING PROGRAM

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(iter.tok, Feature.Iterators);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      var tryBlock = wr.NewBlock("try");
      TrStmt(body, tryBlock);
      var catchBlock = wr.NewBlock("catch (dafny.DafnyHaltException e)");
      catchBlock.WriteLine($"dafny.DafnySequence<Character> {haltMessageVarName} = dafny.DafnySequence.asString(e.getMessage());");
      TrStmt(recoveryBody, catchBlock);
    }
  }
}
