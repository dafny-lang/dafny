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
using System.Text.RegularExpressions;
using System.Reflection;
using Bpl = Microsoft.Boogie;



namespace Microsoft.Dafny{
  public class JavaCompiler : Compiler{
    public JavaCompiler(ErrorReporter reporter)
      : base(reporter){
      IntSelect = ",java.math.BigInteger";
      LambdaExecute = ".apply";
    }

    public override String TargetLanguage => "Java";


    // Shadowing variables in Compiler.cs
    new string DafnySetClass = "dafny.DafnySet";
    new string DafnyMultiSetClass = "dafny.DafnyMultiset";
    new string DafnySeqClass = "dafny.DafnySequence";
    new string DafnyMapClass = "dafny.DafnyMap";

    const string DafnyBigRationalClass = "dafny.BigRational";
    const string DafnyEuclideanClass = "dafny.DafnyEuclidean";
    const string DafnyHelpersClass = "dafny.Helpers";
    const string TypeClass = "dafny.Type";

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

    const string TypeMethodName = "_type";

    private String ModuleName;
    private String ModulePath;
    private int FileCount = 0;
    private Import ModuleImport;
    private HashSet<int> tuples = new HashSet<int>();
    private HashSet<int> functions = new HashSet<int>();
    private HashSet<int> arrays = new HashSet<int>();

    private readonly List<Import> Imports = new List<Import>();

    //RootImportWriter writes additional imports to the main file.
    private TargetWriter RootImportWriter;

    private struct Import{
      public string Name, Path;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    public override bool SupportsInMemoryCompilation => false;

    protected override bool SupportsAmbiguousTypeDecl => false;
    protected override bool SupportsProperties => false;
    protected override bool NeedsWrappersForInheritedFields => false;
    protected override bool FieldsInTraits => false;

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

    protected override void DeclareSpecificOutCollector(string collectorVarName, TargetWriter wr, List<Type> types, List<Type> formalTypes, List<Type> lhsTypes) {
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
          returnedTypes.Add(TypeName(lhsType, wr, Bpl.Token.NoToken, boxed: types.Count > 1));
        }
      }
      if (types.Count > 1) {
        tuples.Add(types.Count);
        wr.Write($"{DafnyTupleClassPrefix}{types.Count}<{Util.Comma(returnedTypes)}> {collectorVarName} = ");
      } else {
        wr.Write($"{returnedTypes[0]} {collectorVarName} = ");
      }
    }
    protected override void EmitCastOutParameterSplits(string outCollector, List<string> lhsNames,
      TargetWriter wr, List<Type> outTypes, List<Type> formalTypes, List<Type> lhsTypes, Bpl.IToken tok){
      var wOuts = new List<TargetWriter>();
      for (var i = 0; i < lhsNames.Count; i++){
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
        wr.Write($"({TypeName(lhsTypes[i], wr, Bpl.Token.NoToken)}) (Object) ");
        if (lhsNames.Count == 1) {
          wr.Write(outCollector);
        } else {
          wr.Write($"{outCollector}.dtor__{i}()");
        }
        EndStmt(wr);
      }
    }

    protected override void EmitMemberSelect(AssignStmt s0, List<Type> tupleTypeArgsList, TargetWriter wr, string tup){
      wr.Write("(");
      var lhs = (MemberSelectExpr) s0.Lhs;
      var wCoerced = EmitCoercionIfNecessary(from: null, to: tupleTypeArgsList[0], tok: s0.Tok, wr: wr);
      wCoerced.Write($"({TypeName(tupleTypeArgsList[0].NormalizeExpand(), wCoerced, s0.Tok)})");
      EmitTupleSelect(tup, 0, wCoerced);
      wr.Write(")");
      wr.Write($".{IdMemberName(lhs)} = ");
      wCoerced = EmitCoercionIfNecessary(from: null, to: tupleTypeArgsList[1], tok: s0.Tok, wr: wr);
      wCoerced.Write($"({TypeName(tupleTypeArgsList[1].NormalizeExpand(), wCoerced, s0.Tok)})");
      EmitTupleSelect(tup, 1, wCoerced);
      EndStmt(wr);
    }

    protected override void EmitSeqSelect(AssignStmt s0, List<Type> tupleTypeArgsList, TargetWriter wr, string tup){
      wr.Write("(");
      var lhs = (SeqSelectExpr) s0.Lhs;
      TargetWriter wColl, wIndex, wValue;
      EmitIndexCollectionUpdate(out wColl, out wIndex, out wValue, wr, nativeIndex: true);
      var wCoerce = EmitCoercionIfNecessary(from: null, to: lhs.Seq.Type, tok: s0.Tok, wr: wColl);
        wCoerce.Write($"({TypeName(lhs.Seq.Type.NormalizeExpand(), wCoerce, s0.Tok)})");
        EmitTupleSelect(tup, 0, wCoerce);
        wColl.Write(")");
      var wCast = EmitCoercionToNativeInt(wIndex);
      EmitTupleSelect(tup, 1, wCast);
        wValue.Write($"({TypeName(tupleTypeArgsList[2].NormalizeExpand(), wValue, s0.Tok)})");
      EmitTupleSelect(tup, 2, wValue);
      EndStmt(wr);
    }

    protected override void EmitMultiSelect(AssignStmt s0, List<Type> tupleTypeArgsList, TargetWriter wr, string tup, int L){
      wr.Write("(");
      var lhs = (MultiSelectExpr) s0.Lhs;
      var wArray = new TargetWriter(wr.IndentLevel, true);
      var wCoerced = EmitCoercionIfNecessary(from: null, to: tupleTypeArgsList[0], tok: s0.Tok, wr: wArray);
        wCoerced.Write($"({TypeName(tupleTypeArgsList[0].NormalizeExpand(), wCoerced, s0.Tok)})");
        EmitTupleSelect(tup, 0, wCoerced);
        wArray.Write(")");
      var array = wArray.ToString();
      var indices = new List<string>();
      for (int i = 0; i < lhs.Indices.Count; i++){
        var wIndex = new TargetWriter();
        wIndex.Write("((java.math.BigInteger)");
        EmitTupleSelect(tup, i + 1, wIndex);
        wIndex.Write(")");
        indices.Add(wIndex.ToString());
      }
      var lv = EmitArraySelectAsLvalue(array, indices, tupleTypeArgsList[L - 1]);
      var wrRhs = EmitAssignment(lv, tupleTypeArgsList[L - 1], null, wr);
      wrRhs.Write($"(({TypeName(tupleTypeArgsList[L - 1], wrRhs, s0.Tok)})");
      EmitTupleSelect(tup, L - 1, wrRhs);
      wrRhs.Write(")");
      EndStmt(wr);
    }

    protected override void WriteCast(string s, TargetWriter wr) {
      wr.Write($"({s})");
    }

    protected override TargetWriter DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, TargetWriter wr, Type t){
      return DeclareLocalVar(name, t, tok, wr);
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, Expression rhs,
      bool inLetExprBody, TargetWriter wr, Type t){
      var w = DeclareLocalVar(name, t, tok, wr);
      TrExpr(rhs, w, inLetExprBody);
    }

    protected override TargetWriter EmitIngredients(TargetWriter wr, string ingredients, int L, string tupleTypeArgs, ForallStmt s, AssignStmt s0, Expression rhs){
      using (var wrVarInit = wr){
        wrVarInit.Write($"java.util.ArrayList<{DafnyTupleClassPrefix}{L}<{tupleTypeArgs}>> {ingredients} = ");
        AddTupleToSet(L);
        EmitEmptyTupleList(tupleTypeArgs, wrVarInit);
      }
      var wrOuter = wr;
      wr = CompileGuardedLoops(s.BoundVars, s.Bounds, s.Range, wr);
      using (var wrTuple = EmitAddTupleToList(ingredients, tupleTypeArgs, wr)){
          wrTuple.Write($"{L}<{tupleTypeArgs}>(");
        if (s0.Lhs is MemberSelectExpr lhs1) {
          TrExpr(lhs1.Obj, wrTuple, false);
        } else if (s0.Lhs is SeqSelectExpr lhs2) {
          TrExpr(lhs2.Seq, wrTuple, false);
          wrTuple.Write(", ");
          TrParenExpr(lhs2.E0,  wrTuple, false);
        } else {
          var lhs = (MultiSelectExpr) s0.Lhs;
          TrExpr(lhs.Array, wrTuple, false);
          foreach (var t in lhs.Indices) {
            wrTuple.Write(", ");
            TrParenExpr(t,  wrTuple, false);
          }
        }
        wrTuple.Write(", ");
        if (rhs is MultiSelectExpr) {
          Type t = rhs.Type.NormalizeExpand();
          wrTuple.Write($"({TypeName(t, wrTuple, rhs.tok)})");
        }
        TrExpr(rhs, wrTuple, false);
      }
      return wrOuter;
    }

    protected override void EmitHeader(Program program, TargetWriter wr){
      wr.WriteLine($"// Dafny program {program.Name} compiled into Java");
      ModuleName = HasMain(program, out _) ? "main" : Path.GetFileNameWithoutExtension(program.Name);
      wr.WriteLine();
      // Keep the import writers so that we can import subsequent modules into the main one
      EmitImports(wr, out RootImportWriter);
      wr.WriteLine();
    }

    // Only exists to make sure method is overriden
    protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr){ }

    public override void EmitCallToMain(Method mainMethod, TargetWriter wr) {
      var companion = TypeName_Companion(mainMethod.EnclosingClass as ClassDecl, wr, mainMethod.tok);
      var wBody = wr.NewNamedBlock("public static void main(String[] args)");
      var modName = mainMethod.EnclosingClass.Module.CompileName == "_module" ? "_System." : "";
      companion = modName + companion;
      Coverage.EmitSetup(wBody);
      wBody.WriteLine($"{DafnyHelpersClass}.withHaltHandling({companion}::{IdName(mainMethod)});");
      Coverage.EmitTearDown(wBody);
    }

    void EmitImports(TargetWriter wr, out TargetWriter importWriter){
      importWriter = wr.ForkSection();
      foreach (var import in Imports){
        if (import.Name != ModuleName){
          EmitImport(import, importWriter);
        }
      }
    }

    private void EmitImport(Import import, TargetWriter importWriter){
      importWriter.WriteLine($"import {import.Path.Replace('/','.')}.*;");
    }

    protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string /*?*/ libraryName, TargetWriter wr) {
      if (isDefault) {
        // Fold the default module into the main module
        return wr;
      }
      var pkgName = libraryName ?? IdProtect(moduleName);
      var path = pkgName.Replace('.', '/');
      var import = new Import{ Name=moduleName, Path=path };
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

    private void AddImport(Import import){
      if (!Imports.Contains(import)) {
        EmitImport(import, RootImportWriter);
        Imports.Add(import);
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr){
      ClassWriter cw = CreateClass(IdName(sst), sst.TypeArgs, wr) as ClassWriter;
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled){
        var sw = new TargetWriter(cw.InstanceMemberWriter.IndentLevel, true);
        TrExpr(sst.Witness, sw, false);
        cw.DeclareField("Witness", true, true, sst.Rhs, sst.tok, sw.ToString());
      }
    }

    protected class ClassWriter : IClassWriter {
      public readonly JavaCompiler Compiler;
      public readonly TargetWriter InstanceMemberWriter;
      public readonly TargetWriter StaticMemberWriter;
      public readonly TargetWriter CtorBodyWriter;

      public ClassWriter(JavaCompiler compiler, TargetWriter instanceMemberWriter, TargetWriter ctorBodyWriter, BlockTargetWriter staticMemberWriter = null) {
        Contract.Requires(compiler != null);
        Contract.Requires(instanceMemberWriter != null);
        this.Compiler = compiler;
        this.InstanceMemberWriter = instanceMemberWriter;
        this.CtorBodyWriter = ctorBodyWriter;
        this.StaticMemberWriter = staticMemberWriter == null ? instanceMemberWriter : staticMemberWriter;
      }

      public TargetWriter Writer(bool isStatic) {
        return isStatic ? StaticMemberWriter : InstanceMemberWriter;
      }

      public BlockTargetWriter CreateConstructor(TopLevelDeclWithMembers c, List<TypeParameter> l){
        return Compiler.CreateConstructor(c, Writer(false), l);
      }

      public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
        return Compiler.CreateMethod(m, createBody, Writer(m.IsStatic));
      }
      public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic));
      }

      public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
        return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic));
      }
      public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
        return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, Writer(isStatic));
      }
      public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, this);
      }
      public TextWriter/*?*/ ErrorWriter() => InstanceMemberWriter;

      public void Finish() { }
    }

    protected BlockTargetWriter CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic,
      bool createBody, TargetWriter wr) {
      wr.Write("public {0}{1} get_{2}()", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      if (createBody) {
        var w = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        return w;
      } else {
        wr.WriteLine(";");
        return null;
      }
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, Expression rhs,
      bool inLetExprBody, TargetWriter wr){
      if (type == null){
        type = rhs.Type;
      }
      var w = DeclareLocalVar(name, type, tok, wr);
      TrExpr(rhs, w, inLetExprBody);
    }

    public BlockTargetWriter /*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic,
      bool createBody, out TargetWriter setterWriter, TargetWriter wr) {
      wr.Write("public {0}{1} get_{2}()", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      BlockTargetWriter wGet = null;
      if (createBody) {
        wGet = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      } else {
        wr.WriteLine(";");
      }
      wr.Write("public {0}void set_{1}({2} value)", isStatic? "static " : "", name, TypeName(resultType, wr, tok));
      if (createBody) {
        setterWriter = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      } else {
        wr.WriteLine(";");
        setterWriter = null;
      }
      return wGet;
    }
    protected BlockTargetWriter CreateMethod(Method m, bool createBody, TargetWriter wr) {
      if (m.IsExtern(out _, out _) && (m.IsStatic || m is Constructor)) {
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
        targetReturnTypeReplacement = DafnyTupleClassPrefix + nonGhostOuts;
      }
      var customReceiver = NeedsCustomReceiver(m);
      var receiverType = UserDefinedType.FromTopLevelDecl(m.tok, m.EnclosingClass);
      wr.Write("public {0}{1}", !createBody ? "abstract " : "", m.IsStatic || customReceiver ? "static " : "");
      if (m.TypeArgs.Count != 0) {
        wr.Write($"<{TypeParameters(m.TypeArgs)}> ");
      }
      wr.Write("{0} {1}", targetReturnTypeReplacement ?? "void", IdName(m));
      wr.Write("(");
      var nTypes = WriteRuntimeTypeDescriptorsFormals(m, m.TypeArgs, useAllTypeArgs: true, wr);
      var sep = nTypes > 0 ? ", " : "";
      if (customReceiver) {
        DeclareFormal(sep, "_this", receiverType, m.tok, true, wr);
        sep = ", ";
      }
      WriteFormals(sep, m.Ins, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      } else {
        return wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      }
    }

    protected override BlockTargetWriter EmitMethodReturns(Method m, BlockTargetWriter wr) {
      int nonGhostOuts = 0;
      foreach (var t in m.Outs) {
        if (t.IsGhost) continue;
        nonGhostOuts += 1;
        break;
      }
      if (!m.Body.Body.OfType<ReturnStmt>().Any() && (nonGhostOuts > 0 || m.IsTailRecursive)) { // If method has out parameters or is tail-recursive but no explicit return statement in Dafny
        var r = new TargetWriter(wr.IndentLevel);
        EmitReturn(m.Outs, r);
        wr.BodySuffix = r.ToString();
        wr = wr.NewBlock("if(true)"); // Ensure no unreachable error is thrown for the return statement
      }
      return wr;
    }

    protected BlockTargetWriter CreateConstructor(TopLevelDeclWithMembers c, TargetWriter wr, List<TypeParameter> l) {
      EmitSuppression(wr);
      wr.Write("public ");
      wr.Write(c.CompileName);
      wr.Write("(");
      var nTypes = WriteRuntimeTypeDescriptorsFormals(l, false, wr);
      var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      return w;
    }

    protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs,
      List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member,
      TargetWriter wr) {
      if (member.IsExtern(out _, out _) && isStatic) {
        // No need for abstract version of static method
        return null;
      }
      var customReceiver = NeedsCustomReceiver(member);
      var receiverType = UserDefinedType.FromTopLevelDecl(member.tok, member.EnclosingClass);
      wr.Write("public {0}{1}", !createBody ? "abstract " : "", isStatic || customReceiver ? "static " : "");
      if (typeArgs != null && typeArgs.Count != 0) {
        wr.Write($"<{TypeParameters(typeArgs)}>");
        wr.Write($"{TypeName(resultType, wr, tok)} {name}(");
      }
      else if (isStatic && resultType.TypeArgs.Count > 0 && resultType.TypeArgs[0].IsTypeParameter){
        string t = "";
        string n = "";
        SplitType(TypeName(resultType, wr, tok), out t, out n);
        wr.Write($"{t} {n} {name}(");
      }
      else{
        wr.Write($"{TypeName(resultType, wr, tok)} {name}(");
      }
      var sep = "";
      var argCount = 0;
      if (customReceiver) {
        DeclareFormal(sep, "_this", receiverType, tok, true, wr);
        sep = ", ";
        argCount++;
      }
      argCount += WriteRuntimeTypeDescriptorsFormals(typeArgs, useAllTypeArgs: true, wr, sep);
      if (argCount > 0) {
        sep = ", ";
      }
      argCount += WriteFormals(sep, formals, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      } else {
        BlockTargetWriter w;
        if (argCount > 1) {
          w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        } else {
          w = wr.NewBlock(")");
        }
        return w;
      }
    }

    private void SplitType(string s, out string t, out string n){
      string pat = @"([^<]+)(<.*>)";
      Regex r = new Regex(pat);
      Match m = r.Match(s);
      if (m.Groups.Count < 2){
        n = s;

        t = null;
      }
      else{
        n = m.Groups[1].Captures[0].Value;
        t = m.Groups[2].Captures[0].Value;
      }
    }

    protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, ClassWriter cw) {
      if (isStatic){
        var r = RemoveParams((rhs != null) ? rhs : DefaultValue(type, cw.StaticMemberWriter, tok));
        var t = RemoveParams(TypeName(type, cw.StaticMemberWriter, tok));
        cw.StaticMemberWriter.WriteLine($"public static {t} {name} = {r};");
      }
      else{
        Contract.Assert(cw.CtorBodyWriter != null, "Unexpected instance field");
        cw.InstanceMemberWriter.WriteLine("public {0} {1};", TypeName(type, cw.InstanceMemberWriter, tok), name);
        cw.CtorBodyWriter.WriteLine("this.{0} = {1};", name, rhs ?? DefaultValue(type, cw.CtorBodyWriter, tok, inAutoInitContext: true));
      }
    }

    private string RemoveParams(string s){
      return Regex.Replace(s, @"<.>", "");
    }

    private void EmitSuppression(TextWriter wr) {
      wr.WriteLine("@SuppressWarnings({\"unchecked\", \"deprecation\"})");
    }

    string TypeParameters(List<TypeParameter> targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      return Util.Comma(targs, tp => IdName(tp));
    }

    protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) {
      return TypeName(type, wr, tok, boxed: false, member);
    }

    private string BoxedTypeName(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName(type, wr, tok, boxed: true);
    }

    private string BoxedTypeNames(List<Type> types, TextWriter wr, Bpl.IToken tok) {
      return Util.Comma(types, t => BoxedTypeName(t, wr, tok));
    }

    protected override string TypeArgumentName(Type type, TextWriter wr, Bpl.IToken tok) {
      return BoxedTypeName(type, wr, tok);
    }

    private string TypeName(Type type, TextWriter wr, Bpl.IToken tok, bool boxed, MemberDecl/*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        return "Object";
      }
      if (xType is BoolType) {
        return boxed ? "Boolean" : "boolean";
      } else if (xType is CharType) {
        return boxed ? "Character" : "char";
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
        return ArrayTypeName(elType, at.Dims, wr, tok);
      } else if (xType is UserDefinedType udt) {
        if (udt.ResolvedParam != null) {
          if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(udt.ResolvedParam, out var instantiatedTypeParameter)) {
            return TypeName(instantiatedTypeParameter, wr, tok, member);
          }
        }
        var s = FullTypeName(udt, member);
        if (s.Equals("string")){
          return "String";
        }
        var cl = udt.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return boxed ? "Long" : "long";
        }
        else if (cl is TupleTypeDecl tupleDecl) {
          s = DafnyTupleClass(tupleDecl.TypeArgs.Count);
        }
        else if (DafnyOptions.O.IronDafny &&
                 !(xType is ArrowType) &&
                 cl != null &&
                 cl.Module != null &&
                 !cl.Module.IsDefaultModule){
          s = cl.FullCompileName;
        }

        // When accessing a static member, leave off the type arguments
        var typeArgs = member != null ? new List<Type>() : udt.TypeArgs;
        return TypeName_UDT(s, typeArgs, wr, udt.tok);
      } else if (xType is SetType) {
        Type argType = ((SetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnySetClass + "<" + BoxedTypeName(argType, wr, tok) + ">";
      } else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnySeqClass + "<" + BoxedTypeName(argType, wr, tok) + ">";

      } else if (xType is MultiSetType) {
        Type argType = ((MultiSetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnyMultiSetClass + "<" + BoxedTypeName(argType, wr, tok) + ">";
      } else if (xType is MapType) {
        Type domType = ((MapType)xType).Domain;
        Type ranType = ((MapType)xType).Range;
        if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) {
          Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnyMapClass + "<" + BoxedTypeName(domType, wr, tok) + "," + BoxedTypeName(ranType, wr, tok) + ">";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    string ArrayTypeName(Type elType, int dims, TextWriter wr, Bpl.IToken tok) {
      if (dims > 1) {
        arrays.Add(dims);
        return $"{DafnyMultiArrayClass(dims)}<{BoxedTypeName(elType, wr, tok)}>";
      } else if (elType.IsTypeParameter) {
        return "java.lang.Object";
      } else {
        return $"{TypeName(elType, wr, tok)}[]";
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
      Contract.Assume(udt != null); // precondition; this ought to be declared as a Requires in the superclass
      if (udt is ArrowType) {
        functions.Add(udt.TypeArgs.Count - 1);
        return DafnyFunctionIface(udt.TypeArgs.Count - 1);
      }
      string qualification;
      if (member != null && member.IsExtern(out qualification, out _) && qualification != null) {
        return qualification;
      }
      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      }
      else if (cl is TupleTypeDecl tupleDecl) {
        return DafnyTupleClass(tupleDecl.TypeArgs.Count);
      } else if (cl.Module.CompileName == ModuleName || cl.Module.IsDefaultModule) {
        return IdProtect(cl.CompileName);
      }
      else{
        return IdProtect(cl.Module.CompileName) + "." + IdProtect(cl.CompileName);
      }
    }

    protected override string TypeNameArrayBrackets(int dims) {
      var name = "[";
      for (int i = 1; i < dims; i++) {
        name += "][";
      }

      return name + "]";
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      if (!isInParam) return false;
      wr.Write($"{prefix}{TypeName(type, wr, tok)} {name}");
      return true;
    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      if (typeArgs.Count != 0) {
        if (typeArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }
        s += "<" + BoxedTypeNames(typeArgs, wr, tok) + ">";
      }
      return s;
    }

    protected string TypeName_UDT(string fullCompileName, List<Type> inArgs, Type outArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Assume(fullCompileName != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(inArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(outArgs != null);  // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      s += "<";
      if (inArgs.Count > 1) {
        if (inArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }
        s += DafnyTupleClass(inArgs.Count) + "<" + BoxedTypeNames(inArgs, wr, tok) + ">";
        tuples.Add(inArgs.Count);
      } else {
        if (inArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }
        s += "" + BoxedTypeNames(inArgs, wr, tok) + "";
      }
      if (outArgs != null) {
        if (inArgs.Count > 0){
          s += ", ";
        }
        s += BoxedTypeName(outArgs, wr, tok) + "";
      }
      s += ">";
      return s;
    }

    // We write an extern class as a base class that the actual extern class
    // needs to extend, so the extern methods and functions need to be abstract
    // in the base class
    protected override bool IncludeExternMembers { get => true; }

    //
    // An example to show how type parameters are dealt with:
    //
    //   class Class<T /* needs zero initializer */, U /* does not */> {
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
    protected override IClassWriter CreateClass(string name, bool isExtern, string /*?*/ fullPrintName,
      List<TypeParameter> /*?*/ typeParameters, List<Type> /*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
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
      var typeParamString = "";
      if (typeParameters != null && typeParameters.Count != 0) {
        typeParamString = $"<{TypeParameters(typeParameters)}>";
      }
      w.Write($"public {abstractness}class {javaName}{typeParamString}");
      string sep;
      // Since Java does not support multiple inheritance, we are assuming a list of "superclasses" is a list of interfaces
      if (superClasses != null) {
        sep = " implements ";
        foreach (var trait in superClasses) {
          w.Write($"{sep}{TypeName(trait, w, tok)}");
          sep = ", ";
        }
      }
      var wBody = w.NewBlock("");
      var wTypeFields = wBody.Fork();

      wBody.Write($"public {javaName}(");
      var wCtorParams = wBody.Fork();
      var wCtorBody = wBody.NewBigBlock(")", "");

      // TODO-RS: This used to filter to only type parameters with the MustSupportZeroInitialization
      // characteristic. That isn't enough for the Java runtime though, in which dafny.Sequence<T> needs
      // a type descriptor in order to optimize for primitive types. Requiring them for all type parameters
      // helps, but is still incomplete since other areas of the compiler are not providing them all the time.
      // This isn't yet exposed by the test suite so we can get away with this for now, but will need to address
      // the issue more completely soon.
      sep = "";
      if (typeParameters != null) {
        foreach (var tp in typeParameters) {
          var fieldName = FormatTypeDescriptorVariable(tp.CompileName);
          var decl = $"{TypeClass}<{tp.CompileName}> {fieldName}";
          wTypeFields.WriteLine($"private {decl};");
          wCtorParams.Write($"{sep}{decl}");
          wCtorBody.WriteLine($"this.{fieldName} = {fieldName};");
          sep = ", ";
        }
      }

      EmitTypeMethod(javaName, typeParameters, typeParameters, initializer: null, wBody);
      return new ClassWriter(this, wBody, wCtorBody);
    }

    private void EmitTypeMethod(string typeName, List<TypeParameter> typeParams, List<TypeParameter> usedTypeParams, string/*?*/ initializer, TargetWriter wr) {
      var typeParamString = "";
      if (typeParams != null && typeParams.Count != 0) {
        typeParamString = $"<{TypeParameters(typeParams)}>";
      }

      var typeDescriptorCast = $"({TypeClass}<{typeName}{typeParamString}>) ({TypeClass}<?>)";
      var typeDescriptorExpr = $"{TypeClass}.referenceWithInitializer({typeName}.class, () -> {initializer ?? "null"})";
      if (usedTypeParams == null || usedTypeParams.Count == 0) {
        wr.WriteLine($"private static final {TypeClass}<{typeName}> _TYPE = {typeDescriptorExpr};");
      }
      wr.Write($"public static {typeParamString}{TypeClass}<{typeName}{typeParamString}> _type(");
      if (usedTypeParams != null) {
        wr.Write(Util.Comma(usedTypeParams, tp => $"{TypeClass}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp.CompileName)}"));
      }
      var wTypeMethodBody = wr.NewBigBlock(")", "");
      if (usedTypeParams == null || usedTypeParams.Count == 0) {
        wTypeMethodBody.WriteLine($"return {typeDescriptorCast} _TYPE;");
      } else {
        wTypeMethodBody.WriteLine($"return {typeDescriptorCast} {typeDescriptorExpr};");
      }
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

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write($"({TypeName(e.Type, wr, e.tok)}) null");
      } else if (e.Value is bool value) {
        wr.Write(value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        wr.Write($"'{(string) e.Value}'");
      } else if (e is StringLiteralExpr str){
        wr.Write($"{DafnySeqClass}.asString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) is NativeType nt) {
        EmitNativeIntegerLiteral((BigInteger) e.Value, nt, wr);
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
      } else if (e.Value is Basetypes.BigDec n){
        if (0 <= n.Exponent){
          wr.Write($"new {DafnyBigRationalClass}(new java.math.BigInteger(\"{n.Mantissa}");
          for (int j = 0; j < n.Exponent; j++){
            wr.Write("0");
          }
          wr.Write("\"), java.math.BigInteger.ONE)");
        } else {
          wr.Write($"new {DafnyBigRationalClass}(");
          wr.Write($"new java.math.BigInteger(\"{n.Mantissa}\")");
          wr.Write(", new java.math.BigInteger(\"1");
          for (int j = n.Exponent; j < 0; j++){
            wr.Write("0");
          }
          wr.Write("\"))");
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      if (!isVerbatim) {
        wr.Write($"\"{str}\"");
      } else {
        //TODO: This is taken from Go and JS since Java doesn't have raw string literals, modify and make better if possible.
        var n = str.Length;
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i+1 < n && str[i+1] == '\"') {
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

    void EmitNativeIntegerLiteral(BigInteger value, NativeType nt, TextWriter wr) {
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
        case JavaNativeType.Byte: return "Byte";
        case JavaNativeType.Short: return "Short";
        case JavaNativeType.Int: return "Integer";
        case JavaNativeType.Long: return "Long";
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    // Note the (semantically iffy) distinction between a *primitive type*,
    // being one of the eight Java primitive types, and a NativeType, which can
    // only be one of the integer types.
    private bool IsJavaPrimitiveType(Type type) {
      return type.IsBoolType || type.IsCharType || AsNativeType(type) != null;
    }

    protected override void EmitThis(TargetWriter wr) {
      var custom =
        (enclosingMethod != null && enclosingMethod.IsTailRecursive) ||
        (enclosingFunction != null && enclosingFunction.IsTailRecursive) ||
        thisContext is NewtypeDecl;
      wr.Write(custom ? "_this" : "this");
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, TargetWriter wr){
      if (type != null && type.AsArrayType != null){
        arrays.Add(type.AsArrayType.Dims);
      }
      if (type.IsDatatype && type.AsDatatype is TupleTypeDecl) {
        tuples.Add(type.AsDatatype.TypeArgs.Count);
      }
      if (type.IsTypeParameter) {
        EmitSuppression(wr);
      }
      wr.Write("{0} {1}", type != null ? TypeName(type, wr, tok) : "Object", name);
      if (leaveRoomForRhs){
        Contract.Assert(rhs == null); // follows from precondition
      } else if (rhs != null){
        wr.WriteLine($" = {rhs};");
      } else if (type.IsIntegerType) {
        wr.WriteLine(" = java.math.BigInteger.ZERO;");
      } else {
        wr.WriteLine(";");
      }
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, TargetWriter wr, Type t) {
      DeclareLocalVar(name, t, tok, leaveRoomForRhs, rhs, wr);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr) {
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
      if (ct is SeqType && !IsJavaPrimitiveType(ct.Arg)) {
        wr.Write(TypeDescriptor(ct.Arg, wr, tok));
        sep = ", ";
      }
      foreach (Expression e in elements) {
        wr.Write(sep);
        TrExpr(e, wr, inLetExprBody);
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("dafny.DafnyMap.fromElements");
      wr.Write("(");
      string sep = "";
      foreach (ExpressionPair p in elements) {
        wr.Write(sep);
        wr.Write("new dafny.Tuple2(");
        TrExpr(p.A, wr, inLetExprBody);
        wr.Write(", ");
        TrExpr(p.B, wr, inLetExprBody);
        wr.Write(")");
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, out string compiledName, out string preString, out string postString) {
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
          compiledName = "toBigInteger()";
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
          compiledName = "dafnyKeySet()";
          break;
        case SpecialField.ID.Values:
          compiledName = "dafnyValues()";
          break;
        case SpecialField.ID.Items:
          compiledName = "dafnyEntrySet()";
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

    protected override ILvalue EmitMemberSelect(Action<TargetWriter> obj, MemberDecl member, Type expectedType, bool internalAccess = false) {
      if (member.EnclosingClass is TraitDecl && !member.IsStatic) {
        return new GetterSetterLvalue(obj, IdName(member));
      } else if (member is ConstantField) {
        return SuffixLvalue(obj, $".{member.CompileName}");
      } else if (member is SpecialField sf) {
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out var compiledName, out _, out _);
        if (compiledName.Length != 0){
          if (member.EnclosingClass is DatatypeDecl) {
            return new GetterSetterLvalue(obj, getter: compiledName, setter: null);
          } else {
            return SuffixLvalue(obj, $".{compiledName}");
          }
        } else {
          // Assume it's already handled by the caller
          return SimpleLvalue(obj);
        }
      } else if (member is Function) {
        return SuffixLvalue(obj, $"::{IdName(member)}");
      } else {
        return SuffixLvalue(obj, $".{IdName(member)}");
      }
    }

    // FIXME This is a bit sketchy: Rather than encapsulating the idea of an
    // lvalue, both EmitRead() and EmitWrite() assume (as does
    // EmitMemberSelect()) that the member has already been written and we need
    // only write the part starting with the period.  Cleaning up this logic
    // would require reworking the way EmitMemberSelect() is called.
    private class GetterSetterLvalue : ILvalue {
      private readonly Action<TargetWriter> Object;
      private readonly string Getter;
      private readonly string/*?*/ Setter;

      public GetterSetterLvalue(Action<TargetWriter> obj, string name) {
        this.Object = obj;
        this.Getter = $"get_{name}";
        this.Setter = $"set_{name}";
      }

      public GetterSetterLvalue(Action<TargetWriter> obj, string getter, string/*?*/ setter) {
        this.Object = obj;
        this.Getter = getter;
        this.Setter = setter;
      }

      public void EmitRead(TargetWriter wr) {
        Object(wr);
        wr.Write($".{Getter}()");
      }

      public TargetWriter EmitWrite(TargetWriter wr) {
        Contract.Assert(Setter != null, "Unexpected write to read-only property");

        Object(wr);
        wr.Write($".{Setter}(");
        var w = wr.Fork();
        wr.WriteLine(");");
        return w;
      }
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, TargetWriter wr){
      wr.Write($"{source}.is_{ctor.CompileName}()");
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl member){
      if (type is UserDefinedType udt && udt.ResolvedClass is TraitDecl) {
        return TypeName_UDT(udt.FullCompanionCompileName, udt.TypeArgs, wr, tok);
      } else {
        return TypeName(type, wr, tok, member);
      }
    }

    protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      List<TargetWriter> wIndices;
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

    protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      List<TargetWriter> wIndices;
      var w = EmitArraySelect(indices.Count, out wIndices, elmtType, wr);

      for (int i = 0; i < indices.Count; i++) {
        TrParenExprAsInt(indices[i], wIndices[i], inLetExprBody);
      }

      return w;
    }

    private TargetWriter EmitArraySelect(int dimCount, out List<TargetWriter> wIndices, Type elmtType, TargetWriter wr) {
      wIndices = new List<TargetWriter>();
      TargetWriter w;
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
          wr.Write($"(({TypeName(elmtType, wr, Bpl.Token.NoToken)}{Util.Repeat("[]", dimCount)}) ((");
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

    // TODO: Generalize the EmitArraySelectAsLvalue API to be rid of this duplication
    protected override TargetWriter EmitArrayUpdate(List<string> indices, string rhs, Type elmtType, TargetWriter wr) {
      TargetWriter w;
      if (indices.Count == 1) {
        if (elmtType.IsTypeParameter) {
          wr.Write($"{FormatTypeDescriptorVariable(elmtType.AsTypeParameter)}.setArrayElement(");
          w = wr.Fork();
          wr.Write($", {DafnyHelpersClass}.toInt({indices[0]}), {rhs})");
        } else {
          w = wr.Fork();
          wr.Write($"[{DafnyHelpersClass}.toInt({indices[0]})] = {rhs}");
        }
      } else {
        if (elmtType.IsTypeParameter) {
          w = wr.Fork();
          wr.Write($".set({Util.Comma(indices, ix => $"{DafnyHelpersClass}.toInt({ix})")}, {rhs})");
        } else {
          wr.Write($"(({TypeName(elmtType, wr, Bpl.Token.NoToken)}{Util.Repeat("[]", indices.Count)}) (");
          w = wr.Fork();
          wr.Write($").elmts){Util.Comma("", indices, ix => $"[{DafnyHelpersClass}.toInt({ix})]")} = {rhs}");
        }
      }
      return w;
    }

    protected override ILvalue EmitArraySelectAsLvalue(string array, List<string> indices, Type elmtType) {
      if (elmtType.IsTypeParameter) {
        return new GenericArrayElementLvalue(this, array, indices, elmtType.AsTypeParameter);
      } else {
        return SimpleLvalue(wr => {
          var wArray = EmitArraySelect(indices, elmtType, wr);
          wArray.Write(array);
        });
      }
    }

    private class GenericArrayElementLvalue : ILvalue {
      private readonly JavaCompiler Compiler;
      private readonly string Array;
      private readonly List<string> Indices;
      private readonly TypeParameter ElmtTypeParameter;

      public GenericArrayElementLvalue(JavaCompiler compiler, string array, List<string> indices, TypeParameter elmtTypeParameter) {
        Compiler = compiler;
        Array = array;
        Indices = indices;
        ElmtTypeParameter = elmtTypeParameter;
      }

      public void EmitRead(TargetWriter wr) {
        var wArray = Compiler.EmitArraySelect(Indices, new UserDefinedType(ElmtTypeParameter), wr);
        wArray.Write(Array);
      }

      public TargetWriter EmitWrite(TargetWriter wr) {
        TargetWriter w;
        if (Indices.Count == 1) {
          wr.Write($"{FormatTypeDescriptorVariable(ElmtTypeParameter)}.setArrayElement({Array}, {Indices[0]}.intValue(),");
          w = wr.Fork();
          wr.Write(")");
        } else {
          wr.Write($"{Array}.set({Util.Comma("", Indices, ix => $"[{DafnyHelpersClass}.toInt({ix})]")}), ");
          w = wr.Fork();
          wr.Write(")");
        }
        return w;
      }
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      if (fromArray) {
        wr.Write($"{DafnySeqClass}.fromRawArrayRange({TypeDescriptor(source.Type.TypeArgs[0], wr, source.tok)}, ");
      }
      TrParenExpr(source, wr, inLetExprBody);
      if (fromArray) {
        wr.Write(", ");
        if (lo != null) {
          TrExprAsInt(lo, wr, inLetExprBody);
        } else {
          wr.Write("0");
        }
        wr.Write(", ");
        if (hi != null) {
          TrExprAsInt(hi, wr, inLetExprBody);
        } else {
          wr.Write("java.lang.reflect.Array.getLength");
          TrParenExpr(source, wr, inLetExprBody);
        }
        wr.Write(")");
      } else {
        if (lo != null && hi != null) {
          wr.Write(".subsequence(");
          TrExprAsInt(lo, wr, inLetExprBody);
          wr.Write(", ");
          TrExprAsInt(hi, wr, inLetExprBody);
          wr.Write(")");
        }
        else if (lo != null) {
          wr.Write(".drop");
          TrParenExpr(lo, wr, inLetExprBody);
        }
        else if (hi != null) {
          wr.Write(".take");
          TrParenExpr(hi, wr, inLetExprBody);
        }
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
      // Taken from C# compiler, assuming source is a DafnySequence type.
      TrParenExpr(source, wr, inLetExprBody);
      if (source.Type.AsCollectionType is MultiSetType){
        TrParenExpr(".multiplicity", index, wr, inLetExprBody);
      } else if (source.Type.AsCollectionType is MapType){
        TrParenExpr(".get", index, wr, inLetExprBody);
      } else {
        TrParenExpr(".select", index, wr, inLetExprBody);
      }

    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(expr.E, wr, inLetExprBody);
      wr.Write(".asDafnyMultiset()");
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value, bool inLetExprBody,
      TargetWriter wr, bool nativeIndex = false) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write(".update(");
      TrExpr(index, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
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
      EmitShift(e0, e1, isRotateLeft ? leftShift : rightShift, isRotateLeft, nativeType, true, wr, inLetExprBody, tr);
      wr.Write(")");
      if (nativeType == null) {
        wr.Write (".or");
      } else {
        wr.Write ("|");
      }
      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? rightShift : leftShift, !isRotateLeft, nativeType, false, wr, inLetExprBody, tr);
      wr.Write(")))");
      if (needsCast) {
        wr.Write("))");
      }
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, NativeType/*?*/ nativeType, bool firstOp, TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }
      tr(e0, wr, inLetExprBody);
      wr.Write($" {op} ");
      if (!firstOp) {
        wr.Write($"({bv.Width} - ");
      }
      wr.Write("((");
      tr(e1, wr, inLetExprBody);
      wr.Write(")");
      if (AsNativeType(e1.Type) == null) {
        wr.Write(".intValue()");
      }
      if (!firstOp) {
        wr.Write(")");
      }
    }

    protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, TargetWriter wr) {
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

    protected override TargetWriter EmitSign(Type type, TargetWriter wr) {
      TargetWriter w;
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

    protected override IClassWriter/*?*/ DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
      if (dt is TupleTypeDecl){
        tuples.Add(((TupleTypeDecl) dt).Dims);
        return null;
      } else {
        var w = CompileDatatypeBase(dt, wr);
        CompileDatatypeConstructors(dt, wr);
        return w;
      }
    }

    IClassWriter CompileDatatypeBase(DatatypeDecl dt, TargetWriter wr) {
      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);
      string DtT_TypeArgs = "";
      if (dt.TypeArgs.Count != 0) {
        DtT_TypeArgs = "<" + TypeParameters(dt.TypeArgs) + ">";
        DtT += DtT_TypeArgs;
        DtT_protected += DtT_TypeArgs;
      }
      var filename = $"{ModulePath}/{dt}.java";
      wr = wr.NewFile(filename);
      FileCount += 1;
      wr.WriteLine($"// Class {DtT_protected}");
      wr.WriteLine($"// Dafny class {DtT_protected} compiled into Java");
      wr.WriteLine($"package {ModuleName};");
      wr.WriteLine();
      EmitImports(wr, out _);
      wr.WriteLine();
      // from here on, write everything into the new block created here:
      //TODO: Figure out how to resolve type checking warnings
      EmitSuppression(wr);
      var btw = wr.NewNamedBlock("public{0} class {1}", dt.IsRecordType ? "" : " abstract", DtT_protected);
      wr = btw;
      // constructor
      if (dt.IsRecordType) {
        DatatypeFieldsAndConstructor(dt.Ctors[0], 0, wr);
      } else {
        wr.WriteLine($"public {IdName(dt)}() {{ }}");
      }
      var typeArgsStr = Util.Comma(dt.TypeArgs, IdName);
      var usedTypeArgs = UsedTypeParameters(dt);
      var usedTypeArgsStr = Util.Comma(usedTypeArgs, IdName);
      var typeDescArgsStr = Util.Comma(usedTypeArgs, FormatTypeDescriptorVariable);
      TargetWriter wDefault;
      if (dt.TypeArgs.Count == 0) {
        wr.Write($"static {IdName(dt)} theDefault = ");
        wDefault = wr.Fork();
        wr.WriteLine(";");

        using (var w = wr.NewNamedBlock($"public static {IdName(dt)} Default()")) {
          w.WriteLine("return theDefault;");
        }
      } else {
        var w = wr.NewBigBlock($"public static <{typeArgsStr}> {dt}<{typeArgsStr}> Default({Util.Comma(usedTypeArgs, tp => $"{TypeClass}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)}")})", "");
        w.Write("return ");
        wDefault = w.Fork();
        w.WriteLine(";");
      }
      DatatypeCtor defaultCtor;
      if (dt is IndDatatypeDecl) {
        defaultCtor = ((IndDatatypeDecl)dt).DefaultCtor;
      } else {
        defaultCtor = ((CoDatatypeDecl) dt).Ctors[0];
      }
      string arguments = "";
      string sep = "";
      foreach (Formal f in defaultCtor.Formals) {
        if (!f.IsGhost) {
          arguments += sep + DefaultValue(f.Type, wDefault, f.Tok);
          sep = ", ";
        }
      }
      EmitDatatypeValue(dt, defaultCtor, dt is CoDatatypeDecl, arguments, wDefault);
      EmitTypeMethod(IdName(dt), dt.TypeArgs, usedTypeArgs, $"Default({typeDescArgsStr})", wr);
      // create methods
      // TODO:  Need to revisit this. Java cannot reference generic types in a static context, so this wont work.
      // (Yes, it can: public static <T1, T2> Foo create_Bar(T1 arg1, T2 arg2) { ... })
//      foreach (var ctor in dt.Ctors) {
//        wr.Write("public static {0} {1}(", DtT_protected, DtCreateName(ctor));
//        WriteFormals("", ctor.Formals, wr);
//        var w = wr.NewBlock(")");
//        w.Write("return new {0}(", DtCtorDeclarationName(ctor, dt.TypeArgs));
//        var sep = "";
//        var i = 0;
//        foreach (var arg in ctor.Formals) {
//          if (!arg.IsGhost) {
//            w.Write("{0}{1}", sep, FormalName(arg, i));
//            sep = ", ";
//            i++;
//          }
//        }
//        w.WriteLine(");");
//      }
      // query properties
      foreach (var ctor in dt.Ctors) {
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
          w.WriteLine("{0}.add(new {1}{2}());", arraylist, DtT_protected, dt.IsRecordType ? "" : $"_{ctor.CompileName}");
        }
        w.WriteLine($"return {arraylist};");
      }
      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors) {
          if (dtor.EnclosingCtors[0] == ctor) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName){
              using (var wDtor = wr.NewNamedBlock($"public {TypeName(arg.Type, wr, arg.tok)} dtor_{arg.CompileName}()")){
                if (dt.IsRecordType){
                  wDtor.WriteLine($"return this.{IdName(arg)};");
                }
                else{
                  wDtor.WriteLine("{0} d = this{1};", DtT_protected, dt is CoDatatypeDecl ? ".Get()" : "");
                  var n = dtor.EnclosingCtors.Count;
                  for (int i = 0; i < n-1; i++) {
                    var ctor_i = dtor.EnclosingCtors[i];
                    Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                    wDtor.WriteLine("if (d instanceof {0}_{1}{2}) {{ return (({0}_{1}{2})d).{3}; }}", dt.CompileName, ctor_i.CompileName, DtT_TypeArgs, IdName(arg));
                  }
                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[n-1].CompileName);
                  wDtor.WriteLine($"return (({dt.CompileName}_{dtor.EnclosingCtors[n-1].CompileName}{DtT_TypeArgs})d).{IdName(arg)};");
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

    void CompileDatatypeConstructors(DatatypeDecl dt, TargetWriter wrx) {
      Contract.Requires(dt != null);
      string typeParams = dt.TypeArgs.Count == 0 ? "" : $"<{TypeParameters(dt.TypeArgs)}>";
      if (dt.IsRecordType) {
        // There is only one constructor, and it is populated by CompileDatatypeBase
        return;
      }
      int constructorIndex = 0; // used to give each constructor a different name
      foreach (DatatypeCtor ctor in dt.Ctors) {
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
        w.WriteLine($"interface Computer {{ {dt.CompileName} run(); }}");
        w.WriteLine("Computer c;");
        w.WriteLine($"{dt.CompileName}{typeParams} d;");
        w.WriteLine($"public {dt.CompileName}__Lazy(Computer c) {{ this.c = c; }}");
        w.WriteLine($"public {dt.CompileName}{typeParams} Get() {{ if (c != null) {{ d = c.run(); c = null; }} return d; }}");
        w.WriteLine("public String toString() { return Get().toString(); }");
      }
    }

    void DatatypeFieldsAndConstructor(DatatypeCtor ctor, int constructorIndex, TargetWriter wr) {
      Contract.Requires(ctor != null);
      Contract.Requires(0 <= constructorIndex && constructorIndex < ctor.EnclosingDatatype.Ctors.Count);
      Contract.Requires(wr != null);
      var dt = ctor.EnclosingDatatype;
      var i = 0;
      foreach (Formal arg in ctor.Formals) {
        if (!arg.IsGhost) {
          wr.WriteLine($"public {TypeName(arg.Type, wr, arg.tok)} {FormalName(arg, i)};");
          i++;
        }
      }
      wr.Write($"public {DtCtorDeclarationName(ctor)}(");
      WriteFormals("", ctor.Formals, wr);
      using (var w = wr.NewBlock(")")) {
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            w.WriteLine($"this.{FormalName(arg, i)} = {FormalName(arg, i)};");
            i++;
          }
        }
      }
      if (ctor.Formals.Count > 0){
        wr.Write($"public {DtCtorDeclarationName(ctor)}(){{}}");
      }
      if (dt is CoDatatypeDecl) {
        string typeParams = dt.TypeArgs.Count == 0 ? "" : $"<{TypeParameters(dt.TypeArgs)}>";
        wr.WriteLine($"public {dt.CompileName}{typeParams} Get() {{ return this; }}");
      }
      // Equals method
      using (var w = wr.NewBlock("\n@Override\npublic boolean equals(Object other)")) {
        w.WriteLine("if (this == other) return true;");
        w.WriteLine("if (other == null) return false;");
        w.WriteLine("if (getClass() != other.getClass()) return false;");
        if(ctor.Formals.Count > 0){string typeParams = dt.TypeArgs.Count == 0 ? "" : $"<{TypeParameters(dt.TypeArgs)}>";
          w.WriteLine("{0} o = ({0})other;", DtCtorDeclarationName(ctor, dt.TypeArgs));
          w.Write("return ");
          i = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              string nm = FormalName(arg, i);
              if(i!= 0)
                w.Write(" && ");
              if (IsDirectlyComparable(arg.Type)) {
                w.Write($"this.{nm} == o.{nm}");
              } else {
                w.Write($"{nm}.equals(o.{nm})");
              }
              i++;
            }
          }
          w.WriteLine(";");
        } else {
          w.WriteLine("return true;");
        }
      }
      // GetHashCode method (Uses the djb2 algorithm)
      using (var w = wr.NewBlock("\n@Override\npublic int hashCode()")) {
        w.WriteLine("long hash = 5381;");
        w.WriteLine($"hash = ((hash << 5) + hash) + {constructorIndex};");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            w.Write("hash = ((hash << 5) + hash) + ");
            if (IsJavaPrimitiveType(arg.Type)) {
              w.WriteLine($"{BoxedTypeName(arg.Type, w, Bpl.Token.NoToken)}.hashCode(this.{nm});");
            } else {
              w.WriteLine($"this.{nm}.hashCode();");
            }
            i++;
          }
        }
        w.WriteLine("return (int) hash;");
      }
      using (var w = wr.NewBlock("\n@Override\npublic String toString()")) {
        string nm;
        if (dt is TupleTypeDecl) {
          nm = "";
        } else {
          nm = (dt.Module.IsDefaultModule ? "" : dt.Module.Name + ".") + dt.Name + "." + ctor.Name;
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
                var memberName = FormalName(arg, i);
                if (IsJavaPrimitiveType(arg.Type)) {
                  w.Write($"this.{memberName}");
                } else {
                  w.Write($"this.{memberName} == null ? \"\" : this.{memberName}");
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

    string DtCtorDeclarationName(DatatypeCtor ctor, List<TypeParameter> typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorDeclarationName(ctor);
      if (typeParams != null && typeParams.Count != 0) {
        s += "<" + TypeParameters(typeParams) + ">";
      }
      return s;
    }
    string DtCtorDeclarationName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
      return dt.IsRecordType ? IdName(dt) : dt.CompileName + "_" + ctor.CompileName;
    }
    string DtCtorName(DatatypeCtor ctor, List<Type> typeArgs, TextWriter wr) {
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
        return DafnyTupleClass(tupleDecl.TypeArgs.Count);
      }
      var dtName = IdProtect(dt.CompileName);
      return dt.IsRecordType ? dtName : dtName + "_" + ctor.CompileName;
    }
    string DtCreateName(DatatypeCtor ctor) {
      if (ctor.EnclosingDatatype.IsRecordType) {
        return "create";
      }
      return "create_" + ctor.CompileName;
    }

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Write("System.out.print(");
      EmitToString(wr, arg);
      wr.WriteLine(");");
    }

    protected void EmitToString(TargetWriter wr, Expression arg) {
      if (arg.Type.IsArrowType) {
        wr.Write(IdName(((IdentifierExpr) ((ConcreteSyntaxExpression)arg).ResolvedExpression).Var) + " == null ? null : \"Function\"");
      } else if (AsNativeType(arg.Type) != null && AsNativeType(arg.Type).LowerBound >= 0) {
        var nativeName = GetNativeTypeName(AsNativeType(arg.Type));
        switch (AsNativeType(arg.Type).Sel) {
          case NativeType.Selection.Byte:
            wr.Write("Integer.toUnsignedString(Byte.toUnsignedInt(");
            TrExpr(arg, wr, false);
            wr.Write("))");
            break;
          case NativeType.Selection.UShort:
            wr.Write("Integer.toUnsignedString(Short.toUnsignedInt(");
            TrExpr(arg, wr, false);
            wr.Write("))");
            break;
          case NativeType.Selection.UInt:
            wr.Write("Integer.toUnsignedString(");
            TrExpr(arg, wr, false);
            wr.Write(")");
            break;
          case NativeType.Selection.ULong:
            wr.Write("Long.toUnsignedString(");
            TrExpr(arg, wr, false);
            wr.Write(")");
            break;
          default:
            // Should be an unsigned type by assumption
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      } else {
        // TODO-RS: This doesn't handle strings printed out as part of datatypes
        bool isString = arg.Type.AsCollectionType != null &&
                        arg.Type.AsCollectionType.AsSeqType != null &&
                        arg.Type.AsCollectionType.AsSeqType.Arg is CharType;
        if (!isString) {
          wr.Write("String.valueOf(");
        }
        TrExpr(arg, wr, false);
        if (isString) {
          wr.Write(".verbatimString()");
        } else {
          wr.Write(")");
        }
      }
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public static string PublicIdProtect(string name) {
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
        case "protected":
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
          return name + "_"; // TODO: figure out what to do here (C# uses @, Go uses _, JS uses _$$_)
        default:
          return name; // Package name is not a keyword, so it can be used
      }
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain, string /*?*/ targetFilename,
      ReadOnlyCollection<string> otherFileNames, bool hasMain, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
      compilationResult = null;
      foreach (var otherFileName in otherFileNames) {
        if (Path.GetExtension(otherFileName) != ".java") {
          outputWriter.WriteLine($"Unrecognized file as extra input for Java compilation: {otherFileName}");
          return false;
        }
        if (!CopyExternLibraryIntoPlace(mainProgram: targetFilename, externFilename: otherFileName, outputWriter: outputWriter)) {
          return false;
        }
      }
      var files = new List<string>();
      foreach (string file in Directory.EnumerateFiles(Path.GetDirectoryName(targetFilename), "*.java", SearchOption.AllDirectories)) {
        files.Add($"\"{Path.GetFullPath(file)}\"");
      }
      var classpath = GetClassPath(targetFilename);
      var psi = new ProcessStartInfo("javac", string.Join(" ", files)) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        WorkingDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename))
      };
      psi.EnvironmentVariables["CLASSPATH"] = classpath;
      var proc = Process.Start(psi);
      while (!proc.StandardOutput.EndOfStream) {
        outputWriter.WriteLine(proc.StandardOutput.ReadLine());
      }
      while (!proc.StandardError.EndOfStream) {
        outputWriter.WriteLine(proc.StandardError.ReadLine());
      }
      proc.WaitForExit();
      if (proc.ExitCode != 0) {
        throw new Exception($"Error while compiling Java files. Process exited with exit code {proc.ExitCode}");
      }
      return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string /*?*/ targetFilename,
     ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {
      var psi = new ProcessStartInfo("java", Path.GetFileNameWithoutExtension(targetFilename)) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        WorkingDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename))
      };
      psi.EnvironmentVariables["CLASSPATH"] = GetClassPath(targetFilename);
      var proc = Process.Start(psi);
      while (!proc.StandardOutput.EndOfStream) {
        outputWriter.WriteLine(proc.StandardOutput.ReadLine());
      }
      while (!proc.StandardError.EndOfStream) {
        outputWriter.WriteLine(proc.StandardError.ReadLine());
      }
      proc.WaitForExit();
      if (proc.ExitCode != 0) {
        throw new Exception($"Error while running Java file {targetFilename}. Process exited with exit code {proc.ExitCode}");
      }
      return true;
    }

    protected string GetClassPath(string targetFilename) {
      var assemblyLocation = Assembly.GetExecutingAssembly().Location;
      Contract.Assert(assemblyLocation != null);
      var codebase = Path.GetDirectoryName(assemblyLocation);
      Contract.Assert(codebase != null);
      // DafnyRuntime-1.jar has already been created using Maven. It is added to the java CLASSPATH below.
      return "." + Path.PathSeparator + Path.GetFullPath(Path.GetDirectoryName(targetFilename)) + Path.PathSeparator + Path.Combine(codebase, "DafnyRuntime-1.jar");
    }

    static bool CopyExternLibraryIntoPlace(string externFilename, string mainProgram, TextWriter outputWriter) {
      // Grossly, we need to look in the file to figure out where to put it
      var pkgName = FindPackageName(externFilename);
      if (pkgName == null) {
        outputWriter.WriteLine($"Unable to determine package name: {externFilename}");
        return false;
      }
      string baseName = Path.GetFileNameWithoutExtension(externFilename);
      var mainDir = Path.GetDirectoryName(mainProgram);
      Contract.Assert(mainDir != null);
      var tgtDir = Path.Combine(mainDir, pkgName);
      var tgtFilename = Path.Combine(tgtDir, baseName + ".java");
      Directory.CreateDirectory(tgtDir);
      FileInfo file = new FileInfo(externFilename);
      file.CopyTo(tgtFilename, true);
      if (DafnyOptions.O.CompileVerbose) {
        outputWriter.WriteLine($"Additional input {externFilename} copied to {tgtFilename}");
      }
      return true;
    }

    private static string FindPackageName(string externFilename){
      using (var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read))){
        while (rd.ReadLine() is string line){
          var match = PackageLine.Match(line);
          if (match.Success){
            return match.Groups[1].Value;
          }
        }
        return null;
      }
    }

    protected override void EmitReturn(List<Formal> outParams, TargetWriter wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      if (outParams.Count == 0){
        wr.WriteLine("return;");
      } else if (outParams.Count == 1){
        wr.WriteLine($"return {IdName(outParams[0])};");
      } else {
        tuples.Add(outParams.Count);
        wr.WriteLine($"return new {DafnyTupleClass(outParams.Count)}<>({Util.Comma(outParams, IdName)});");
      }
    }

    private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*;$");

    // TODO: See if more types need to be added
    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || t.IsRefType || AsJavaNativeType(t) != null;
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr)
    {
      // Todo: see if there is ever a time in java where this is necessary
//      if (typeArgs.Count != 0) {
//        wr.Write("<" + TypeNames(typeArgs, wr, tok) + ">");
//      }
    }

    protected override string GenerateLhsDecl(string target, Type type, TextWriter wr, Bpl.IToken tok){
      return TypeName(type, wr, tok) + " " + target;
    }

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt initCall, TargetWriter wr){
      var ctor = (Constructor) initCall?.Method; // correctness of cast follows from precondition of "EmitNew"
      wr.Write($"new {TypeName(type, wr, tok)}(");
      if (type is UserDefinedType definedType) {
        EmitRuntimeTypeDescriptors(definedType.ResolvedClass.TypeArgs, definedType.TypeArgs, useAll: true, tok, wr);
      }
      if (ctor != null && ctor.IsExtern(out _, out _)) {
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


    private void EmitRuntimeTypeDescriptors(List<TypeParameter> typeParams, List<Type> typeArgs, bool useAll, Bpl.IToken tok, TargetWriter wr) {
      Contract.Assert(typeParams.Count == typeArgs.Count);

      var sep = "";
      for (var i = 0; i < typeParams.Count; i++) {
        var tp = typeParams[i];
        var actual = typeArgs[i];

        if (useAll || tp.Characteristics.MustSupportZeroInitialization) {
          wr.Write(sep);
          wr.Write(TypeDescriptor(actual, wr, tok));
          sep = ", ";
        }
      }
    }

    private string TypeDescriptor(Type type, TextWriter wr, Bpl.IToken tok) {
      type = type.NormalizeExpand();
      if (type is BoolType) {
        return $"{TypeClass}.BOOLEAN";
      } else if (type is CharType) {
        return $"{TypeClass}.CHAR";
      } else if (type is IntType || type is BigOrdinalType) {
        return $"{TypeClass}.BIG_INTEGER";
      } else if (type is RealType) {
        return $"{TypeClass}.BIG_RATIONAL";
      } else if (AsNativeType(type) != null) {
        return GetNativeTypeDescriptor(AsNativeType(type));
      } else if (type is BitvectorType bvt) {
        // already checked if it has a native type
        return $"{TypeClass}.BIG_INTEGER";
      } else if (type.AsNewtype != null) {
        // already checked if it has a native type
        return TypeDescriptor(type.AsNewtype.BaseType, wr, tok);
      } else if (type.IsObjectQ) {
        return $"{TypeClass}.OBJECT";
      } else if (type.IsArrayType) {
        ArrayClassDecl at = type.AsArrayType;
        var elType = UserDefinedType.ArrayElementType(type);
        var elTypeName = TypeName(elType, wr, tok);
        if (at.Dims > 1) {
          arrays.Add(at.Dims);
          return $"{DafnyMultiArrayClass(at.Dims)}.<{elTypeName}>{TypeMethodName}()";
        } else if (elType is BoolType) {
          return $"{TypeClass}.BOOLEAN_ARRAY";
        } else if (elType is CharType) {
          return $"{TypeClass}.CHAR_ARRAY";
        } else if (AsNativeType(type) != null) {
          switch (AsJavaNativeType(type)) {
            case JavaNativeType.Byte: return $"{TypeClass}.BYTE_ARRAY";
            case JavaNativeType.Short: return $"{TypeClass}.SHORT_ARRAY";
            case JavaNativeType.Int: return $"{TypeClass}.INT_ARRAY";
            case JavaNativeType.Long: return $"{TypeClass}.LONG_ARRAY";
            default:
              Contract.Assert(false);
              throw new cce.UnreachableException();
          }
        } else {
          return $"({TypeDescriptor(elType, wr, tok)}).arrayType()";
        }
      } else if (type.IsTypeParameter) {
        return FormatTypeDescriptorVariable(type.AsTypeParameter.CompileName);
      } else if (type is ArrowType arrowType && arrowType.Arity == 1) {
        // Can't go the usual route because java.util.function.Function doesn't have a _type() method
        return $"{TypeClass}.function({TypeDescriptor(arrowType.Args[0], wr, tok)}, {TypeDescriptor(arrowType.Result, wr, tok)})";
      } else if (type is UserDefinedType udt) {
        var s = FullTypeName(udt);
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return $"{TypeClass}.LONG";
        } else if (cl is TupleTypeDecl tupleDecl) {
          s = $"{DafnyTupleClass(tupleDecl.TypeArgs.Count)}";
        } else if (DafnyOptions.O.IronDafny &&
                 !(type is ArrowType) &&
                 cl != null &&
                 cl.Module != null &&
                 !cl.Module.IsDefaultModule){
          s = cl.FullCompileName;
        }

        if (cl.IsExtern(out _, out _)) {
          var td = $"{TypeClass}.<{TypeName(type, wr, tok)}> findType({s}.class";
          if (udt.TypeArgs != null && udt.TypeArgs.Count > 0) {
            td += $", {Util.Comma(udt.TypeArgs, arg => TypeDescriptor(arg, wr, tok))}";
          }
          return td + ")";
        }

        List<Type> relevantTypeArgs;
        if (type is ArrowType) {
          relevantTypeArgs = type.TypeArgs;
        } else if (cl is TupleTypeDecl) {
          relevantTypeArgs = new List<Type>();
        } else if (cl is DatatypeDecl dt) {
          UsedTypeParameters(dt, udt.TypeArgs, out _, out relevantTypeArgs);
        } else {
          relevantTypeArgs = new List<Type>();
          for (int i = 0; i < cl.TypeArgs.Count; i++) {
            if (cl.TypeArgs[i].Characteristics.MustSupportZeroInitialization) {
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
        case JavaNativeType.Byte: return $"{TypeClass}.BYTE";
        case JavaNativeType.Short: return $"{TypeClass}.SHORT";
        case JavaNativeType.Int: return $"{TypeClass}.INT";
        case JavaNativeType.Long: return $"{TypeClass}.LONG";
        default: Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private string AddTypeDescriptorArgs(string fullCompileName, List<Type> typeArgs, List<Type> relevantTypeArgs, TextWriter wr, Bpl.IToken tok) {
      string s = $"{IdProtect(fullCompileName)}.";
      if (typeArgs != null && typeArgs.Count != 0) {
        s += $"<{BoxedTypeNames(typeArgs, wr, tok)}>";
      }
      s += $"{TypeMethodName}(";
      s += Util.Comma(relevantTypeArgs, arg => TypeDescriptor(arg, wr, tok));
      return s + ")";
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization){
          wr.Write($"{prefix}{TypeClass}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)}");
          prefix = ", ";
          c++;
        }
      }
      return c;
    }

    int WriteRuntimeTypeDescriptorsFormals(Method m, List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization || OutContainsParam(m.Outs, tp)){
          wr.Write($"{prefix}{TypeClass}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)}");
          prefix = ", ";
          c++;
        }
      }
      return c;
    }

    bool OutContainsParam(List<Formal> l, TypeParameter tp){
      foreach (Formal f in l){
        if (f.Type.IsTypeParameter && f.Type.AsTypeParameter.Equals(tp) || f.Type.AsCollectionType != null && f.Type.AsCollectionType.Arg.IsTypeParameter && f.Type.AsCollectionType.Arg.AsTypeParameter.Equals(tp)){
          return true;
        }
      }
      return false;
    }

    protected override void EmitSetComprehension(TargetWriter wr, Expression expr, String collection_name){
      var e = (SetComprehension) expr;
      wr.Write($"java.util.ArrayList<{BoxedTypeName(((SetType)expr.Type).Arg, wr, null)}> {collection_name} = ");
      EmitCollectionBuilder_New(e.Type.AsSetType, e.tok, wr);
      wr.WriteLine(";");
    }

    protected override void OrganizeModules(Program program, out List<ModuleDefinition> modules){
      modules = new List<ModuleDefinition>();
      foreach (var m in program.CompileModules){
        if (!m.IsDefaultModule && !m.Name.Equals("_System")){
          modules.Add(m);
        }
      }
      foreach (var m in program.CompileModules){
        if (m.Name.Equals("_System")){
          modules.Add(m);
        }
      }
      foreach (var m in program.CompileModules){
        if (m.IsDefaultModule){
          modules.Add(m);
        }
      }
    }

    protected override void EmitAssignment(out TargetWriter wLhs, Type /*?*/ lhsType, out TargetWriter wRhs, Type /*?*/ rhsType, TargetWriter wr) {
      wLhs = wr.Fork();
      wr.Write(" = ");
      TargetWriter w;
      w = rhsType != null ? EmitCoercionIfNecessary(@from: rhsType, to: lhsType, tok: Bpl.Token.NoToken, wr: wr) : wr;
      wRhs = w.Fork();
      EndStmt(wr);
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      EmitDatatypeValue(dt, dtv.Ctor, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string arguments, TargetWriter wr) {
      var dtName = dt is TupleTypeDecl tupleDecl ? DafnyTupleClass(tupleDecl.TypeArgs.Count) : dt.CompileName;
      var ctorName = ctor.CompileName;
      var typeParams = dt.TypeArgs.Count == 0 ? "" : "<>";
      //TODO: Determine if this implementation is ever needed
//      var typeDecl = dtv.InferredTypeArgs.Count == 0
//        ? ""
//        : string.Format("new {0}", TypeNames(dtv.InferredTypeArgs, wr, dtv.tok));
      if (!isCoCall) {
        wr.Write("new {0}{1}{2}", dtName, dt.IsRecordType ? "" : "_" + ctorName, typeParams);
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   new Dt_Cons<T>( args )
        if (arguments != null && !arguments.Equals("")){
          wr.Write($"({arguments})");
        } else {
          wr.Write("()");
        }
      } else {
        wr.Write($"new {dt.CompileName}__Lazy(");
        wr.Write("() -> { return ");
        wr.Write($"new {DtCtorName(ctor)}({arguments})");
        wr.Write("; })");
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false) {
      if (inTypes.Count != 1) {
        functions.Add(inTypes.Count);
      }
      wr.Write('(');
      if (!untyped) {
        wr.Write("({0}<{1}{2}>)", DafnyFunctionIface(inTypes.Count), Util.Comma("", inTypes, t => BoxedTypeName(t, wr, tok) + ", "), BoxedTypeName(resultType, wr, tok));
      }
      wr.Write($"({Util.Comma(inNames, nm => nm)}) ->");
      var w = wr.NewExprBlock("");
      wr.Write(")");
      return w;
    }

    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      functions.Add(0);
      wr.Write($"(({DafnyFunctionIface(0)}<{BoxedTypeName(resultType, wr, resultTok)}>)(() ->");
      var w = wr.NewBigExprBlock("", ")).apply()");
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          if (AsNativeType(expr.Type) != null) {
            TrParenExpr(CastIfSmallNativeType(expr.Type) + "~", expr, wr, inLetExprBody);
          } else {
            TrParenExpr("", expr, wr, inLetExprBody);
            wr.Write(".not()");
          }
          break;
        case ResolvedUnaryOp.Cardinality:
          if (expr.Type.AsCollectionType is MultiSetType) {
            TrParenExpr("", expr, wr, inLetExprBody);
            wr.Write(".cardinality()");
          } else if (expr.Type.AsCollectionType is SetType || expr.Type.AsCollectionType is MapType) {
            TrParenExpr("java.math.BigInteger.valueOf(", expr, wr, inLetExprBody);
            wr.Write(".size())");
          } else if (expr.Type.IsArrayType) {
            TrParenExpr("java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength", expr, wr, inLetExprBody);
            wr.Write(")");
          } else {
            TrParenExpr("java.math.BigInteger.valueOf(", expr, wr, inLetExprBody);
            wr.Write(".length())");
          }
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
    }

    // Find the class with static methods like "divideUnsigned" for the type
    private string HelperClass(NativeType nt) {
      return AsJavaNativeType(nt) == JavaNativeType.Long ? "Long" : "Integer";
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op, Expression e0, Expression e1, Bpl.IToken tok,
      Type resultType, out string opString,
      out string preOpString, out string postOpString, out string callString, out string staticCallString,
      out bool reverseArguments, out bool truncateResult, out bool convertE1_to_int, TextWriter errorWr){
      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

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

      switch (op){
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "==";
          break;
        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "!";
          opString = "||";
          break;
        case BinaryExpr.ResolvedOpcode.Or:
          opString = "||";
          break;
        case BinaryExpr.ResolvedOpcode.And:
          opString = "&&";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          doPossiblyNativeBinOp("&", "and", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          doPossiblyNativeBinOp("|", "or", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          doPossiblyNativeBinOp("^", "xor", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.EqCommon:{
          if (IsHandleComparison(tok, e0, e1, errorWr)) {
            opString = "==";
          } else if (e0.Type.IsRefType) {
            opString = "== (Object) ";
          } else if (IsDirectlyComparable(e0.Type)) {
            opString = "==";
          } else {
            callString = "equals";
          }
          break;
        }
        case BinaryExpr.ResolvedOpcode.NeqCommon:{
          if (IsHandleComparison(tok, e0, e1, errorWr)) {
            opString = "!=";
          } else if (e0.Type.IsRefType) {
            opString = "!= (Object) ";
          } else if (IsDirectlyComparable(e0.Type)) {
            opString = "!=";
          } else {
            preOpString = "!";
            callString = "equals";
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
            switch(op) {
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
            switch(op) {
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
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">=";
          break;
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">";
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
            preOpString = "(char) (";
            postOpString = ")";
            opString = "+";
          } else {
            doPossiblyNativeBinOp("+", "add", out preOpString, out opString, out postOpString, out callString);
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = "(char) (";
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
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyEuclideanClass}.EuclideanDivision" + suffix;
          } else if (AsNativeType(resultType) != null) {
            preOpString = CastIfSmallNativeType(resultType);
            staticCallString = HelperClass(AsNativeType(resultType)) + ".divideUnsigned";
          } else {
            callString = "divide";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyEuclideanClass}.EuclideanModulus" + suffix;
          } else if (AsNativeType(resultType) != null) {
            preOpString = CastIfSmallNativeType(resultType);
            staticCallString = HelperClass(AsNativeType(resultType)) + ".remainderUnsigned";
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
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
          preOpString = "!";
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
        case BinaryExpr.ResolvedOpcode.Superset:
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
          callString = "isSubsetOf";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          callString = "IsProperSubsetOf";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          callString = "disjoint";
          break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "contains";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "!";
          callString = "contains";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "union";
          break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "intersection";
          break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "difference";
          break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          callString = "isProperPrefixOf";
          break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "isPrefixOf";
          break;
        case BinaryExpr.ResolvedOpcode.Concat:
          callString = "concatenate";
          break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "contains";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "!";
          callString = "contains";
          reverseArguments = true;
          break;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected binary expression
      }
    }

    public void CompileTuples(string path){
      foreach(int i in tuples) {
        if (i == 2 || i == 3) continue; // Tuple2 and Tuple3 already exist in DafnyRuntime-1.jar, so don't remake these files.
        CreateTuple(i, path);
      }
    }

    private static void CreateTuple(int i, string path) {
      var wrTop = new TargetWriter();
      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();
      wrTop.Write("public class Tuple");
      wrTop.Write(i);
      if (i != 0) {
        wrTop.Write("<");
        for (int j = 0; j < i; j++){
          wrTop.Write("T" + j);
          if (j != i - 1)
            wrTop.Write(", ");
          else{
            wrTop.Write(">");
          }
        }
      }

      var wr = wrTop.NewBlock("");
      for (int j = 0; j < i; j++) {
        wr.WriteLine("private T" + j + " _" + j + ";");
      }
      wr.WriteLine();

      wr.Write("public Tuple" + i + "(");
      for (int j = 0; j < i; j++){
        wr.Write("T" + j + " _" + j);
        if (j != i - 1)
          wr.Write(", ");
      }
      using (var wrCtor = wr.NewBlock(")")) {
        for (int j = 0; j < i; j++) {
          wrCtor.WriteLine("this._" + j + " = _" + j + ";");
        }
      }

      wr.WriteLine($"private static final Tuple{i} DEFAULT = new Tuple{i}();");
      wr.WriteLine($"private static final {TypeClass}<Tuple{i}> TYPE = {TypeClass}.referenceWithDefault(Tuple{i}.class, DEFAULT);");
      wr.WriteLine($"public static {TypeClass}<Tuple{i}> {TypeMethodName}() {{ return TYPE; }}");
      if (i != 0) {
        wr.WriteLine();
        wr.Write("public Tuple" + i + "() {}");
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      using (var wrEquals = wr.NewBlock("public boolean equals(Object obj)")) {
        wrEquals.WriteLine("if (this == obj) return true;");
        wrEquals.WriteLine("if (obj == null) return false;");
        wrEquals.WriteLine("if (getClass() != obj.getClass()) return false;");
        wrEquals.WriteLine($"Tuple{i} o = (Tuple{i}) obj;");
        if (i != 0) {
          wrEquals.Write("return ");
          for (int j = 0; j < i; j++) {
            wrEquals.Write("this._" + j + ".equals(o._" + j + ")");
            if (j != i - 1)
              wrEquals.Write(" && ");
            else {
              wrEquals.WriteLine(";");
            }
          }
        } else {
          wrEquals.WriteLine("return true;");
        }
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      using (var wrToString = wr.NewBlock("public String toString()")) {
        wrToString.WriteLine("StringBuilder sb = new StringBuilder();");
        wrToString.WriteLine("sb.append(\"(\");");
        for (int j = 0; j < i; j++) {
          wrToString.WriteLine($"sb.append(_{j} == null ? \"\" : _{j}.toString());");
          if (j != i - 1)
            wrToString.WriteLine("sb.append(\", \");");
        }
        wrToString.WriteLine("sb.append(\")\");");
        wrToString.WriteLine("return sb.toString();");
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      using (var wrHashCode = wr.NewBlock("public int hashCode()")) {
        wrHashCode.WriteLine("// GetHashCode method (Uses the djb2 algorithm)");
        wrHashCode.WriteLine("// https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm");
        wrHashCode.WriteLine("long hash = 5381;");
        wrHashCode.WriteLine("hash = ((hash << 5) + hash) + 0;");
        for (int j = 0; j < i; j++) {
          wrHashCode.WriteLine("hash = ((hash << 5) + hash) + ((long) this._" + j + ".hashCode());");
        }
        wrHashCode.WriteLine("return (int) hash;");
      }

      for (int j = 0; j < i; j++){
        wr.WriteLine();
        wr.WriteLine("public T" + j + " dtor__" + j + "() { return this._" + j + "; }");
      }

      // Create a file to write to.
      using (StreamWriter sw = File.CreateText(path + "/Tuple" + i + ".java")) {
        sw.Write(wrTop.ToString());
      }
    }

    public override string TypeInitializationValue(Type type, TextWriter wr, Bpl.IToken tok, bool inAutoInitContext) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      } else if (xType is CharType) {
        return "'D'";
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
      if (udt.ResolvedParam != null) {
        if (inAutoInitContext && !udt.ResolvedParam.Characteristics.MustSupportZeroInitialization) {
          return "null";
        } else {
          return $"{FormatTypeDescriptorVariable(udt.ResolvedParam.CompileName)}.defaultValue()";
        }
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return FullTypeName(udt) + ".Witness";
        } else if (td.NativeType != null) {
          return GetNativeDefault(td.NativeType);
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, inAutoInitContext);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return FullTypeName(udt) + ".Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return $"(({BoxedTypeName(xType, wr, udt.tok)}) null)";
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) -> rangeDefaultValue)
            return $"(({Util.Comma(", ", udt.TypeArgs.Count - 1, i => $"{BoxedTypeName(udt.TypeArgs[i], wr, udt.tok)} x{i}")}) -> {rangeDefaultValue})";
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            string newarr = "";
            string bareArray;
            var elType = udt.TypeArgs[0];

            if (elType.IsTypeParameter) {
              bareArray =
                $"(Object{Util.Repeat("[]", arrayClass.Dims - 1)}) {TypeDescriptor(elType, wr, tok)}.newArray({Util.Comma(Enumerable.Repeat("0", arrayClass.Dims))})";
            } else {
              bareArray = $"new {TypeName(elType, wr, tok)}{Util.Repeat("[0]", arrayClass.Dims)}";
            }
            if (arrayClass.Dims > 1){
              arrays.Add(arrayClass.Dims);
              newarr += $"new {DafnyMultiArrayClass(arrayClass.Dims)}<>({TypeDescriptor(elType, wr, tok)}, ";
              for (int i = 0; i < arrayClass.Dims; i++) {
                newarr += "0, ";
              }
              newarr += $"{bareArray})";
            } else {
              newarr = bareArray;
            }
            return newarr;
          } else {
            return "null";
          }
        } else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, inAutoInitContext);
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
        if (udt.TypeArgs.Count != 0) {
          typeargs = $"<{BoxedTypeNames(udt.TypeArgs, wr, udt.tok)}>";
        }
        // In an auto-init context (like a field initializer), we may not have
        // access to all the type descriptors, so we can't construct the
        // default value, but then null is always an acceptable default in
        // such contexts (since Dafny proves the null won't be accessed).
        if (cl is TupleTypeDecl || inAutoInitContext) {
          return $"({s}{typeargs})null";
        }
        UsedTypeParameters(dt, udt.TypeArgs, out _, out var usedTypeArgs);
        return $"{s}.{typeargs}Default({Util.Comma(usedTypeArgs, ta => TypeDescriptor(ta, wr, tok))})";
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected type
      }
    }

    protected override TargetWriter DeclareLocalVar(string name, Type type, Bpl.IToken tok, TargetWriter wr) {
      wr.Write("{0} {1} = ", type != null ? TypeName(type, wr, tok) : "var", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, bool useReturnStyleOuts, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter>/*?*/ typeParameters, List<Type> superClasses, Bpl.IToken tok, TargetWriter wr) {
      var filename = $"{ModulePath}/{name}.java";
      var w = wr.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Interface {name}");
      w.WriteLine($"// Dafny trait {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      EmitImports(w, out _);
      w.WriteLine();
      EmitSuppression(w); //TODO: Fix implementations so they do not need this suppression
      var typeParamString = "";
      if (typeParameters != null && typeParameters.Count != 0) {
        typeParamString = $"<{TypeParameters(typeParameters)}>";
      }
      w.Write($"public interface {IdProtect(name)}{typeParamString}");
      if (superClasses != null) {
        string sep = " extends ";
        foreach (var trait in superClasses) {
          w.Write($"{sep}{TypeName(trait, w, tok)}");
          sep = ", ";
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
      w.Write($"public class _Companion_{name}{typeParamString}");
      var staticMemberWriter = w.NewBlock("");
      var ctorBodyWriter = staticMemberWriter.NewBlock($"public _Companion_{name}()");
      return new ClassWriter(this, instanceMemberWriter, ctorBodyWriter, staticMemberWriter);
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, TargetWriter wr){
      string dtorName;
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        dtorName = $"dtor__{dtor.Name}()";
      } else if (int.TryParse(dtor.Name, out _)) {
        dtorName = $"dtor_{dtor.Name}()";
      } else {
        dtorName = FormalName(dtor, formalNonGhostIndex);
      }
      wr.Write("(({0}){1}{2}).{3}", DtCtorName(ctor, typeArgs, wr), source, ctor.EnclosingDatatype is CoDatatypeDecl ? ".Get()" : "", dtorName);
    }

    public void CreateFunctionInterface(string path) {
      foreach(int i in functions){
        CreateLambdaFunctionInterface(i, path);
      }
    }

    public void CreateLambdaFunctionInterface(int i, string path) {
      var typeArgs = "<";
      for (int j = 0; j < i + 1; j++) {
        typeArgs += "T" + j;
        if (j != i) {
          typeArgs += ", ";
        }
      }
      typeArgs += ">";

      var wr = new TargetWriter();
      wr.WriteLine("package dafny;");
      wr.WriteLine();
      wr.WriteLine("@FunctionalInterface");
      wr.Write("public interface Function");
      wr.Write(i);
      wr.Write(typeArgs);
      var wrMembers = wr.NewBlock("");
      wrMembers.Write("public T" + i + " apply(");
      for (int j = 0; j < i; j++){
        wrMembers.Write("T" + j + " t" + j);
        if (j != i - 1)
          wrMembers.Write(", ");
      }
      wrMembers.WriteLine(");");

      EmitSuppression(wrMembers);
      wrMembers.Write($"public static {typeArgs} {TypeClass}<Function{i}{typeArgs}> {TypeMethodName}(");
      for (int j = 0; j < i + 1; j++) {
        wrMembers.Write($"{TypeClass}<T{j}> t{j}");
        if (j != i) {
          wrMembers.Write(", ");
        }
      }
      var wrTypeBody = wrMembers.NewBigBlock(")", "");
      // XXX This seems to allow non-nullable types to have null values (since
      // arrow types are allowed as "(0)"-constrained type arguments), but it's
      // consistent with other backends.
      wrTypeBody.Write($"return ({TypeClass}<Function{i}{typeArgs}>) ({TypeClass}<?>) {TypeClass}.reference(Function{i}.class);");

      using (StreamWriter sw = File.CreateText(path + "/Function" + i + ".java")) {
        sw.Write(wr.ToString());
      }
    }

    public void CompileDafnyArrays(string path) {
      foreach(int i in arrays){
        CreateDafnyArrays(i, path);
      }
    }

    public void CreateDafnyArrays(int i, string path) {
      var wrTop = new TargetWriter();
      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();

      // All brackets on the underlying "real" array type, minus the innermost
      // pair.  The innermost array must be represented as an Object since it
      // could be of primitive type.
      var outerBrackets = Util.Repeat("[]", i - 1);

      var dims = Enumerable.Range(0, i);
      var outerDims = Enumerable.Range(0, i - 1);

      var wr = wrTop.NewBlock($"public final class Array{i}<T>");

      wr.WriteLine($"public final Object{outerBrackets} elmts;");
      wr.WriteLine($"private final {TypeClass}<T> elmtType;");

      foreach (var j in dims) {
        wr.WriteLine($"public final int dim{j};");
      }

      using (var wrBody = wr.NewBlock($"public Array{i}({TypeClass}<T> elmtType, {Util.Comma(dims, j => $"int dim{j}")}, Object{outerBrackets} elmts)")) {
        wrBody.WriteLine("assert elmts.getClass().isArray();");
        wrBody.WriteLine("this.elmtType = elmtType;");
        foreach (var j in dims) {
          wrBody.WriteLine($"this.dim{j} = dim{j};");
        }
        wrBody.WriteLine("this.elmts = elmts;");
      }

      using (var wrBody = wr.NewBlock($"public T get({Util.Comma(dims, j => $"int i{j}")})")) {
        wrBody.Write("return elmtType.getArrayElement(elmts");
        foreach (var j in outerDims) {
          wrBody.Write($"[i{j}]");
        }
        wrBody.WriteLine($", i{i-1});");
      }

      using (var wrBody = wr.NewBlock($"public void set({Util.Comma(dims, j => $"int i{j}")}, T value)")) {
        wrBody.Write("elmtType.setArrayElement(elmts");
        foreach (var j in outerDims) {
          wrBody.Write($"[i{j}]");
        }
        wrBody.WriteLine($", i{i-1}, value);");
      }

      using (var body = wr.NewBlock("public void fill(T z)")) {
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

      using (var body = wr.NewBlock($"public Array{i} fillThenReturn(T z)")) {
        body.WriteLine("fill(z);");
        body.WriteLine("return this;");
      }

      EmitSuppression(wr);
      wr.WriteLine($"private static final {TypeClass}<Array{i}<?>> TYPE = ({TypeClass}<Array{i}<?>>) ({TypeClass}<?>) {TypeClass}.reference(Array{i}.class);");
      EmitSuppression(wr);
      var wrTypeMethod = wr.NewBlock($"public static <T> {TypeClass}<Array{i}<T>> {TypeMethodName}()");
      wrTypeMethod.WriteLine($"return ({TypeClass}<Array{i}<T>>) ({TypeClass}<?>) TYPE;");

      using (StreamWriter sw = File.CreateText(path + "/Array" + i + ".java")) {
        sw.Write(wrTop.ToString());
      }
    }

    protected override BlockTargetWriter EmitTailCallStructure(MemberDecl member, BlockTargetWriter wr) {
      if (!member.IsStatic && !NeedsCustomReceiver(member)) {
        var receiverType = UserDefinedType.FromTopLevelDecl(member.tok, member.EnclosingClass);
        var receiverTypeName = TypeName(receiverType, wr, member.tok);
        if (member.EnclosingClass.IsExtern(out _, out _)) {
          receiverTypeName = FormatExternBaseClassName(receiverTypeName);
        }
        wr.WriteLine("{0} _this = this;", receiverTypeName);
      }
      return wr.NewBlock("TAIL_CALL_START: while (true)");
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.WriteLine("continue TAIL_CALL_START;");
    }

    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("new java.util.ArrayList<>()");
      } else if (ct is MapType mt) {
        wr.Write($"new {DafnyMapClass}<>()");
      } else {
        Contract.Assume(false);  // unexpected collection type
      }
    }

    protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type boundVarType, out TargetWriter collectionWriter,
      TargetWriter wr, string altBoundVarName = null, Type altVarType = null, Bpl.IToken tok = null) {
      if (boundVarType != null) {
        wr.Write($"for({TypeName(boundVarType, wr, tok)} {boundVar} : ");
      } else {
        wr.Write($"for({DafnyTupleClass(TargetTupleSize)} {boundVar} : ");
      }
      collectionWriter = wr.Fork();
      if (altBoundVarName == null) {
        return wr.NewBlock(")");
      } else if (altVarType == null) {
        return wr.NewBlockWithPrefix(")", $"{altBoundVarName} = {boundVar};");
      } else {
        return wr.NewBlockWithPrefix(")", "{2} {0} = ({2}){1};", altBoundVarName, boundVar, TypeName(altVarType, wr, tok));
      }
    }

    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write($"{collName}.add(");
        TrExpr(elmt, wr, inLetExprBody);
        wr.WriteLine(");");
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr) {
      if (ct is SetType) {
        var typeName = BoxedTypeName(ct.Arg, wr, tok);
        return $"new dafny.DafnySet<{typeName}>({collName})";
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

    protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr) {
      return wr.NewNamedBlock($"goto_{label}:");
    }

    protected override void EmitBreak(string label, TargetWriter wr) {
      wr.WriteLine(label == null ? "break;" : $"break goto_{label};");
    }

    protected override void EmitAbsurd(string message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }

      wr.WriteLine($"throw new IllegalArgumentException(\"{message}\");");
    }

    protected override void EmitAbsurd(string message, TargetWriter wr, bool needIterLimit) {
      if (!needIterLimit) {
        EmitAbsurd(message, wr);
      }
    }

    protected override void EmitHalt(Expression messageExpr, TargetWriter wr) {
      wr.Write("throw new dafny.DafnyHaltException(");
      EmitToString(wr, messageExpr);
      wr.WriteLine(");");
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, TargetWriter wr){
      var cw = CreateClass(IdName(nt), null, wr) as ClassWriter;
      var w = cw.StaticMemberWriter;
      if (nt.NativeType != null) {
        var nativeType = GetBoxedNativeTypeName(nt.NativeType);
        var wEnum = w.NewNamedBlock($"public static java.util.ArrayList<{nativeType}> IntegerRange(java.math.BigInteger lo, java.math.BigInteger hi)");
        wEnum.WriteLine($"java.util.ArrayList<{nativeType}> arr = new java.util.ArrayList<>();");
        var numberval = "intValue()";
        if (nativeType == "Byte" || nativeType == "Short")
          numberval = $"{nativeType.ToLower()}Value()";
        wEnum.WriteLine($"for (java.math.BigInteger j = lo; j.compareTo(hi) < 0; j.add(java.math.BigInteger.ONE)) {{ arr.add(new {nativeType}(j.{numberval})); }}");
        wEnum.WriteLine("return arr;");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new TargetWriter(w.IndentLevel, true);
        TrExpr(nt.Witness, witness, false);
        if (nt.NativeType == null) {
          cw.DeclareField("Witness", true, true, nt.BaseType, nt.tok, witness.ToString());
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

    private void TrExprAsInt(Expression expr, TargetWriter wr, bool inLetExprBody) {
      // TODO: Optimize
      if (AsNativeType(expr.Type) == null) {
        TrParenExpr(expr, wr, inLetExprBody);
        wr.Write(".intValue()");
      } else {
        TrExpr(expr, wr, inLetExprBody);
      }
    }

    private void TrParenExprAsInt(Expression expr, TargetWriter wr, bool inLetExprBody) {
      wr.Write('(');
      TrExprAsInt(expr, wr, inLetExprBody);
      wr.Write(')');
    }

    private void TrParenExprAsInt(string prefix, Expression expr, TargetWriter wr, bool inLetExprBody) {
      wr.Write(prefix);
      TrParenExprAsInt(expr, wr, inLetExprBody);
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr) {
      // Where to put the array to be wrapped
      TargetWriter wBareArray;
      if (dimensions.Count > 1) {
        arrays.Add(dimensions.Count);
        wr.Write($"new {DafnyMultiArrayClass(dimensions.Count)}<>({TypeDescriptor(elmtType, wr, tok)}, ");
        foreach (var dim in dimensions) {
          TrExprAsInt(dim, wr, inLetExprBody: false);
          wr.Write(", ");
        }
        wBareArray = wr.Fork();
        wr.Write(")");
        if (mustInitialize) {
          wr.Write($".fillThenReturn({DefaultValue(elmtType, wr, tok)})");
        }
      } else {
        if (!elmtType.IsTypeParameter) {
          wr.Write($"({ArrayTypeName(elmtType, dimensions.Count, wr, tok)}) ");
        }
        if (mustInitialize) {
          wr.Write($"{TypeDescriptor(elmtType, wr, tok)}.fillThenReturnArray(");
        }
        wBareArray = wr.Fork();
        if (mustInitialize) {
          wr.Write($", {DefaultValue(elmtType, wr, tok)})");
        }
      }

      if (dimensions.Count > 1) {
        wBareArray.Write($"(Object{Util.Repeat("[]", dimensions.Count - 1)}) ");
      }
      wBareArray.Write($"{TypeDescriptor(elmtType, wr, tok)}.newArray(");
      var sep = "";
      foreach (var dim in dimensions) {
        wBareArray.Write(sep);
        TrExprAsInt(dim, wBareArray, inLetExprBody: false);
        sep = ", ";
      }
      wBareArray.Write(")");
    }

    protected override int EmitRuntimeTypeDescriptorsActuals(List<Type> typeArgs, List<TypeParameter> formals, Bpl.IToken tok, bool useAllTypeArgs, TargetWriter wr) {
      var sep = "";
      var c = 0;
      for (int i = 0; i < typeArgs.Count; i++) {
        var actual = typeArgs[i];
        var formal = formals[i];
        // Ignore useAllTypeArgs; we always need all of them
        wr.Write(sep);
        wr.Write(TypeDescriptor(actual, wr, tok));
        sep = ", ";
        c++;
      }
      return c;
    }
    protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs,
      List<Type> boundTypes, Type resultType, Bpl.IToken resultTok, bool inLetExprBody, TargetWriter wr){
      if (boundTypes.Count != 1) {
        functions.Add(boundTypes.Count);
      }
      wr.Write("(({0}<{1}{2}>)", DafnyFunctionIface(boundTypes.Count), Util.Comma("", boundTypes, t => BoxedTypeName(t, wr, resultTok) + ", "), BoxedTypeName(resultType, wr, resultTok));
      wr.Write($"({Util.Comma(boundVars)}) -> ");
      var w = wr.Fork();
      wr.Write(").apply");
      TrExprList(arguments, wr, inLetExprBody);
      return w;
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      return wr.NewNamedBlock($"for (java.math.BigInteger {indexVar} = java.math.BigInteger.ZERO; {indexVar}.compareTo({bound}) < 0; {indexVar} = {indexVar}.add(java.math.BigInteger.ONE))");
    }

    protected override string GetHelperModuleName() => DafnyHelpersClass;

    protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr){
      wr.WriteLine("new java.util.ArrayList<>();");
    }

    protected override void AddTupleToSet(int i) {
      tuples.Add(i);
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr) {
      // FIXME: tupleTypeArgs is wrong because it already got generated from
      // TypeName (with unboxed being the default)  :-(
      wr.Write($"{ingredients}.add(new {DafnyTupleClassPrefix}");
      var wrTuple = wr.Fork();
      wr.Write("));");
      return wrTuple;
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr){
      TrParenExpr(expr, wr, inLetExprBody);
      wr.Write(".intValue()");
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr) {
      wr.Write($"{prefix}.dtor__{i}()");
    }

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function, List<Expression> arguments, bool inLetExprBody, TargetWriter wr){
      TrParenExpr(function, wr, inLetExprBody);
      wr.Write(".apply");
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override TargetWriter EmitCoercionToNativeInt(TargetWriter wr) {
      wr.Write("((java.math.BigInteger)");
      var w = wr.Fork();
      wr.Write(").intValue()");
      return w;
    }

    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr) {
      return wr.NewNamedBlock($"for (java.math.BigInteger {indexVar} = java.math.BigInteger.valueOf({start}); ; {indexVar} = {indexVar}.multiply(new java.math.BigInteger(\"2\")))");
    }

    protected override void EmitIsZero(string varName, TargetWriter wr) {
      wr.Write($"{varName}.equals(java.math.BigInteger.ZERO)");
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr) {
      wr.WriteLine($"{varName} = {varName}.subtract(java.math.BigInteger.ONE);");
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr) {
      wr.WriteLine($"{varName} = {varName}.add(java.math.BigInteger.ONE);");
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      wr.Write("java.util.Arrays.asList");
      TrParenExpr(e, wr, inLetExprBody);
    }

    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write($"((java.util.function.Function<java.math.BigInteger, {BoxedTypeName(resultType, wr, resultTok)}>)(({bvName}) ->");
      var w = wr.NewBigExprBlock("", $")).apply(java.math.BigInteger.valueOf({source}))");
      return w;
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term, bool inLetExprBody, TargetWriter wr){
      wr.Write($"{collName}.put(");
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      TrExpr(term, wr, inLetExprBody);
      wr.WriteLine(");");
      return termLeftWriter;
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, TargetWriter wr) {
      wr.Write($"{DafnySeqClass}.Create({TypeDescriptor(expr.Type.AsCollectionType.Arg, wr, expr.tok)}, ");
      TrExpr(expr.N, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(expr.Initializer, wr, inLetExprBody);
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

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // (int or bv) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write($"new {DafnyBigRationalClass}(");
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("java.math.BigInteger.valueOf");
          }
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(", java.math.BigInteger.ONE)");
        } else if (e.ToType.IsCharType) {
          // Painfully, Java sign-extends bytes when casting to chars ...
          var fromNative = AsNativeType(e.E.Type);
          wr.Write("(char)");
          if (fromNative != null && fromNative.Sel == NativeType.Selection.Byte) {
            wr.Write("java.lang.Byte.toUnsignedInt");
            TrParenExpr(e.E, wr, inLetExprBody);
          } else {
            TrExprAsInt(e.E, wr, inLetExprBody);
          }
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative == null && toNative == null) {
            if (e.E.Type.IsCharType) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("java.math.BigInteger.valueOf");
              TrParenExpr(e.E, wr, inLetExprBody);
            } else {
              // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
              TrExpr(e.E, wr, inLetExprBody);
            }
          } else if (fromNative != null && toNative == null) {
            // native (int or bv) -> big-integer (int or bv)
            if (fromNative.Sel == NativeType.Selection.ULong) {
              // Can't just use .longValue() because that may return a negative
              wr.Write($"{DafnyHelpersClass}.unsignedLongToBigInteger");
              TrParenExpr(e.E, wr, inLetExprBody);
            } else {
              wr.Write("java.math.BigInteger.valueOf(");
              if (fromNative.LowerBound >= 0) {
                TrParenExpr($"{GetBoxedNativeTypeName(fromNative)}.toUnsignedLong", e.E, wr, inLetExprBody);
              } else {
                TrParenExpr(e.E, wr, inLetExprBody);
              }
              wr.Write(")");
            }
          } else if (fromNative != null && NativeTypeSize(toNative) == NativeTypeSize(fromNative)) {
            // native (int or bv) -> native (int or bv)
            // Cast between signed and unsigned, which have the same Java type
            TrParenExpr(e.E, wr, inLetExprBody);
          } else {
            GetNativeInfo(toNative.Sel, out var toNativeName, out var toNativeSuffix, out var toNativeNeedsCast);
            // any (int or bv) -> native (int or bv)
            // A cast would do, but we also consider some optimizations
            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              EmitNativeIntegerLiteral((BigInteger) literal, toNative, wr);
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              // Optimize || to avoid intermediate BigInteger
              wr.Write(CastIfSmallNativeType(e.ToType));
              TrParenExpr("", u.E, wr, inLetExprBody);
              wr.Write(".cardinalityInt()");
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .length to avoid intermediate BigInteger
              wr.Write(CastIfSmallNativeType(e.ToType));
              var elmtType = UserDefinedType.ArrayElementType(m.Obj.Type);
              TargetWriter w;
              if (elmtType.IsTypeParameter) {
                wr.Write($"{FormatTypeDescriptorVariable(elmtType.AsTypeParameter)}.getArrayLength(");
                w = wr.Fork();
                wr.Write(")");
              } else {
                w = wr.Fork();
                wr.Write(".length");
              }
              TrParenExpr(m.Obj, w, inLetExprBody);
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
                TrParenExpr(e.E, wr, inLetExprBody);
              } else {
                if (fromNative == null && !e.E.Type.IsCharType) {
                  TrParenExpr(e.E, wr, inLetExprBody);
                  wr.Write($".{toNativeName}Value()");
                } else {
                  wr.Write($"(({toNativeName}) ");
                  TrParenExpr(e.E, wr, inLetExprBody);
                  wr.Write(")");
                }
              }
            }
          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody);
        } else if (e.ToType.IsCharType) {
          // real -> char
          // Painfully, Java sign-extends bytes when casting to chars ...
          wr.Write("(char)");
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".ToBigInteger().intValue()");
        } else {
          // real -> (int or bv)
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".ToBigInteger()");
          if (AsNativeType(e.ToType) != null) {
            wr.Write($".{GetNativeTypeName(AsNativeType(e.ToType))}Value()");
          }
        }
      } else {
        Contract.Assert(e.E.Type.IsBigOrdinalType);
        Contract.Assert(e.ToType.IsNumericBased(Type.NumericPersuation.Int));
        TrParenExpr(e.E, wr, inLetExprBody);
        if (AsNativeType(e.ToType) != null) {
          wr.Write($".{GetNativeTypeName(AsNativeType(e.ToType))}Value()");
        }
      }
    }

    protected override BlockTargetWriter CreateStaticMain(IClassWriter cw) {
      var wr = ((ClassWriter) cw).StaticMemberWriter;
      return wr.NewBlock("public static void Main(string[] args)");
    }

    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write($"{DafnyHelpersClass}.Let(");
      wr.Write($"{source}, {bvName} -> ");
      var w = wr.Fork();
      wr.Write(")");
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write($"{DafnyHelpersClass}.Let(");
      TrExpr(source, wr, inLetExprBody);
      wr.Write($", {bvName} -> ");
      var w = wr.Fork();
      wr.Write(")");
      return w;
    }

    protected override string GetQuantifierName(string bvType) {
      return $"{DafnyHelpersClass}.Quantifier";
    }

    // ABSTRACT METHOD DECLARATIONS FOR THE SAKE OF BUILDING PROGRAM

    protected override void EmitYield(TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr)
    {
      throw new NotImplementedException();
    }
  }
}
