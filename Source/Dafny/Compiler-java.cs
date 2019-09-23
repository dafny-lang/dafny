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
      IntSelect = ",BigInteger";
      LambdaExecute = ".apply";
    }

    public override String TargetLanguage => "Java";


    // Shadowing variables in Compiler.cs
    new string DafnySetClass = "dafny.DafnySet";
    new string DafnyMultiSetClass = "dafny.DafnyMultiset";
    new string DafnySeqClass = "dafny.DafnySequence";
    new string DafnyMapClass = "dafny.DafnyMap";

    private String ModuleName;
    private String ModulePath;
    private int FileCount = 0;
    private Import ModuleImport;
    private HashSet<int> tuples = new HashSet<int>();
    private HashSet<int> functions = new HashSet<int>();
    private HashSet<int> arrays = new HashSet<int>();
    private HashSet<int> arrayinits = new HashSet<int>();
    private HashSet<string> NeedsInputStrings = new HashSet<string>();

    private static List<Import> StandardImports =
      new List<Import>{
        new Import{Name = "_dafny", Path = "dafny"},
      };
    private readonly List<Import> Imports = new List<Import>(StandardImports);

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

    protected override void DeclareSpecificOutCollector(string collectorVarName, TargetWriter wr, int outCount, List<Type> types, Method m) {
      if (outCount > 1) {
        tuples.Add(outCount);
        wr.Write($"Tuple{outCount} {collectorVarName} = ");
      } else {
        for (int i = 0; i < types.Count; i++) {
          Formal p = m.Outs[i];
          if (!p.IsGhost) {
            wr.Write($"{TypeName(types[i], wr, p.tok)} {collectorVarName} = ");
            return;
          }
        }
      }
    }
    protected override void EmitCastOutParameterSplits(string outCollector, List<string> actualOutParamNames,
      TargetWriter wr, List<Type> actualOutParamTypes, Bpl.IToken tok){
      if (actualOutParamNames.Count == 1){
        EmitAssignment(actualOutParamNames[0], null, outCollector, null, wr);
      }
      else {
        for (var i = 0; i < actualOutParamNames.Count; i++){
          SplitType(TypeName(actualOutParamTypes[i], wr, tok), out _, out var n);
          wr.WriteLine($"{actualOutParamNames[i]} = ({n}) {outCollector}.dtor__{i}();");
        }
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
        wIndex.Write("((BigInteger)");
        EmitTupleSelect(tup, i + 1, wIndex);
        wIndex.Write(")");
        indices.Add(wIndex.ToString());
      }
      EmitArraySelectAsLvalue(array, indices, tupleTypeArgsList[L - 1], wr);
      wr.Write(" = ");
      EmitTupleSelect(tup, L - 1, wr);
      EndStmt(wr);
    }

    protected override void WriteCast(string s, TargetWriter wr) {
      wr.Write($"({s})");
    }

    protected override bool ReturnStyleHelper(string returnStyleOutCollector) {
      return returnStyleOutCollector != null;
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
        wrVarInit.Write($"ArrayList<Tuple{L}<{tupleTypeArgs}>> {ingredients} = ");
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
      wBody.WriteLine($"{companion}.{IdName(mainMethod)}();");
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
        cw.DeclareField("Witness", true, true, sst.Rhs, sst.tok, sst.Rhs.AsBitVectorType != null ? $"new {TypeName(sst.Witness.Type, sw, sst.tok)}({sw})" : sw.ToString());
      }
    }

    protected class ClassWriter : IClassWriter {
      public readonly JavaCompiler Compiler;
      public readonly BlockTargetWriter InstanceMemberWriter;
      public readonly BlockTargetWriter StaticMemberWriter;

      public ClassWriter(JavaCompiler compiler, BlockTargetWriter instanceMemberWriter, BlockTargetWriter staticMemberWriter = null) {
        Contract.Requires(compiler != null);
        Contract.Requires(instanceMemberWriter != null);
        this.Compiler = compiler;
        this.InstanceMemberWriter = instanceMemberWriter;
        this.StaticMemberWriter = staticMemberWriter == null ? instanceMemberWriter : staticMemberWriter;
      }

      public BlockTargetWriter Writer(bool isStatic) {
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
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, Writer(isStatic));
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
        targetReturnTypeReplacement = "Tuple" + nonGhostOuts;
      }
      wr.Write("{0}{1}", createBody ? "public " : "", m.IsStatic ? "static " : "");
      if (m.TypeArgs.Count != 0) {
        wr.Write($"<{TypeParameters(m.TypeArgs)}> ");
      }
      wr.Write("{0} {1}", targetReturnTypeReplacement ?? "void", IdName(m));
      wr.Write("(");
      var nTypes = WriteRuntimeTypeDescriptorsFormals(m, m.TypeArgs, nonGhostOuts > 0, wr);
      WriteFormals(nTypes > 0 ? ", " : "", m.Ins, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      } else {
        var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        if (m.IsTailRecursive) {
          w = w.NewBlock("TAIL_CALL_START: while (true)");
        }
        return w;
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
      wr.Write("{0}{1}", createBody ? "public " : "", isStatic ? "static " : "");
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
      WriteFormals("", formals, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      } else {
        BlockTargetWriter w;
        if (formals.Count > 1) {
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

    protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      if (isStatic){
        var r = RemoveParams((rhs != null) ? rhs : DefaultValue(type, wr, tok));
        var t = RemoveParams(TypeName(type, wr, tok));
        wr.WriteLine($"public static {t} {name} = {r};");
      }
      else{
        wr.WriteLine("public {0} {1} = {2};", TypeName(type, wr, tok), name, rhs ?? DefaultValue(type, wr, tok));
        //If the previous field is s*, then we know it is a string for getDefault, which requires warnings to be suppressed before the line
        if (name.StartsWith("s") && name.Length == 2) {
          EmitSuppression(wr);
        }
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
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        return "Object";
      }
      if (xType is BoolType) {
        return "Boolean";
      } else if (xType is CharType) {
        return "Character";
      } else if (xType is IntType || xType is BigOrdinalType) {
        return "BigInteger";
      } else if (xType is RealType) {
        return "BigRational";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType) : "BigInteger";
      } else if (xType.AsNewtype != null) {
        var nativeType = xType.AsNewtype.NativeType;
        if (nativeType != null) {
          return GetNativeTypeName(nativeType);
        }
        return TypeName(xType.AsNewtype.BaseType, wr, tok);
      } else if (xType.IsObjectQ) {
        return "Object";
      } else if (xType.IsArrayType) {
        ArrayClassDecl at = xType.AsArrayType;
        Contract.Assert(at != null);  // follows from type.IsArrayType
        if (at.Dims > 1) {
          return "Array" + at.Dims;
        }
        Type elType = UserDefinedType.ArrayElementType(xType);
        string typeNameSansBrackets, brackets;
        TypeName_SplitArrayName(elType, wr, tok, out typeNameSansBrackets, out brackets);
        return typeNameSansBrackets + "[]";
      } else if (xType is UserDefinedType) {
        var udt = (UserDefinedType)xType;
        var s = FullTypeName(udt, member);
        if (s.Equals("string")){
          return "String";
        }
        var cl = udt.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "ULong";
        }
        else if (DafnyOptions.O.IronDafny &&
                 !(xType is ArrowType) &&
                 cl != null &&
                 cl.Module != null &&
                 !cl.Module.IsDefaultModule){
          s = cl.FullCompileName;
        }

        return TypeName_UDT(s, udt.TypeArgs, wr, udt.tok);
      } else if (xType is SetType) {
        Type argType = ((SetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnySetClass + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is SeqType) {
        Type argType = ((SeqType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnySeqClass + "<" + TypeName(argType, wr, tok) + ">";

      } else if (xType is MultiSetType) {
        Type argType = ((MultiSetType)xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnyMultiSetClass + "<" + TypeName(argType, wr, tok) + ">";
      } else if (xType is MapType) {
        Type domType = ((MapType)xType).Domain;
        Type ranType = ((MapType)xType).Range;
        if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) {
          Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr);
        }
        return DafnyMapClass + "<" + TypeName(domType, wr, tok) + "," + TypeName(ranType, wr, tok) + ">";
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
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
        return $"Function{(udt.TypeArgs.Count != 2 ? (udt.TypeArgs.Count - 1).ToString() : "")}";
      }
      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      }
      else if (cl.Module.CompileName == ModuleName || cl is TupleTypeDecl || cl.Module.IsDefaultModule) {
        return IdProtect(cl.CompileName);
      }
      else{
        return IdProtect(cl.Module.CompileName) + "." + IdProtect(cl.CompileName);
      }
    }

    protected override string TypeNameArrayBrackets(int dims){
      Contract.Requires(0 <= dims);
      var name = "[";
      for (int i = 1; i < dims; i++){
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
        s += "<" + TypeNames(typeArgs, wr, tok) + ">";
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
        s += $"Tuple{inArgs.Count}<" + TypeNames(inArgs, wr, tok) + ">";
        tuples.Add(inArgs.Count);
      } else {
        if (inArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }
        s += "" + TypeNames(inArgs, wr, tok) + "";
      }
      if (outArgs != null) {
        if (inArgs.Count > 0){
          s += ", ";
        }
        s += TypeName(outArgs, wr, tok) + "";
      }
      s += ">";
      return s;
    }

    protected override IClassWriter CreateClass(string name, bool isExtern, string /*?*/ fullPrintName,
      List<TypeParameter> /*?*/ typeParameters, List<Type> /*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      if (isExtern) {
        return new ClassWriter(this, new BlockTargetWriter(TargetWriter.IndentAmount, "", ""));
      }
      var filename = $"{ModulePath}/{name}.java";
      var w = wr.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Class {name}");
      w.WriteLine($"// Dafny class {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      w.WriteLine("import java.util.*;");
      w.WriteLine("import java.util.function.*;");
      w.WriteLine("import java.util.Arrays;");
      w.WriteLine("import java.lang.reflect.Array;");
      w.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
      EmitImports(w, out _);
      w.WriteLine();
      //TODO: Fix implementations so they do not need this suppression
      EmitSuppression(w);
      w.Write($"public class {name}");
      if (typeParameters != null && typeParameters.Count != 0) {
        w.Write($"<{TypeParameters(typeParameters)}>");
      }
      // Since Java does not support multiple inheritance, we are assuming a list of "superclasses" is a list of interfaces
      if (superClasses != null) {
        string sep = " implements ";
        foreach (var trait in superClasses) {
          w.Write($"{sep}{TypeName(trait, w, tok)}");
          sep = ", ";
        }
      }
      return new ClassWriter(this, w.NewBlock(""));
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
        wr.Write("DafnySequence.asString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) != null) {
        GetNativeInfo(AsNativeType(e.Type).Sel, out var name, out var literalSuffix, out _);
        var cast = name == "Short" || name == "Byte" ? $"({name.ToLower()})" : "";
        wr.Write($"new {name}({cast}{(BigInteger)e.Value}{literalSuffix})");
      } else if (e.Value is BigInteger i) {
        if (i.IsZero) {
          wr.Write("BigInteger.ZERO");
        } else if (i.IsOne) {
          wr.Write("BigInteger.ONE");
        } else if (long.MinValue <= i && i <= long.MaxValue) {
          wr.Write($"BigInteger.valueOf({i}L)");
        } else {
          wr.Write($"new BigInteger(\"{i}\")");
        }
      } else if (e.Value is Basetypes.BigDec n){
        if (0 <= n.Exponent){
          wr.Write($"new dafny.BigRational(new BigInteger(\"{n.Mantissa}");
          for (int j = 0; j < n.Exponent; j++){
            wr.Write("0");
          }
          wr.Write("\"), BigInteger.ONE)");
        } else {
          wr.Write("new dafny.BigRational(");
          wr.Write($"new BigInteger(\"{n.Mantissa}\")");
          wr.Write(", new BigInteger(\"1");
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

    protected string GetNativeDefault(NativeType.Selection sel) {
      switch (sel) {
        case NativeType.Selection.Byte:
          return "new dafny.UByte(0)";
        case NativeType.Selection.SByte:
          return "new Byte((byte)0)";
        case NativeType.Selection.UShort:
          return "new dafny.UShort";
        case NativeType.Selection.Short:
          return "new Short((short)0)";
        case NativeType.Selection.UInt:
          return "new dafny.UInt(0)";
        case NativeType.Selection.Int:
          return "0";
        case NativeType.Selection.ULong:
          return "new dafny.ULong(0)";
        case NativeType.Selection.Number:
        case NativeType.Selection.Long:
          return "0L";
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    private HashSet<string> unsignedTypes = new HashSet<string> {"dafny.UByte", "dafny.UShort", "dafny.UInt", "dafny.ULong"};

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix,
      out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
          name = "dafny.UByte";
          break;
        case NativeType.Selection.SByte:
          name = "Byte";
          break;
        case NativeType.Selection.UShort:
          name = "dafny.UShort";
          break;
        case NativeType.Selection.Short:
          name = "Short";
          break;
        case NativeType.Selection.UInt:
          name = "dafny.UInt";
          literalSuffix = "L";
          break;
        case NativeType.Selection.Int:
          name = "Integer";
          break;
        case NativeType.Selection.ULong:
          name = "dafny.ULong";
          break;
        case NativeType.Selection.Number:
        case NativeType.Selection.Long:
          name = "Long";
          literalSuffix = "L";
          break;
        default:
          Contract.Assert(false);  // unexpected native type
          throw new cce.UnreachableException();  // to please the compiler
      }
    }

    protected override void EmitThis(TargetWriter wr) {
      wr.Write("this");
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, TargetWriter wr){
      if (type != null && type.AsArrayType != null){
        arrays.Add(type.AsArrayType.Dims);
      }
      if (type.IsDatatype && type.AsDatatype is TupleTypeDecl) {
        wr.Write($"Tuple{type.AsDatatype.TypeArgs.Count} {name}");
        tuples.Add(type.AsDatatype.TypeArgs.Count);
      } else {
        if (type.IsTypeParameter) {
          EmitSuppression(wr);
        }
        wr.Write("{0} {1}", type != null ? TypeName(type, wr, tok) : "Object", name);
      }
      if (leaveRoomForRhs){
        Contract.Assert(rhs == null); // follows from precondition
      } else if (rhs != null){
        wr.WriteLine($" = {rhs};");
      } else if (type.IsIntegerType) {
        wr.WriteLine(" = BigInteger.ZERO;");
      } else {
        wr.WriteLine(";");
      }
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, TargetWriter wr, Type t) {
      DeclareLocalVar(name, t, tok, leaveRoomForRhs, rhs, wr);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write($"{CollectionTypeUnparameterizedName(ct)}.of(");
      string sep = "";
      foreach (Expression e in elements) {
        wr.Write(sep);
        TrExpr(e, wr, inLetExprBody);
        sep = ", ";
      }
      wr.Write(")");
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("new dafny.DafnyMap() {{{{\n");
      foreach (ExpressionPair p in elements) {
        wr.Write("put(");
        TrExpr(p.A, wr, inLetExprBody);
        wr.Write(", ");
        TrExpr(p.B, wr, inLetExprBody);
        wr.Write(");\n");
      }
      wr.Write("}}}}");
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
          compiledName = idParam == null ? "length" : "dims" + (int)idParam;
          if (id == SpecialField.ID.ArrayLength) {
            preString = "BigInteger.valueOf(";
            postString = ")";
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

    protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType,
      TargetWriter wr) {
      return EmitMemberSelect(member, isLValue, expectedType, wr, false);
    }

    protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr, bool MemberSelectObjIsTrait) {
      var wSource = wr.Fork();
      if (isLValue && member is ConstantField) {
        wr.Write($".{member.CompileName}");
      } else if (!isLValue && member is SpecialField sf) {
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out var compiledName, out _, out _);
        if (compiledName.Length != 0){
          wr.Write(".{0}{1}{2}", MemberSelectObjIsTrait && !sf.IsStatic ? "get_" : "", compiledName,
            (MemberSelectObjIsTrait && !sf.IsStatic) || member.EnclosingClass is DatatypeDecl ? "()" : "");
        }
      } else if (!isLValue && MemberSelectObjIsTrait && !member.IsStatic) {
        wr.Write($".get_{IdName(member)}()");
      } else if (isLValue && MemberSelectObjIsTrait && !member.IsStatic) {
        wr.Write($".set_{IdName(member)}(");
      } else if (member is Function) {
        wr.Write($"::{IdName(member)}");
      } else {
        wr.Write($".{IdName(member)}");
      }
      return wSource;
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, TargetWriter wr){
      wr.Write($"{source}.is_{ctor.CompileName}()");
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl member){
      if (type is UserDefinedType udt) {
        if (udt.ResolvedClass is TraitDecl){
          string s = IdProtect(udt.FullCompanionCompileName);
          Contract.Assert(udt.TypeArgs.Count == 0); // traits have no type parameters
        return s;
        } else if (udt.ResolvedClass.Module.CompileName == ModuleName || udt.ResolvedClass is TupleTypeDecl || udt.ResolvedClass.Module.IsDefaultModule) {
          return IdProtect(udt.ResolvedClass.CompileName);
        } else{
          return IdProtect(udt.ResolvedClass.FullCompileName);
        }
      } else {
        return TypeName(type, wr, tok, member);
      }
    }

    protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      if (indices.Count == 1) {
        wr.Write($"[{indices[0]}");
        if (!int.TryParse(indices[0], out _)) wr.Write(".intValue()");
        wr.Write("]");
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write($"[{index}");
          if (!int.TryParse(index, out _)) wr.Write(".intValue()");
          wr.Write("]");
        }
      }
      return w;
    }

    protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      if (indices.Count == 1) {
        wr.Write("[");
        TrParenExpr(indices[0], wr, inLetExprBody);
        wr.Write(".intValue()]");
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write("[");
          TrParenExpr(index, wr, inLetExprBody);
          wr.Write(".intValue()]");
        }
      }
      return w;
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      if (fromArray) {
        wr.Write("DafnySequence.fromArrayRange(");
      }
      TrParenExpr(source, wr, inLetExprBody);
      if (fromArray) {
        wr.Write(", ");
        if (lo != null) {
          TrParenExpr(lo, wr, inLetExprBody);
          wr.Write(".intValue()");
        } else {
          wr.Write("0");
        }
        wr.Write(", ");
        if (hi != null) {
          TrParenExpr(hi, wr, inLetExprBody);
          wr.Write(".intValue()");
        } else {
          TrParenExpr(source, wr, inLetExprBody);
          wr.Write(".length");
        }
        wr.Write(")");
      } else {
        if (lo != null && hi != null) {
          wr.Write(".subsequence(");
          TrParenExpr(lo, wr, inLetExprBody);
          wr.Write(".intValue(), ");
          TrParenExpr(hi, wr, inLetExprBody);
          wr.Write(".intValue())");
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
      // ( e0 op1 e1) | (e0 op2 (width - e1))
      if (needsCast) {
        wr.Write("(" + nativeName + ")(");
      }
      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? ".shiftLeft" : ".shiftRight", isRotateLeft, nativeType, true, wr, inLetExprBody, tr);
      wr.Write(")");
      wr.Write (".or");
      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? ".shiftRight" : ".shiftLeft", !isRotateLeft, nativeType, false, wr, inLetExprBody, tr);
      wr.Write(")))");
      if (needsCast) {
        wr.Write(")");
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
      wr.Write("(");
      tr(e1, wr, inLetExprBody);
      wr.Write(".intValue()");
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
        wr.Write($"({nativeName})((");
      }
      // --- Middle
      var middle = wr.Fork();
      // --- After
      // do the truncation, if needed
      if (bvType.NativeType == null) {
        wr.Write($").and((BigInteger.ONE.shiftLeft({bvType.Width})).subtract(BigInteger.ONE)))");
      } else {
        if (bvType.NativeType.Bitwidth != bvType.Width) {
          // print in hex, because that looks nice
          var t = RepresentableByInt(bvType.NativeType) ? "" : "L";
          wr.Write($").and(new {nativeName}(0x{(1UL << bvType.Width) - 1:X}{literalSuffix}{t})))");
        } else {
          wr.Write("))");  // close the parentheses for the cast
        }
      }
      return middle;
    }

    private static bool RepresentableByInt(NativeType n){
      return !(n.Sel.Equals(NativeType.Selection.ULong) || n.Sel.Equals(NativeType.Selection.Long)
                                                        || n.Sel.Equals(NativeType.Selection.Number));
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

    private readonly BigInteger java_max_int = 2147483647;

    protected override void TrBvExpr(Expression expr, TargetWriter wr, bool inLetExprBody){
      var bv = expr.Type.AsBitVectorType;
      if (bv != null && expr is LiteralExpr literalExpr) {
        // If literal is larger than Java's max int value, make it a Long instead to avoid overflow error
        var suffix = (BigInteger)literalExpr.Value > java_max_int ? "L" : "";
        wr.Write(bv.NativeType != null ? $"new {GetNativeTypeName(bv.NativeType)}({literalExpr.Value}{suffix})" : $"BigInteger.valueOf({literalExpr.Value}{suffix})");
      } else {
        TrParenExpr(expr, wr, inLetExprBody);
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
      wr.WriteLine("import java.util.*;");
      wr.WriteLine("import java.util.function.*;");
      wr.WriteLine("import java.util.Arrays;");
      wr.WriteLine("import java.lang.reflect.Array;");
      wr.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
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
        wr.WriteLine($"public {dt}() {{ }}");
      }
      wr.Write($"static {dt} theDefault = ");
      DatatypeCtor defaultCtor;
      if (dt is IndDatatypeDecl) {
        defaultCtor = ((IndDatatypeDecl)dt).DefaultCtor;
      } else {
        defaultCtor = ((CoDatatypeDecl) dt).Ctors[0];
      }
      wr.Write($"new {DtCtorName(defaultCtor)}(");
      string sep = "";
      foreach (Formal f in defaultCtor.Formals) {
        if (!f.IsGhost) {
          wr.Write($"{sep}null");
          sep = ", ";
        }
      }
      wr.WriteLine(");");
      wr.WriteLine("public static String defaultInstanceName = theDefault.getClass().toString();");
      using (var w = wr.NewNamedBlock($"public static {IdName(dt)} Default()")) {
        w.WriteLine("return theDefault;");
      }
      wr.WriteLine($"public static {dt} _DafnyDefaultValue() {{ return {dt}.Default(); }}");
      // create methods
      // TODO:  Need to revisit this. Java cannot reference generic types in a static context, so this wont work.
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
        var w = wr.NewNamedBlock($"public static ArrayList<{DtT_protected}> AllSingletonConstructors()");
        string arraylist = "singleton_iterator";
        w.WriteLine($"ArrayList<{DtT_protected}> {arraylist} = new ArrayList<>();");
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

      return new ClassWriter(this, btw);
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
        wr.WriteLine("import java.util.*;");
        wr.WriteLine("import java.util.function.*;");
        wr.WriteLine("import java.util.Arrays;");
        wr.WriteLine("import java.lang.reflect.Array;");
        wr.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
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
        wr.WriteLine("import java.util.*;");
        wr.WriteLine("import java.util.function.*;");
        wr.WriteLine("import java.util.Arrays;");
        wr.WriteLine("import java.lang.reflect.Array;");
        wr.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
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
              w.Write($"{nm}.equals(o.{nm})");
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
            w.WriteLine($"hash = ((hash << 5) + hash) + ((long)this.{nm}.hashCode());");
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
                w.WriteLine($"{tempVar}.append(this.{FormalName(arg, i)} == null ? \"\" : this.{FormalName(arg, i)}.toString());");
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
        s += "<" + TypeNames(typeArgs, wr, ctor.tok) + ">";
      }
      return s;
    }
    string DtCtorName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
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
      if (arg.Type.IsArrowType) {
        wr.Write(IdName(((IdentifierExpr) ((ConcreteSyntaxExpression)arg).ResolvedExpression).Var) + " == null ? null : \"Function\"");
      } else {
        TrExpr(arg, wr, false);
        if (arg.Type.AsCollectionType != null && arg.Type.AsCollectionType.AsSeqType!= null && arg.Type.AsCollectionType.AsSeqType.Arg is CharType){
          wr.Write(".verbatimString()");
        }
      }
      wr.WriteLine(");");
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
        files.Add(Path.GetFullPath(file));
      }
      var classpath = GetClassPath(targetFilename);
      foreach (var file in files) {
        var psi = new ProcessStartInfo("javac", file) {
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
          throw new Exception($"Error while compiling Java file {file}. Process exited with exit code {proc.ExitCode}");
        }
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
        wr.WriteLine($"return new Tuple{outParams.Count}<>({Util.Comma(outParams, IdName)});");
      }
    }

    private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*;$");

    // TODO: See if more types need to be added
    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || t.IsRefType;
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
      if (type is UserDefinedType definedType && NeedsInputStrings.Contains(definedType.CompileName)) {
        EmitRuntimeTypeDescriptors(definedType.TypeArgs, tok, wr);
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


    private void EmitRuntimeTypeDescriptors(List<Type> typeArgs, Bpl.IToken tok, TargetWriter wr) {
      var sep = "";
      foreach (var actual in typeArgs) {
        SplitType(TypeName(actual, wr, tok), out _, out var n);
        if (actual.IsDatatype){
          wr.Write($"{sep}{n}.defaultInstanceName");
        } else if (actual.IsTypeParameter) {
          wr.Write($"s{n}");
        } else {
          wr.Write($"{sep}{n}.class.toString()");
        }
        sep = ", ";
      }
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization){
          wr.Write($"{prefix}String s{tp.Name}");
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
          wr.Write($"{prefix}String s{tp.Name}");
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
      wr.Write($"ArrayList<{TypeName(((SetType)expr.Type).Arg, wr, null)}> {collection_name} = ");
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

    protected override void EmitTypeParams(IClassWriter classWriter, List<TypeParameter> l, Field f, TextWriter errorWr){
      l.Add(f.Type.AsTypeParameter);
      classWriter.DeclareField($"s{f.Type.AsTypeParameter.Name}", false, false, Type.String(), null, "null");
      classWriter.DeclareField(IdName(f), f.IsStatic, false, f.Type, f.tok, DefaultValue(f.Type, errorWr, f.tok, true));
    }

    protected override void EmitAssignment(out TargetWriter wLhs, Type /*?*/ lhsType, out TargetWriter wRhs, Type /*?*/ rhsType, TargetWriter wr) {
      EmitAssignment(out wLhs, lhsType, out wRhs, rhsType, wr, false);
    }

    protected override void EmitAssignment(out TargetWriter wLhs, Type /*?*/ lhsType, out TargetWriter wRhs, Type /*?*/ rhsType, TargetWriter wr, bool MemberSelectObjIsTrait){
      wLhs = wr.Fork();
      if (!MemberSelectObjIsTrait)
        wr.Write(" = ");
      TargetWriter w;
      w = rhsType != null ? EmitCoercionIfNecessary(@from: rhsType, to: lhsType, tok: Bpl.Token.NoToken, wr: wr) : wr;
      wRhs = w.Fork();
      if (MemberSelectObjIsTrait)
        w.Write(")");
      EndStmt(wr);
    }

    protected override TargetWriter EmitCoercionIfNecessary(Type/*?*/ from, Type/*?*/ to, Bpl.IToken tok, TargetWriter wr) {
      if (to == null) {
        return wr;
      }
      from = from?.NormalizeExpand();
      to = to.NormalizeExpand();
      if (from is BitvectorType && to is BitvectorType && ((BitvectorType)from).NativeType != null){
        GetNativeInfo(((BitvectorType)from).NativeType.Sel, out var p, out _, out _);
        wr.Write($"new {p}(");
        var w = wr.Fork();
        wr.Write(")");
        return w;
      }
      return wr;
    }


    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      var dtName = dt.CompileName;
      var ctorName = dtv.Ctor.CompileName;
      var typeParams = dtv.InferredTypeArgs.Count == 0 ? "" : "<>";
      //TODO: Determine if this implementation is ever needed
//      var typeDecl = dtv.InferredTypeArgs.Count == 0
//        ? ""
//        : string.Format("new {0}", TypeNames(dtv.InferredTypeArgs, wr, dtv.tok));
      if (!dtv.IsCoCall) {
        wr.Write("new {0}{1}{2}", dtName, dt.IsRecordType ? "" : "_" + ctorName, typeParams);
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   new Dt_Cons<T>( args )
        if (arguments != null && !arguments.Equals("")){
          wr.Write($"({arguments})");
        } else {
          wr.Write("()");
        }
      } else {
        wr.Write($"new {dtv.DatatypeName}__Lazy(");
        wr.Write("() -> { return ");
        wr.Write($"new {DtCtorName(dtv.Ctor)}({arguments})");
        wr.Write("; })");
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false) {
      if (inTypes.Count != 1) {
        functions.Add(inTypes.Count);
      }
      wr.Write('(');
      if (!untyped) {
        wr.Write("(Function{0}<{1}{2}>)", inTypes.Count != 1 ? inTypes.Count.ToString() : "", Util.Comma("", inTypes, t => TypeName(t, wr, tok) + ", "), TypeName(resultType, wr, tok));
      }
      wr.Write($"({Util.Comma(inNames, nm => nm)}) ->");
      var w = wr.NewExprBlock("");
      wr.Write(")");
      return w;
    }

    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      functions.Add(0);
      wr.Write($"((Function0<{TypeName(resultType, wr, resultTok)}>)(() ->");
      var w = wr.NewBigExprBlock("", ")).apply()");
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("", expr, wr, inLetExprBody);
          wr.Write(".not()");
          break;
        case ResolvedUnaryOp.Cardinality:
          if (expr.Type.AsCollectionType is MultiSetType) {
            TrParenExpr("", expr, wr, inLetExprBody);
            wr.Write(".cardinality()");
          } else if (expr.Type.AsCollectionType is SetType || expr.Type.AsCollectionType is MapType) {
            TrParenExpr("BigInteger.valueOf(", expr, wr, inLetExprBody);
            wr.Write(".size())");
          } else if (expr.Type.IsArrayType) {
            TrParenExpr("BigInteger.valueOf(", expr, wr, inLetExprBody);
            wr.Write(".length)");
          } else {
            TrParenExpr("BigInteger.valueOf(", expr, wr, inLetExprBody);
            wr.Write(".length())");
          }
          break;
        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
      }
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
          callString = "and";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          callString = "or";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          callString = "xor";
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
          callString = "compareTo";
          postOpString = " < 0";
          break;
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.Le:
          callString = "compareTo";
          postOpString = " <= 0";
          break;
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
          callString = "compareTo";
          postOpString = " >= 0";
          break;
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">=";
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
          callString = "compareTo";
          postOpString = " > 0";
          break;
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">";
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          callString = "shiftLeft";
          truncateResult = true;
          convertE1_to_int = true;
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          callString = "shiftRight";
          convertE1_to_int = true;
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = "(char) (";
            postOpString = ")";
            opString = "+";
          } else if (resultType is UserDefinedType && !resultType.IsIntegerType && !unsignedTypes.Contains(TypeName(e0.Type, null, tok)) && !unsignedTypes.Contains(TypeName(e1.Type, null, tok))) {
            opString = "+";
          } else {
            callString = "add";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = "(char) (";
            opString = "-";
            postOpString = ")";
          } else if (resultType is UserDefinedType && !resultType.IsIntegerType && !unsignedTypes.Contains(TypeName(e0.Type, null, tok)) && !unsignedTypes.Contains(TypeName(e1.Type, null, tok))) {
            opString = "-";
          } else {
            callString = "subtract";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          callString = "multiply";
          truncateResult = true;
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = "DafnyEuclidean.EuclideanDivision" + suffix;
          } else {
            callString = "divide";
          }
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType || (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = "DafnyEuclidean.EuclideanModulus" + suffix;
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
        case BinaryExpr.ResolvedOpcode.MapDisjoint:
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

      wr.WriteLine($"public static String defaultInstanceName = Tuple{i}.class.toString();");
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
        return "BigInteger.ZERO";
      } else if (xType is RealType) {
        return "BigRational.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? $"new {GetNativeTypeName(t.NativeType)}(0)" : "BigInteger.ZERO";
      } else if (xType is CollectionType collType) {
        string collName = CollectionTypeUnparameterizedName(collType);
        string argNames = TypeName(collType.Arg, wr, tok);
        if (xType is MapType mapType) {
          argNames += "," + TypeName(mapType.Range, wr, tok);
        }
        return $"{collName}.<{argNames}> empty()";
      }
      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
        return $"({type}) Helpers.getDefault(s{type})";
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return FullTypeName(udt) + ".Witness";
        } else if (td.NativeType != null) {
          return GetNativeDefault(td.NativeType.Sel);
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
            return $"(({TypeName(xType, wr, udt.tok)}) null)";
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) -> rangeDefaultValue)
            return $"(({Util.Comma(", ", udt.TypeArgs.Count - 1, i => $"{TypeName(udt.TypeArgs[i], wr, udt.tok)} x{i}")}) -> {rangeDefaultValue})";
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            TypeName_SplitArrayName(udt.TypeArgs[0], wr, udt.tok, out var typeNameSansBrackets, out _);
            string newarr = "";
            if (arrayClass.Dims > 1){
              arrays.Add(arrayClass.Dims);
              newarr += $"new Array{arrayClass.Dims}(";
              for (int i = 0; i < arrayClass.Dims; i++) {
                newarr += "0, ";
              }
            }
            if (udt.TypeArgs[0] is UserDefinedType && (udt.TypeArgs[0] as UserDefinedType).ResolvedClass == null) {
              newarr += $"({(udt.TypeArgs[0] as UserDefinedType).CompileName}";
              for (int i = 0; i < arrayClass.Dims; i++) {
                newarr += "[]";
              }
              newarr += ")";
              // Java class strings are written in the format "class x", so we use substring(6) to get the classname "x"
              newarr += $"Array.newInstance(dafny.Helpers.getClassUnsafe(s{udt.TypeArgs[0]}.substring(6))";
              for (int i = 0; i < arrayClass.Dims; i++) {
                newarr += ", 0";
              }
              newarr += ")";
              if (arrayClass.Dims > 1) {
                newarr += ")";
              }
              return newarr;
            }
            newarr += $"new {typeNameSansBrackets}";
            for (int i = 0; i < arrayClass.Dims; i++) {
              newarr += "[0]";
            }
            if (arrayClass.Dims > 1) {
              newarr += ")";
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
          return $"({TypeName(xType, wr, udt.tok)}) null";
        }
      } else if (cl is DatatypeDecl) {
        var s = FullTypeName(udt);
        var typeargs = "";
        if (udt.TypeArgs.Count != 0) {
          typeargs = $"<{TypeNames(udt.TypeArgs, wr, udt.tok)}>";
        }
        if (cl is TupleTypeDecl) {
          return $"({s}{typeargs})null";
        }
        return $"{s}.{typeargs}Default()";
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

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type> superClasses, Bpl.IToken tok, TargetWriter wr) {
      var filename = $"{ModulePath}/{name}.java";
      var w = wr.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Interface {name}");
      w.WriteLine($"// Dafny trait {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      w.WriteLine("import java.util.*;");
      w.WriteLine("import java.util.function.*;");
      w.WriteLine("import java.util.Arrays;");
      w.WriteLine("import java.lang.reflect.Array;");
      w.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
      EmitImports(w, out _);
      w.WriteLine();
      EmitSuppression(w); //TODO: Fix implementations so they do not need this suppression
      w.Write($"public interface {IdProtect(name)}");
      if (superClasses != null) {
        string sep = " implements ";
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
      w.WriteLine("import java.util.*;");
      w.WriteLine("import java.util.function.*;");
      w.WriteLine("import java.util.Arrays;");
      w.WriteLine("import java.lang.reflect.Array;");
      w.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
      EmitImports(w, out _);
      w.WriteLine();
      w.Write($"public class _Companion_{name}");
      var staticMemberWriter = w.NewBlock("");
      return new ClassWriter(this, instanceMemberWriter, staticMemberWriter);
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
      var wr = new TargetWriter();
      wr.WriteLine("package dafny;");
      wr.WriteLine();
      wr.WriteLine("@FunctionalInterface");
      wr.Write("public interface Function");
      wr.Write(i);
      wr.Write("<");
      for (int j = 0; j < i + 1; j++){
        wr.Write("T" + j);
        if (j != i)
          wr.Write(", ");
        else{
          wr.Write(">");
        }
      }
      var wrMembers = wr.NewBlock("");
      wrMembers.Write("public T" + i + " apply(");
      for (int j = 0; j < i; j++){
        wrMembers.Write("T" + j + " t" + j);
        if (j != i - 1)
          wrMembers.Write(", ");
      }
      wrMembers.WriteLine(");");

      using (StreamWriter sw = File.CreateText(path + "/Function" + i + ".java")) {
        sw.Write(wr.ToString());
      }
    }

    public void CompileDafnyArrays(string path) {
      foreach(int i in arrays){
        CreateDafnyArrays(i, path);
      }
    }

    protected override void CreateDefaultConstructor(TopLevelDeclWithMembers c, IClassWriter cw, List<TypeParameter> l) {
      var w = ((ClassWriter) cw).CreateConstructor(c, l);
      NeedsInputStrings.Add(c.CompileName);
      if (w != null) {
        foreach(TypeParameter t in l) {
          w.WriteLine($"this.s{t.Name} = s{t.Name};");
          w.WriteLine($"{t.Name.ToLower()} = ({t.Name}) Helpers.getDefault(s{t.Name});");
        }
      }
    }

    public void CreateDafnyArrays(int i, string path) {
      var wrTop = new TargetWriter();
      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();

      var wr = wrTop.NewBlock("public class Array" + i + "<T>");

      wr.Write("public T");
      for (int j = 0; j < i; j++) {
        wr.Write("[]");
      }
      wr.WriteLine(" elmts;");

      for (int j = 0; j < i; j++) {
        wr.WriteLine($"public int dims{j};");
      }

      wr.Write("public Array" + i + "(");
      for (int j = 0; j < i; j++) {
        wr.Write("int dims" + j + ", ");
      }
      wr.Write("T");
      for (int j = 0; j < i; j++) {
        wr.Write("[]");
      }
      using (var wrBody = wr.NewBlock(" elmts)")) {
        for (int j = 0; j < i; j++) {
          wrBody.WriteLine($"this.dims{j} = dims{j};");
        }
        wrBody.WriteLine("this.elmts = elmts;");
      }

      wr.WriteLine("public Array" + i + "() {}");

      using (StreamWriter sw = File.CreateText(path + "/Array" + i + ".java")) {
        sw.Write(wrTop.ToString());
      }
    }

    public void CompileArrayInits(string path) {
      foreach (int i in arrayinits) {
        CreateArrayInit(i, path);
      }
    }

    public void CreateArrayInit(int i, string path) {
      Contract.Requires(1 <= i);
      var wrTop = new TargetWriter();
      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();
      wrTop.WriteLine("import java.lang.reflect.Array;");
      wrTop.WriteLine();
      var wr = wrTop.NewBlock("public class ArrayInit" + i);
      EmitSuppression(wr);
      wr.Write("public static<T> T");
      for (int j = 0; j < i; j++) {
        wr.Write("[]");
      }
      wr.Write(" InitNewArray(T z");
      for (int j = 0; j < i; j++) {
        wr.Write($", int size{j}");
      }

      using (var body = wr.NewBlock(", Class cls)")) {
        body.Write("T");
        for (int j = 0; j < i; j++) {
          body.Write("[]");
        }
        body.Write(" a = (T");
        for (int j = 0; j < i; j++) {
          body.Write("[]");
        }
        body.Write(")Array.newInstance(cls");
        for (int j = 0; j < i; j++) {
          body.Write($", size{j}");
        }
        body.WriteLine(");");

        var forBodyWr = body;
        for (int j = 0; j < i; j++) {
          forBodyWr = forBodyWr.NewBlock($"for(int i{j} = 0; i{j} < size{j}; i{j}++)");
        }
        forBodyWr.Write("a");
        for (int j = 0; j < i; j++) {
          forBodyWr.Write($"[i{j}]");
        }
        forBodyWr.WriteLine(" = z;");

        body.WriteLine("return a;");
      }

      using (StreamWriter sw = File.CreateText(path + "/ArrayInit" + i + ".java")) {
        sw.Write(wrTop.ToString());
      }
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.WriteLine("continue TAIL_CALL_START;");
    }

    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("new ArrayList<>()");
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
        wr.Write($"for(Tuple{TargetTupleSize} {boundVar} : ");
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
        var typeName = TypeName(ct.Arg, wr, tok);
        return $"new dafny.DafnySet<{typeName}>({collName})";
      } else if (ct is MapType) {
        var mt = (MapType)ct;
        var domtypeName = TypeName(mt.Domain, wr, tok);
        var rantypeName = TypeName(mt.Range, wr, tok);
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

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, TargetWriter wr){
      var cw = CreateClass(IdName(nt), null, wr) as ClassWriter;
      var w = cw.StaticMemberWriter;
      if (nt.NativeType != null) {
        var nativeType = GetNativeTypeName(nt.NativeType);
        var wEnum = w.NewNamedBlock($"public static ArrayList<{nativeType}> IntegerRange(BigInteger lo, BigInteger hi)");
        wEnum.WriteLine($"ArrayList<{nativeType}> arr = new ArrayList<>();");
        var numberval = "intValue()";
        if (nativeType == "Byte" || nativeType == "Short")
          numberval = $"{nativeType.ToLower()}Value()";
        wEnum.WriteLine($"for (BigInteger j = lo; j.compareTo(hi) < 0; j.add(BigInteger.ONE)) {{ arr.add(new {nativeType}(j.{numberval})); }}");
        wEnum.WriteLine("return arr;");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new TargetWriter(w.IndentLevel, true);
        TrExpr(nt.Witness, witness, false);
        if (nt.NativeType == null) {
          cw.DeclareField("Witness", true, true, nt.BaseType, nt.tok, witness.ToString());
        } else {
          var nativeType = GetNativeTypeName(nt.NativeType);
          w.Write("public static {0} Witness = new {0}(", nativeType);
          w.Append(witness);
          if (nt.Witness.Type is IntType) {
            if(nativeType == "Short")
              w.Write(".shortValue()");
            else if (nativeType == "Byte")
              w.Write(".byteValue()");
            else w.Write(".intValue()");
          }
          w.WriteLine(");");
        }
      }
      return cw;
    }

    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr) {
      TypeName_SplitArrayName(elmtType, wr, tok, out var typeNameSansBrackets, out _);
      if (dimensions.Count > 1) {
        arrays.Add(dimensions.Count);
        wr.Write($"new Array{dimensions.Count}<>(");
        foreach (var dim in dimensions) {
          TrParenExpr(dim, wr, false);
          wr.Write(".intValue(), ");
        }
      }
      if (!mustInitialize) {
        if (elmtType is UserDefinedType type && type.ResolvedClass == null) {
          wr.Write($"({type.CompileName}");
          for (int i = 0; i < dimensions.Count; i++) {
            wr.Write("[]");
          }
          wr.Write(")");
          // Java class strings are written in the format "class x", so we use substring(6) to get the classname "x".
          wr.Write($"Array.newInstance(dafny.Helpers.getClassUnsafe(s{type.ToString()}.substring(6))");
          string pref = ", ";
          foreach (var dim in dimensions) {
            wr.Write(pref);
            TrParenExpr(dim, wr, false);
            pref = ".intValue(), ";
          }
          wr.Write(".intValue())");
        } else {
          var xType = elmtType.NormalizeExpand();
          if (xType is SetType) {
            Type argType = ((SetType)xType).Arg;
            if (ComplicatedTypeParameterForCompilation(argType)) {
              Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
            }
            wr.Write("(" + DafnySetClass + "<" + TypeName(argType, wr, tok) + ">");
            for (int i = 0; i < dimensions.Count; i++) {
              wr.Write("[]");
            }
            wr.Write(")");
            typeNameSansBrackets = DafnySetClass;
          } else if (xType is SeqType) {
            Type argType = ((SeqType)xType).Arg;
            if (ComplicatedTypeParameterForCompilation(argType)) {
              Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
            }
            wr.Write("(" + DafnySeqClass + "<" + TypeName(argType, wr, tok) + ">");
            for (int i = 0; i < dimensions.Count; i++) {
              wr.Write("[]");
            }
            wr.Write(")");
            typeNameSansBrackets = DafnySeqClass;

          } else if (xType is MultiSetType) {
            Type argType = ((MultiSetType)xType).Arg;
            if (ComplicatedTypeParameterForCompilation(argType)) {
              Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
            }
            wr.Write("(" + DafnyMultiSetClass + "<" + TypeName(argType, wr, tok) + ">");
            for (int i = 0; i < dimensions.Count; i++) {
              wr.Write("[]");
            }
            wr.Write(")");
            typeNameSansBrackets = DafnyMultiSetClass;
          } else if (xType is MapType) {
            Type domType = ((MapType)xType).Domain;
            Type ranType = ((MapType)xType).Range;
            if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) {
              Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost", wr);
            }
            wr.Write("(" + DafnyMapClass + "<" + TypeName(domType, wr, tok) + "," + TypeName(ranType, wr, tok) + ">");
            for (int i = 0; i < dimensions.Count; i++) {
              wr.Write("[]");
            }
            wr.Write(")");
            typeNameSansBrackets = DafnyMapClass;
          }
          wr.Write($"new {typeNameSansBrackets}");
          string prefix = "[";
          foreach (var dim in dimensions) {
            wr.Write(prefix);
            TrParenExpr(dim, wr, false);
            prefix = ".intValue()][";
          }
          wr.Write(".intValue()]");
        }
      } else {
        arrayinits.Add(dimensions.Count);
        wr.Write($"ArrayInit{dimensions.Count}.InitNewArray({DefaultValue(elmtType, wr, tok)}");
        string prefix = ", ";
        foreach (var dim in dimensions) {
          wr.Write(prefix);
          TrParenExpr(dim, wr, false);
          prefix = ".intValue(), ";
        }
        typeNameSansBrackets = elmtType.AsTypeParameter != null ? $"dafny.Helpers.getClassUnsafe(s{typeNameSansBrackets}.substring(6))" : $"{typeNameSansBrackets}.class";
        wr.Write($".intValue(), {typeNameSansBrackets})");
      }
      if (dimensions.Count > 1) {
        wr.Write(")");
      }
    }

    protected override int EmitRuntimeTypeDescriptorsActuals(List<Type> typeArgs, List<TypeParameter> formals, Bpl.IToken tok, bool useAllTypeArgs, TargetWriter wr) {
      var sep = "";
      var c = 0;
      for (int i = 0; i < typeArgs.Count; i++) {
        var actual = typeArgs[i];
        var formal = formals[i];
        if (useAllTypeArgs || formal.Characteristics.MustSupportZeroInitialization) {
          SplitType(TypeName(actual, wr, tok), out _, out var n);
          if (actual.IsDatatype && !(actual.AsDatatype is TupleTypeDecl)) {
            wr.Write($"{sep}{n}.defaultInstanceName");
          } else if (actual.IsTypeParameter){
            wr.Write($"s{n}");
          } else{
            wr.Write($"{sep}{n}.class.toString()");
          }
          sep = ", ";
          c++;
        }
      }
      return c;
    }
    protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs,
      List<Type> boundTypes, Type resultType, Bpl.IToken resultTok, bool inLetExprBody, TargetWriter wr){
      if (boundTypes.Count != 1) {
        functions.Add(boundTypes.Count);
      }
      wr.Write("((Function{0}<{1}{2}>)", boundTypes.Count != 1 ? boundTypes.Count.ToString() : "", Util.Comma("", boundTypes, t => TypeName(t, wr, resultTok) + ", "), TypeName(resultType, wr, resultTok));
      wr.Write($"({Util.Comma(boundVars)}) -> ");
      var w = wr.Fork();
      wr.Write(").apply");
      TrExprList(arguments, wr, inLetExprBody);
      return w;
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      return wr.NewNamedBlock($"for (BigInteger {indexVar} = BigInteger.ZERO; {indexVar}.compareTo(BigInteger.valueOf({bound})) < 0; {indexVar} = {indexVar}.add(BigInteger.ONE))");
    }

    protected override string GetHelperModuleName() => "dafny.Helpers";

    protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr){
      wr.WriteLine("new ArrayList<>();");
    }

    protected override void AddTupleToSet(int i) {
      tuples.Add(i);
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr) {
      wr.Write($"{ingredients}.add(new Tuple");
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
      wr.Write("((BigInteger)");
      var w = wr.Fork();
      wr.Write(").intValue()");
      return w;
    }

    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr) {
      return wr.NewNamedBlock($"for (BigInteger {indexVar} = BigInteger.valueOf({start}); ; {indexVar} = {indexVar}.multiply(new BigInteger(\"2\")))");
    }

    protected override void EmitIsZero(string varName, TargetWriter wr) {
      wr.Write($"{varName}.equals(BigInteger.ZERO)");
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr) {
      wr.WriteLine($"{varName} = {varName}.subtract(BigInteger.ONE);");
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr) {
      wr.WriteLine($"{varName} = {varName}.add(BigInteger.ONE);");
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      wr.Write("Arrays.asList");
      TrParenExpr(e, wr, inLetExprBody);
    }

    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write($"((Function<BigInteger, {TypeName(resultType, wr, resultTok)}>)(({bvName}) ->");
      var w = wr.NewBigExprBlock("", $")).apply(BigInteger.valueOf({source}))");
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
      wr.Write($"{DafnySeqClass}.Create(");
      TrExpr(expr.N, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(expr.Initializer, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr) {
      if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // (int or bv) -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          wr.Write("new dafny.BigRational(");
          if (AsNativeType(e.E.Type) != null) {
            wr.Write("BigInteger.valueOf");
          }
          TrParenExpr(e.E, wr, inLetExprBody);
          if (!e.E.Type.IsIntegerType) {
            wr.Write(".intValue()");
          }
          wr.Write(", BigInteger.ONE)");
        } else if (e.ToType.IsCharType) {
          wr.Write("dafny.Helpers.createCharacter(");
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".intValue()");
          wr.Write(")");
        } else {
          // (int or bv or char) -> (int or bv or ORDINAL)
          var fromNative = AsNativeType(e.E.Type);
          var toNative = AsNativeType(e.ToType);
          if (fromNative == null && toNative == null) {
            if (e.E.Type.IsCharType) {
              // char -> big-integer (int or bv or ORDINAL)
              wr.Write("BigInteger.valueOf");
              TrParenExpr(e.E, wr, inLetExprBody);
            } else {
              // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
              TrExpr(e.E, wr, inLetExprBody);
            }
          } else if (fromNative != null && toNative == null) {
            // native (int or bv) -> big-integer (int or bv)
            wr.Write("BigInteger.valueOf(");
            TrParenExpr(e.E, wr, inLetExprBody);
            if (!e.E.Type.IsIntegerType) {
              wr.Write(".intValue()");
            }
            wr.Write(")");
          } else {
            GetNativeInfo(toNative.Sel, out var toNativeName, out var toNativeSuffix, out var toNativeNeedsCast);
            // any (int or bv) -> native (int or bv)
            // A cast would do, but we also consider some optimizations
            wr.Write($"new {toNativeName}(");
            var literal = PartiallyEvaluate(e.E);
            UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
            MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
            if (literal != null) {
              // Optimize constant to avoid intermediate BigInteger
              wr.Write("(" + literal + toNativeSuffix + ")");
            } else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
              if (u.Type.AsCollectionType is MultiSetType) {
                TrParenExpr("", u.E, wr, inLetExprBody);
                wr.Write(".cardinality()");
              } else if (u.Type.AsCollectionType is SetType || u.Type.AsCollectionType is MapType) {
                TrParenExpr("BigInteger.valueOf(", u.E, wr, inLetExprBody);
                wr.Write(".size())");
              } else if (u.Type.IsArrayType) {
                TrParenExpr("BigInteger.valueOf(", u.E, wr, inLetExprBody);
                wr.Write(".length)");
              } else {
                TrParenExpr("BigInteger.valueOf(", u.E, wr, inLetExprBody);
                wr.Write(".length())");
              }
            } else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
              // Optimize .Length to avoid intermediate BigInteger
              TrParenExpr(m.Obj, wr, inLetExprBody);
              wr.Write(".length");
            } else {
              // no optimization applies; use the standard translation
              TrParenExpr(e.E, wr, inLetExprBody);
            }
            wr.Write(")");
          }
        }
      } else if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
        Contract.Assert(AsNativeType(e.E.Type) == null);
        if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
          // real -> real
          Contract.Assert(AsNativeType(e.ToType) == null);
          TrExpr(e.E, wr, inLetExprBody);
        } else {
          // real -> (int or bv)
          if (AsNativeType(e.ToType) != null) {
            wr.Write($"({GetNativeTypeName(AsNativeType(e.ToType))})");
          }
          TrParenExpr(e.E, wr, inLetExprBody);
          wr.Write(".ToBigInteger()");
        }
      } else {
        Contract.Assert(e.E.Type.IsBigOrdinalType);
        Contract.Assert(e.ToType.IsNumericBased(Type.NumericPersuation.Int));
        // identity will do
        TrExpr(e.E, wr, inLetExprBody);
      }
    }

    protected override BlockTargetWriter CreateStaticMain(IClassWriter cw) {
      var wr = ((ClassWriter) cw).StaticMemberWriter;
      return wr.NewBlock("public static void Main(string[] args)");
    }

    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write("dafny.Helpers.Let(");
      wr.Write($"{source}, {bvName} -> ");
      var w = wr.Fork();
      wr.Write(")");
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType, Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write("dafny.Helpers.Let(");
      TrExpr(source, wr, inLetExprBody);
      wr.Write($", {bvName} -> ");
      var w = wr.Fork();
      wr.Write(")");
      return w;
    }

    protected override string GetQuantifierName(string bvType) {
      return "dafny.Helpers.Quantifier";
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
