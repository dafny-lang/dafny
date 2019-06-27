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
      : base(reporter){ }

    public override String TargetLanguage => "Java";
    protected new readonly string DafnySetClass = "DafnyClasses.DafnySet";
    protected new readonly string DafnyMultiSetClass = "DafnyClasses.DafnyMultiset";
    protected new readonly string DafnySeqClass = "DafnyClasses.DafnySequence";
    protected readonly string DafnyStringClass = "DafnyClasses.DafnyString";
    protected new readonly string DafnyMapClass = "DafnyClasses.Dafnymap";

    private String ModuleName;
    private String MainModuleName;
    private HashSet<int> tuples = new HashSet<int>();

    private static List<Import> StandardImports =
      new List<Import>{
        new Import{Name = "_dafny", Path = "DafnyClasses"},
      };
    private readonly List<Import> Imports = new List<Import>(StandardImports);

    //RootImportWriter writes additional imports to the main file.
    private TargetWriter RootImportWriter;
    private TargetWriter RootImportDummyWriter; // TODO: Remove if not deemed necessary.

    private struct Import{
      public string Name, Path;
      public bool SuppressDummy; // TODO: Not sure what this does, might not need it? (Copied from Compiler-go.cs)
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    protected override bool SupportsAmbiguousTypeDecl => false;
    protected override bool SupportsProperties => false;
    protected override bool NeedsWrappersForInheritedFields => false;
    protected override bool FieldsInTraits => false;

    protected override void DeclareSpecificOutCollector(string collectorVarName, TargetWriter wr, int outCount,
      Method m){
      if (outCount > 1){
        wr.Write("Tuple{0} {1} = ", outCount, collectorVarName);
      }
      else {
        for (int i = 0; i < m.Outs.Count; i++) {
          Formal p = m.Outs[i];
          if (!p.IsGhost) {
            wr.Write("{0} {1} = ", TypeName(p.Type, wr, p.tok), collectorVarName);
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
      else{
        for (var i = 0; i < actualOutParamNames.Count; i++){
          wr.WriteLine("{0} = ({3}) {1}.dtor__{2}();", actualOutParamNames[i], outCollector, i,
            TypeName(actualOutParamTypes[i], wr, tok));
        }
      }
    }

    protected override void EmitHeader(Program program, TargetWriter wr){
      wr.WriteLine("// Dafny program {0} compiled into Java", program.Name);
      ModuleName = MainModuleName = HasMain(program, out _) ? "main" : Path.GetFileNameWithoutExtension(program.Name);
      wr.WriteLine();
      // Keep the import writers so that we can import subsequent modules into the main one
      EmitImports(wr, out RootImportWriter);
      wr.WriteLine();
    }

    // Only exists to make sure method is overriden, actual Emit occurs in DafnyDriver.cs
    protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr){ }

    // Creates file header for each module's file.
    void EmitModuleHeader(TargetWriter wr){
      wr.WriteLine("// Package {0}", ModuleName);
      wr.WriteLine("// Dafny module {0} compiled into Java", ModuleName);
      wr.WriteLine();
      wr.WriteLine("package {0};", ModuleName);
      wr.WriteLine();
      wr.WriteLine("import java.util.*;");
      wr.WriteLine("import java.util.function.*;");
      wr.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
      EmitImports(wr, out _);
      wr.WriteLine();
    }

    public override void EmitCallToMain(Method mainMethod, TargetWriter wr){
      var companion = TypeName_Companion(mainMethod.EnclosingClass as ClassDecl, wr, mainMethod.tok);
      var wBody = wr.NewNamedBlock("public static void main(String[] args)");
      wBody.WriteLine("\t{0}.{1}();", companion, IdName(mainMethod));
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
      var path = import.Path;

      importWriter.WriteLine("import {0}.*;", path);
    }

    protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern, string /*?*/ libraryName, TargetWriter wr) {
      if (isDefault) {
        // Fold the default module into the main module
        return wr;
      }
      string pkgName;
      if (libraryName != null) {
        pkgName = libraryName;
      } else {
        pkgName = IdProtect(moduleName);
      }
      var import = new Import{ Name=moduleName, Path=pkgName };
      var filename = string.Format("{0}/{0}.java", pkgName);
      var w = wr.NewFile(filename);
      ModuleName = moduleName;
      EmitModuleHeader(w);
      AddImport(import);
      return w;
    }
    
    private void AddImport(Import import){
      EmitImport(import, RootImportWriter);
      Imports.Add(import);
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
            
      public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
        return Compiler.CreateMethod(m, createBody, Writer(m.IsStatic));
      }
      public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
        return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic));
      }
            
      // TODO: Decide if we need to make the getters/setters, since all fields are public anyway.
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
        var w = wr.NewBlock(null, null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        return w;
      } else {
        wr.WriteLine(";");
        return null;
      }
    }

    public BlockTargetWriter /*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic,
      bool createBody, out TargetWriter setterWriter, TargetWriter wr) {
      wr.Write("public {0}{1} get_{2}()", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      BlockTargetWriter wGet = null;
      if (createBody) {
        wGet = wr.NewBlock(null, null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      } else {
        wr.WriteLine(";");
      }
      wr.Write("public {0}void set_{1}({2} value)", isStatic? "static " : "", name, TypeName(resultType, wr, tok));
      if (createBody) {
        setterWriter = wr.NewBlock(null, null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      } else {
        wr.WriteLine(";");
        setterWriter = null;
      }
      return wGet;
    }
        
    protected BlockTargetWriter CreateMethod(Method m, bool createBody, TargetWriter wr) {
      string targetReturnTypeReplacement = null;
      int nonGhostOuts = 0;
      foreach (var p in m.Outs) {
        if (!p.IsGhost) {
          nonGhostOuts += 1;
        }
      }
      if (nonGhostOuts == 1) {
        targetReturnTypeReplacement = TypeName(m.Outs[0].Type, wr, m.Outs[0].tok);
      } else if (nonGhostOuts > 1) {
        targetReturnTypeReplacement = "Tuple" + nonGhostOuts;
      }
      wr.Write("{0}{1}", createBody ? "public " : "", m.IsStatic ? "static " : "");
      if (m.TypeArgs.Count != 0) {
        wr.Write("<{0}> ", TypeParameters(m.TypeArgs));
      }
      wr.Write("{0} {1}", targetReturnTypeReplacement ?? "void", IdName(m));
      wr.Write("(");
      WriteFormals("", m.Ins, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      } else {
        var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        if (m.IsTailRecursive) {
          w = w.NewBlock("TAIL_CALL_START: while (true)");
        }
        if (!m.Body.Body.OfType<ReturnStmt>().Any() && (nonGhostOuts > 0 || m.IsTailRecursive)) { // If method has out parameters or is tail-recursive but no explicit return statement in Dafny
          var r = new TargetWriter(w.IndentLevel);
          EmitReturn(m.Outs, r);
          w.BodySuffix = r.ToString();
        }
        return w;
      }
    }
    
    protected BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs,
      List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member,
      TargetWriter wr) {
      wr.Write("{0}{1}", createBody ? "public " : "", isStatic ? "static " : "");
      if (typeArgs != null && typeArgs.Count != 0) {
        wr.Write("<{0}>", TypeParameters(typeArgs));
      }
      wr.Write("{0} {1}(", TypeName(resultType, wr, tok), name);
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
    
    protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, TargetWriter wr) {
      wr.WriteLine("public {0}{1} {2} = {3};", isStatic ? "static " : "", TypeName(type, wr, tok), name, (rhs != null) ? rhs : DefaultValue(type, wr, tok));
    }

    string TypeParameters(List<TypeParameter> targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      return Util.Comma(targs, tp => IdName(tp));
    }

    // Function copied and pasted from Compiler-Csharp.cs, will be modified later if deemed necessary.
    protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl/*?*/ member = null) { 
      Contract.Ensures(Contract.Result<string>() != null); 
      Contract.Assume(type != null);  // precondition; this ought to be declared as a Requires in the superclass
            
      var xType = type.NormalizeExpand(); 
      if (xType is TypeProxy) { 
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        return "object"; 
      }
      if (xType is BoolType) { 
        return "Boolean"; 
      } else if (xType is CharType) { 
        return "Character"; 
      } else if (xType is IntType || xType is BigOrdinalType) { 
        return "BigInteger"; 
      } else if (xType is RealType) { 
        return "BigDecimal"; //TODO: change the data structure to match the one in DafnyRuntime.java
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
        Type elType = UserDefinedType.ArrayElementType(xType);
        string typeNameSansBrackets, brackets; 
        TypeName_SplitArrayName(elType, wr, tok, out typeNameSansBrackets, out brackets); 
        return typeNameSansBrackets + TypeNameArrayBrackets(at.Dims) + brackets; 
      } else if (xType is UserDefinedType) { 
        var udt = (UserDefinedType)xType; 
        var s = FullTypeName(udt, member); 
        var cl = udt.ResolvedClass; 
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "DafnyULong";
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

        if (argType is CharType || argType is InferredTypeProxy && ((InferredTypeProxy)argType).T is CharType){
          return DafnyStringClass;
        }
        else{
          return DafnySeqClass + "<" + TypeName(argType, wr, tok) + ">"; 
        }
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

    // Copied from Compiler-C#, seemed most applicable to Java compiler due to similar data types.
    // TODO: verify, change if necessary to match Java language specifications
    protected override string FullTypeName(UserDefinedType udt, MemberDecl /*?*/ member = null) {
      Contract.Assume(udt != null); // precondition; this ought to be declared as a Requires in the superclass
      if (udt is ArrowType) {
        return ArrowType.Arrow_FullCompileName;
      }
      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      }
      else{
        return IdProtect(cl.CompileName);
      }
    }
    
    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam, TextWriter wr) {
      if (isInParam) {
        wr.Write("{0}{1} {2}", prefix, TypeName(type, wr, tok), name);
        return true;
      } else {
        return false;
      }
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

    protected override IClassWriter CreateClass(string name, bool isExtern, string /*?*/ fullPrintName,
      List<TypeParameter> /*?*/ typeParameters, List<Type> /*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      if (!isExtern) {
        var filename = string.Format("{1}/{0}.java", name, ModuleName);
        var w = wr.NewFile(filename);
        w.WriteLine("// Class {0}", name);
        w.WriteLine("// Dafny class {0} compiled into Java", name);
        w.WriteLine("package {0};", ModuleName);
        w.WriteLine();
        w.WriteLine("import java.util.*;");
        w.WriteLine("import java.util.function.*;");
        w.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
        EmitImports(w, out _);
        w.WriteLine();
        w.Write("public class {0}", name);
        if (typeParameters != null && typeParameters.Count != 0) {
          w.Write("<{0}>", TypeParameters(typeParameters));
        }
        // Since Java does not support multiple inheritance, we are assuming a list of "superclasses" is a list of interfaces
        if (superClasses != null) {
          string sep = " implements ";
          foreach (var trait in superClasses) {
            w.Write("{0}{1}", sep, TypeName(trait, w, tok));
            sep = ", ";
          }
        }
        return new ClassWriter(this, w.NewBlock(""));
      }
      return new ClassWriter(this, new BlockTargetWriter(0, "", ""));
    }
        
    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      } else if (e.Value == null) {
        wr.Write("({0}) null", TypeName(e.Type, wr, e.tok));
      } else if (e.Value is bool) {
        wr.Write((bool)e.Value ? "true" : "false");
      } else if (e is CharLiteralExpr) {
        wr.Write("'{0}'", (string) e.Value);
      } else if (e is StringLiteralExpr) {
        var str = (StringLiteralExpr)e;
        wr.Write("new DafnyString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      } else if (AsNativeType(e.Type) != null) {
        string literalSuffix;
        GetNativeInfo(AsNativeType(e.Type).Sel, out _, out literalSuffix, out _);
        wr.Write((BigInteger)e.Value + literalSuffix);
      } else if (e.Value is BigInteger i) {
        wr.Write("new BigInteger(\"{0}\")", i);
      } else if (e.Value is Basetypes.BigDec n) {
        wr.Write("new BigDecimal(\"{0}E{1}\")", n.Mantissa, n.Exponent);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
      }
    }
        
    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      if (!isVerbatim) {
        wr.Write("\"{0}\"", str);
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

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix,
      out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (sel) {
        case NativeType.Selection.Byte:
          name = "Dafny.DafnyByte";
          break;
        case NativeType.Selection.SByte:
          name = "Byte";
          break;
        case NativeType.Selection.UShort:
          name = "Dafny.DafnyUShort";
          break;
        case NativeType.Selection.Short:
          name = "Short";
          break;
        case NativeType.Selection.UInt:
          name = "Dafny.DafnyUInt";
          break;
        case NativeType.Selection.Int:
          name = "Integer";
          break;
        case NativeType.Selection.ULong:
          name = "Dafny.DafnyULong";
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
      wr.Write("{0} {1}", type != null ? TypeName(type, wr, tok) : "Object", name);
      if (leaveRoomForRhs){
        Contract.Assert(rhs == null); // follows from precondition
      }
      else if (rhs != null){
        wr.WriteLine(" = {0};", rhs);
      } else {
        wr.WriteLine(";");
      }
    }
        
    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("new {0}", TypeName(ct, wr, tok));
      TrExprList(elements, wr, inLetExprBody);
    }

    protected void TrExprList(List<Expression> exprs, TargetWriter wr, bool inLetExprBody, Type/*?*/ type = null) {
      Contract.Requires(cce.NonNullElements(exprs));
      wr.Write("(Arrays.asList(");
      string sep = "";
      foreach (Expression e in exprs) {
        wr.Write(sep);
        TargetWriter w;
        if (type != null) {
          w = wr.Fork();
          w = EmitCoercionIfNecessary(e.Type, type, e.tok, w);
        } else {
          w = wr;
        }
        TrExpr(e, w, inLetExprBody);
        sep = ", ";
      }
      wr.Write("))");
    }
        
    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements, bool inLetExprBody, TargetWriter wr) {
      wr.Write("new DafnyClasses.Dafnymap<>() {{{{\n");
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
          compiledName = (string)idParam;
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          compiledName = idParam == null ? "length" : "dims[" + (int)idParam + "]";
          if (id == SpecialField.ID.ArrayLength) {
            preString = "new BigInteger(";
            postString = ")";
          }
          break;
        case SpecialField.ID.Floor:
          compiledName = "toBigInteger()";
          break;
        case SpecialField.ID.IsLimit:
          preString = "Dafny.BigOrdinal.IsLimit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = "Dafny.BigOrdinal.IsSucc(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = "Dafny.BigOrdinal.Offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = "Dafny.BigOrdinal.IsNat(";
          postString = ")";
          break;
        case SpecialField.ID.Keys:
          compiledName = "keySet()";
          break;
        case SpecialField.ID.Values:
          compiledName = "values()";
          break;
        case SpecialField.ID.Items:
          compiledName = "entrySet()";
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

    protected override TargetWriter EmitMemberSelect(MemberDecl member, bool isLValue, Type expectedType, TargetWriter wr) {
      var wSource = wr.Fork();
      if (isLValue && member is ConstantField) {
        wr.Write(".{0}", member.CompileName);
      } else if (!isLValue && member is SpecialField sf) {
        string compiledName, preStr, postStr;
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out preStr, out postStr);
        if (compiledName.Length != 0){
          wr.Write(".{0}{1}{2}", MemberSelectObjIsTrait && !sf.IsStatic ? "get_" : "", compiledName,
            (MemberSelectObjIsTrait && !sf.IsStatic) || member.EnclosingClass is DatatypeDecl ? "()" : "");
        }
      } else if (!isLValue && MemberSelectObjIsTrait && !member.IsStatic) {
        wr.Write(".get_{0}()", IdName(member));
      } else if (isLValue && MemberSelectObjIsTrait && !member.IsStatic) { 
        wr.Write(".set_{0}(", IdName(member));
      } else {
        wr.Write(".{0}", IdName(member));
      }
      return wSource;
    }
    
    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, TargetWriter wr){
      wr.Write("{0}.is_{1}()", source, ctor.CompileName);
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl member){
      var udt = type as UserDefinedType;
      if (udt != null && udt.ResolvedClass is TraitDecl) {
        string s = udt.FullCompanionCompileName;
        Contract.Assert(udt.TypeArgs.Count == 0);  // traits have no type parameters
        return s;
      } else {
        return TypeName(type, wr, tok, member);
      }
    }
        
    protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      if (indices.Count == 1) {
        wr.Write("[(int) {0}]", indices[0]);
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write("[(int) {0}]", index);
        }
      }
      return w;
    }

    protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count);  // follows from precondition
      var w = wr.Fork();
      if (indices.Count == 1) {
        wr.Write("[(int) ");
        TrParenExpr(indices[0], wr, inLetExprBody);
        wr.Write("]");
      } else {
        wr.Write(".elmts");
        foreach (var index in indices) {
          wr.Write("[(int) ");
          TrParenExpr(index, wr, inLetExprBody);
          wr.Write("]");
        }
      }
      return w;
    }
        
    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody, TargetWriter wr) {
      if (fromArray) {
        wr.Write("new DafnySequence(Arrays.asList(Arrays.copyOfRange(");
      }
      TrParenExpr(source, wr, inLetExprBody);
      if (fromArray) {
        wr.Write(", ");
        if (lo != null) {
          TrExpr(lo, wr, inLetExprBody);
        } else {
          wr.Write("0");
        }
        wr.Write(", ");
        if (hi != null) {
          TrExpr(hi, wr, inLetExprBody);
        } else {
          TrParenExpr(source, wr, inLetExprBody);
          wr.Write(".length");
        }
        wr.Write(")))");
      } else {
        if (lo != null && hi != null) {
          wr.Write(".subsequence(");
          wr.Write(((BigInteger)((LiteralExpr)lo).Value).ToString());
          wr.Write(", ");
          wr.Write(((BigInteger)((LiteralExpr)lo).Value).ToString());
          wr.Write(")");
        }
        else if (lo != null) {
          wr.Write(".drop(");
          wr.Write(((BigInteger)((LiteralExpr)lo).Value).ToString());
          wr.Write(")");
        }
        else if (hi != null) {
          wr.Write(".take(");
          wr.Write(((BigInteger)((LiteralExpr)hi).Value).ToString());
          wr.Write(")");
        }
      }
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, TargetWriter wr) {
      // Taken from C# compiler, assuming source is a DafnySequence type.
      TrParenExpr(source, wr, inLetExprBody);
      if (source.Type.AsCollectionType.CollectionTypeName.Equals("multiset")){
        TrParenExpr(".multiplicity", index, wr, inLetExprBody);
      }
      else if (source.Type.AsCollectionType.CollectionTypeName.Equals("map")){
        TrParenExpr(".get", index, wr, inLetExprBody);
      }
      else if (source.Type.AsCollectionType.CollectionTypeName.Equals("seq") ||
          source.Type.AsCollectionType.CollectionTypeName.Equals("string")){
        wr.Write(".select(");
        wr.Write(((BigInteger)((LiteralExpr)index).Value).ToString());
        wr.Write(")");
      }
      else{
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
      if (source.Type.AsCollectionType.CollectionTypeName.Equals("map")){
        wr.Write(".put(");
        TrExpr(index, wr, inLetExprBody);
      }
      else{
        wr.Write(".update(");
        if (source.Type.AsCollectionType.CollectionTypeName.Equals("seq") ||
            source.Type.AsCollectionType.CollectionTypeName.Equals("string")){
          wr.Write(((BigInteger)((LiteralExpr)index).Value).ToString());
        }
        else{
          TrExpr(index, wr, inLetExprBody);
        }
      }
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
      EmitShift(e0, e1, isRotateLeft ? "<<" : ">>", isRotateLeft, nativeType, true, wr, inLetExprBody, tr);
      wr.Write(")");
      wr.Write (" | ");
      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? ">>" : "<<", !isRotateLeft, nativeType, false, wr, inLetExprBody, tr);
      wr.Write(")");
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
      wr.Write(" {0} ", op);
      if (!firstOp) {
        wr.Write("({0} - ", bv.Width);
      }
      wr.Write("(int) (");
      tr(e1, wr, inLetExprBody);
      wr.Write(")");
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
        wr.Write("({0})((", nativeName);
      }
      // --- Middle
      var middle = wr.Fork();
      // --- After
      // do the truncation, if needed
      if (bvType.NativeType == null) {
        wr.Write(") & ((new BigInteger(1) << {0}) - 1))", bvType.Width);
      } else {
        if (bvType.NativeType.Bitwidth != bvType.Width) {
          // print in hex, because that looks nice
          wr.Write(") & ({2})0x{0:X}{1})", (1UL << bvType.Width) - 1, literalSuffix, nativeName);
        } else {
          wr.Write("))");  // close the parentheses for the cast
        }
      }
      return middle;
    }
    
    protected override void DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
      
      if (dt is TupleTypeDecl){
        tuples.Add(((TupleTypeDecl) dt).Dims);
      }
      else{
        CompileDatatypeBase(dt, wr);
        CompileDatatypeConstructors(dt, wr);
      }
    }
    
    void CompileDatatypeBase(DatatypeDecl dt, TargetWriter wr) {
      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);
      string DtT_TypeArgs = "";
      if (dt.TypeArgs.Count != 0) {
        DtT_TypeArgs = "<" + TypeParameters(dt.TypeArgs) + ">";
        DtT += DtT_TypeArgs;
        DtT_protected += DtT_TypeArgs;
      }
      var filename = string.Format("{1}/{0}.java", dt, ModuleName);
      wr = wr.NewFile(filename);
      wr.WriteLine("// Class {0}", DtT_protected);
      wr.WriteLine("// Dafny class {0} compiled into Java", DtT_protected);
      wr.WriteLine("package {0};", ModuleName);
      wr.WriteLine();
      wr.WriteLine("import java.util.*;");
      wr.WriteLine("import java.util.function.*;");
      wr.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
      EmitImports(wr, out _);
      wr.WriteLine();
      // from here on, write everything into the new block created here:
      wr = wr.NewNamedBlock("public{0} class {1}", dt.IsRecordType ? "" : " abstract", DtT_protected);
      // constructor
      if (dt.IsRecordType) {
        DatatypeFieldsAndConstructor(dt.Ctors[0], 0, wr);
      } else {
        wr.WriteLine("public {0}() {{ }}", dt);
      }
      wr.WriteLine("static {0} theDefault;", dt);
      using (var w = wr.NewNamedBlock("public static {0} Default()", IdName(dt))) {
        var wIf = EmitIf("theDefault == null", false, w);
        wIf.Write("theDefault = ");
        DatatypeCtor defaultCtor;
        if (dt is IndDatatypeDecl) {
          defaultCtor = ((IndDatatypeDecl)dt).DefaultCtor;
        } else {
          defaultCtor = ((CoDatatypeDecl) dt).Ctors[0];
        }
        wIf.Write("new {0}(", DtCtorName(defaultCtor));
        string sep = "";
        foreach (Formal f in defaultCtor.Formals) {
          if (!f.IsGhost) {
            wIf.Write("{0}{1}", sep, DefaultValue(f.Type, wIf, f.tok));
            sep = ", ";
          }
        }
        wIf.Write(");");
        wIf.WriteLine();
        w.WriteLine("return theDefault;");
      }
      wr.WriteLine("public static {0} _DafnyDefaultValue() {{ return {0}.Default(); }}", dt);
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
          wr.WriteLine("public boolean is_{0}() {{ return true; }}", ctor.CompileName);
        } else {
          wr.WriteLine("public boolean is_{0}() {{ return this instanceof {1}_{0}; }}", ctor.CompileName, dt.CompileName);
        }
      }
      if (dt is CoDatatypeDecl) {
        wr.WriteLine("public abstract {0} Get();", DtT_protected);
      }
      if (dt.HasFinitePossibleValues) {
        Contract.Assert(dt.TypeArgs.Count == 0);
        var w = wr.NewNamedBlock("public static ArrayList<{0}> AllSingletonConstructors()", DtT_protected);
        string arraylist = "singleton_iterator";
        w.WriteLine("ArrayList<{0}> {1} = new ArrayList<>();", DtT_protected, arraylist);
        foreach (var ctor in dt.Ctors) {
          Contract.Assert(ctor.Formals.Count == 0);
          w.WriteLine("{2}.add(new {0}_{1}());", DtT_protected, ctor.CompileName, arraylist);
        }
        w.WriteLine("return {0};", arraylist);
      }
      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors) {
          if (dtor.EnclosingCtors[0] == ctor) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName){
              using (var wDtor = wr.NewNamedBlock("public {0} dtor_{1}()", TypeName(arg.Type, wr, arg.tok),
                arg.CompileName)){
                if (dt.IsRecordType){
                  wDtor.WriteLine("return this.{0};", IdName(arg));
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
                  wDtor.WriteLine("return (({0}_{1}{2})d).{3}; ", dt.CompileName, dtor.EnclosingCtors[n-1].CompileName, DtT_TypeArgs, IdName(arg));
                }
              }
            }
          }
        }
      }
    }

    void CompileDatatypeConstructors(DatatypeDecl dt, TargetWriter wrx) {
      Contract.Requires(dt != null);
      string typeParams = dt.TypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeParameters(dt.TypeArgs));
      if (dt.IsRecordType) {
        // There is only one constructor, and it is populated by CompileDatatypeBase
        return;
      }
      int constructorIndex = 0; // used to give each constructor a different name
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var filename = string.Format("{1}/{0}.java", DtCtorDeclarationName(ctor), ModuleName);
        var wr = wrx.NewFile(filename);
        wr.WriteLine("// Class {0}", DtCtorDeclarationName(ctor, dt.TypeArgs));
        wr.WriteLine("// Dafny class {0} compiled into Java", DtCtorDeclarationName(ctor, dt.TypeArgs));
        wr.WriteLine("package {0};", ModuleName);
        wr.WriteLine();
        wr.WriteLine("import java.util.*;");
        wr.WriteLine("import java.util.function.*;");
        wr.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
        EmitImports(wr, out _);
        wr.WriteLine();
        var w = wr.NewNamedBlock("public class {0} extends {1}{2}", DtCtorDeclarationName(ctor, dt.TypeArgs), IdName(dt), typeParams);
        DatatypeFieldsAndConstructor(ctor, constructorIndex, w);
        constructorIndex++;
      }
      
      if (dt is CoDatatypeDecl) {
        var filename = string.Format("{1}/{0}__Lazy.java", dt.CompileName, ModuleName);
        var wr = wrx.NewFile(filename);
        wr.WriteLine("// Class {0}__Lazy", dt.CompileName);
        wr.WriteLine("// Dafny class {0}__Lazy compiled into Java", dt.CompileName);
        wr.WriteLine("package {0};", ModuleName);
        wr.WriteLine();
        wr.WriteLine("import java.util.*;");
        wr.WriteLine("import java.util.function.*;");
        wr.WriteLine("import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
        EmitImports(wr, out _);
        wr.WriteLine();
        var w = wr.NewNamedBlock("public class {0}__Lazy extends {1}{2}", dt.CompileName, IdName(dt), typeParams);
        w.WriteLine("interface Computer {{ {0}{1} run(); }}", dt.CompileName, typeParams);
        w.WriteLine("Computer c;");
        w.WriteLine("{0}{1} d;", dt.CompileName, typeParams);
        w.WriteLine("public {0}__Lazy(Computer c) {{ this.c = c; }}", dt.CompileName);
        w.WriteLine("public {0}{1} Get() {{ if (c != null) {{ d = c.run(); c = null; }} return d; }}", dt.CompileName, typeParams);
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
          wr.WriteLine("public {0} {1};", TypeName(arg.Type, wr, arg.tok), FormalName(arg, i));
          i++;
        }
      }
      wr.Write("public {0}(", DtCtorDeclarationName(ctor));
      WriteFormals("", ctor.Formals, wr);
      using (var w = wr.NewBlock(")")) {
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            w.WriteLine("this.{0} = {0};", FormalName(arg, i));
            i++;
          }
        }
      }

      if (dt is CoDatatypeDecl) {
        string typeParams = dt.TypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeParameters(dt.TypeArgs));
        wr.WriteLine("public {0}{1} Get() {{ return this; }}", dt.CompileName, typeParams);
      }

      // Equals method
      using (var w = wr.NewBlock("\n@Override\npublic boolean equals(Object other)")) {
        w.WriteLine("if (this == other) return true;");
        w.WriteLine("if (other == null) return false;");
        w.WriteLine("if (getClass() != other.getClass()) return false;");
        if(ctor.Formals.Count > 0){string typeParams = dt.TypeArgs.Count == 0 ? "" : string.Format("<{0}>", TypeParameters(dt.TypeArgs));
          w.WriteLine("{0} o = ({0})other;", DtCtorDeclarationName(ctor, dt.TypeArgs));
          w.Write("return ");
          i = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              string nm = FormalName(arg, i);
              if(i!= 0)
                w.Write(" && ");
              w.Write("{0}.equals(o.{0})", nm);
              i++;
            }
          }
          w.WriteLine(";");
        }
        else{
          w.WriteLine("return true;");
        }
      }

//      // GetHashCode method (Uses the djb2 algorithm)
      using (var w = wr.NewBlock("\n@Override\npublic int hashCode()")) {
        w.WriteLine("long hash = 5381;");
        w.WriteLine("hash = ((hash << 5) + hash) + {0};", constructorIndex);
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            w.WriteLine("hash = ((hash << 5) + hash) + ((long)this.{0}.hashCode());", nm);
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
        if (dt is TupleTypeDecl tupleDt && ctor.Formals.Count == 0) {
          // here we want parentheses and no name
          w.WriteLine("return \"()\";");
        } else if (dt is CoDatatypeDecl) {
          w.WriteLine("return \"{0}\";", nm);
        } else {
          var tempVar = GenVarName("s", ctor.Formals);
          w.WriteLine("StringBuilder {0} = new StringBuilder();", tempVar);
          w.WriteLine("{0}.append(\"{1}\");", tempVar, nm);
          if (ctor.Formals.Count != 0) {
            w.WriteLine("{0}.append(\"(\");", tempVar);
            i = 0;
            foreach (var arg in ctor.Formals) {
              if (!arg.IsGhost) {
                if (i != 0) {
                  w.WriteLine("{0}.append(\", \");", tempVar);
                }
                w.WriteLine("{0}.append(this.{1}.toString());", tempVar, FormalName(arg, i));
                i++;
              }
            }
            w.WriteLine("{0}.append(\")\");", tempVar);
          }
          w.WriteLine("return {0}.toString();", tempVar);
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
    string DtCtorName(DatatypeCtor ctor, List<TypeParameter> typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeParams != null && typeParams.Count != 0) {
        s += "<" + TypeParameters(typeParams) + ">";
      }
      return s;
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
      } else {
        return "create_" + ctor.CompileName;
      }
    }
    
    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Write("System.out.print(");
      TrExpr(arg, wr, false);
      wr.WriteLine(");");
    }
    
    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public static string PublicIdProtect(string name) {
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
          outputWriter.WriteLine("Unrecognized file as extra input for Java compilation: {0}", otherFileName);
          return false;
        }
        if (!CopyExternLibraryIntoPlace(mainProgram: targetFilename, externFilename: otherFileName, outputWriter: outputWriter)) {
          return false;
        }
      }
      var files = new List<string>();
      foreach (string file in Directory.EnumerateFiles(Path.GetDirectoryName(targetFilename), "*.java", SearchOption.AllDirectories)) {
        files.Add(file);
      }
      foreach (var file in files) {
        var psi = new ProcessStartInfo("javac", file);
        psi.CreateNoWindow = true;
        psi.UseShellExecute = false;
        psi.WorkingDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
        psi.EnvironmentVariables["CLASSPATH"] = ".:" + Path.GetFullPath(Path.GetDirectoryName(targetFilename));
        var proc = Process.Start(psi);
        proc.WaitForExit();
        if (proc.ExitCode != 0) {
          throw new Exception("Error while compiling Java file " + file + ". Process exited with exit code " + proc.ExitCode);
        }
      }
      return true;
    }
    
    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string /*?*/ targetFilename, 
     ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {
      var psi = new ProcessStartInfo("java", Path.GetFileNameWithoutExtension(targetFilename));
      psi.CreateNoWindow = true;
      psi.UseShellExecute = false;
      psi.RedirectStandardOutput = true;
      psi.WorkingDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
      var proc = Process.Start(psi);
      while (!proc.StandardOutput.EndOfStream) {
        outputWriter.WriteLine(proc.StandardOutput.ReadLine());
      }
      proc.WaitForExit();
      if (proc.ExitCode != 0) {
        throw new Exception("Error while compiling Java file " + targetFilename + ". Process exited with exit code " + proc.ExitCode);
      }
      return true;
    }
    
    static bool CopyExternLibraryIntoPlace(string externFilename, string mainProgram, TextWriter outputWriter) {
      // Grossly, we need to look in the file to figure out where to put it
      var pkgName = FindPackageName(externFilename);
      if (pkgName == null) {
        outputWriter.WriteLine("Unable to determine package name: {0}", externFilename);
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
        outputWriter.WriteLine("Additional input {0} copied to {1}", externFilename, tgtFilename);
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
      if (outParams.Count == 0){
        wr.WriteLine("return;");
      }
      else if (outParams.Count == 1){
        wr.WriteLine("return {0};", IdName(outParams[0]));
      }
      else{
        wr.WriteLine("return new Tuple{0}({1});", outParams.Count, Util.Comma(outParams, IdName));
      }
    }
    
    private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*;$");
    
    // TODO: See if more types need to be added
    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || AsNativeType(t) != null || t.IsRefType;
    }
    
    protected void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, TargetWriter wr)
    {
      wr.Write("{0} {1};\n", TypeName(type, wr, tok), name);
      EmitAssignment(name, type, rhs, null, wr);
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
    

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type> superClasses, Bpl.IToken tok,
      TargetWriter wr){
      var filename = string.Format("{1}/{0}.java", name, ModuleName);
      var w = wr.NewFile(filename);
      w.WriteLine("// Interface {0}", name);
      w.WriteLine("// Dafny trait {0} compiled into Java", name);
      w.WriteLine("package {0};", ModuleName);
      w.WriteLine();
      w.WriteLine(
        "import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
      EmitImports(w, out _);
      w.WriteLine();
      w.Write("public interface {0}", IdProtect(name));
      if (superClasses != null){
        string sep = " implements ";
        foreach (var trait in superClasses){
          w.Write("{0}{1}", sep, TypeName(trait, w, tok));
          sep = ", ";
        }
      }

      var instanceMemberWriter = w.NewBlock("");

      //writing the _Companion class
      filename = string.Format("{1}/_Companion_{0}.java", name, ModuleName);
      w = w.NewFile(filename);
      w.WriteLine("// Interface {0}", name);
      w.WriteLine("// Dafny trait {0} compiled into Java", name);
      w.WriteLine("package {0};", ModuleName);
      w.WriteLine();
      w.WriteLine(
        "import java.math.*;"); // TODO: Figure out all the Java imports necessary for compiled program to run.
      EmitImports(w, out _);
      w.WriteLine();
      w.Write("public class _Companion_{0}", name);
      var staticMemberWriter = w.NewBlock("");

      return new ClassWriter(this, instanceMemberWriter, staticMemberWriter);
    }

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt initCall, TargetWriter wr){
      var ctor = initCall == null
        ? null
        : (Constructor) initCall.Method; // correctness of cast follows from precondition of "EmitNew"
      wr.Write("new {0}(", TypeName(type, wr, tok));
      wr.Write(")");
    }

    protected override void EmitAssignment(out TargetWriter wLhs, Type /*?*/ lhsType, out TargetWriter wRhs,
      Type /*?*/ rhsType, TargetWriter wr){
      wLhs = wr.Fork();
      if (!MemberSelectObjIsTrait)
        wr.Write(" = ");
      TargetWriter w;
      if (rhsType != null){
        w = EmitCoercionIfNecessary(from: rhsType, to: lhsType, tok: Bpl.Token.NoToken, wr: wr);
      }
      else{
        w = wr;
      }

      wRhs = w.Fork();
      if (MemberSelectObjIsTrait)
        w.Write(")");
      EndStmt(wr);
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr){
      var dt = dtv.Ctor.EnclosingDatatype;
      var dtName = dt.Module.IsDefaultModule || dt.Module.Name.Equals(ModuleName) ? dt.CompileName : dt.FullCompileName;
      var ctorName = dtv.Ctor.CompileName;

      var typeParams = dtv.InferredTypeArgs.Count == 0
        ? ""
        : string.Format("<{0}>", TypeNames(dtv.InferredTypeArgs, wr, dtv.tok));
      if (!dtv.IsCoCall){
        wr.Write("new {0}{1}", dtName, typeParams);
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   new Dt_Cons<T>( args )
        wr.Write("({0})", arguments);
      }
      else{
        throw new NotImplementedException();
      }

//      else {
//        // In the case of a co-recursive call, generate:
//        //     new Dt__Lazy<T>( LAMBDA )
//        // where LAMBDA is:
//        //     () => { return Dt_Cons<T>( ...args... ); }
//        wr.Write("new {0}__Lazy{1}(", dtv.DatatypeName, typeParams);
//
//        wr.Write("() => { return ");
//        wr.Write("new {0}({1})", DtCtorName(dtv.Ctor, dtv.InferredTypeArgs, wr), arguments);
//        wr.Write("; })");
//      }
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr)
    {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          TrParenExpr("~", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.Cardinality:
          if (expr.Type.AsCollectionType.CollectionTypeName.Equals("multiset")){
            TrParenExpr("", expr, wr, inLetExprBody);
            wr.Write(".cardinality()");
          }
          else if (expr.Type.AsCollectionType.CollectionTypeName.Equals("set") || 
                   expr.Type.AsCollectionType.CollectionTypeName.Equals("map")){
            TrParenExpr("new BigInteger(Long.toString(", expr, wr, inLetExprBody);
            wr.Write(".size()))");
          }
          else{
            TrParenExpr("new BigInteger(Long.toString(", expr, wr, inLetExprBody);
            wr.Write(".length()))");
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
          callString = "&";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          callString = "|";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          callString = "^";
          break;
        case BinaryExpr.ResolvedOpcode.EqCommon:{
          if (IsHandleComparison(tok, e0, e1, errorWr)){
            opString = "==";
          }
          else if (e0.Type.IsRefType){
            opString = "== (Object) ";
          }
          else if (IsDirectlyComparable(e0.Type)){
            opString = "==";
          }
          else{
            callString = "equals";
          }

          break;
        }

        case BinaryExpr.ResolvedOpcode.NeqCommon:{
          if (IsHandleComparison(tok, e0, e1, errorWr)){
            opString = "!=";
          }
          else if (e0.Type.IsRefType){
            opString = "!= (Object) ";
          }
          else if (IsDirectlyComparable(e0.Type)){
            opString = "!=";
          }
          else{
            preOpString = "!";
            callString = "equals";
          }
          break;
        }

        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.LtChar:
          callString = "compareTo";
          postOpString = " < 0";
          break;
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.LeChar:
          callString = "compareTo";
          postOpString = " <= 0";
          break;
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.GeChar:
          callString = "compareTo";
          postOpString = " > 0";
          break;
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.GtChar:
          callString = "compareTo";
          postOpString = " >= 0";
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
          callString = "add";
          truncateResult = true;
          if (resultType.IsCharType){
            preOpString = "(char) (";
            postOpString = ".intValue())";
          }

          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          callString = "subtract";
          truncateResult = true;
          if (resultType.IsCharType){
            preOpString = "(char) (";
            postOpString = ".intValue())";
          }

          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          callString = "multiply";
          truncateResult = true;
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsIntegerType ||
              (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)){
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = "DafnyEuclidian.EuclideanDivision" + suffix;
          }
          else{
            callString = "divide";
          }

          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType ||
              (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)){
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = "DafnyEuclidian.EuclideanModulus" + suffix;
          }
          else{
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
      tuples.Add(2);
      tuples.Add(3);
      foreach(int i in tuples){
        CreateTuple(i, path);
      }
    }

    private static int indent = 0;
    private static String Indent(){
      String Indent = "";
      for (int i = 0; i <= indent; i++){
        Indent += "    ";
      }

      return Indent;
    }
    private static void CreateTuple(int i, string path){
        path += "/Tuple"+i+".java";
        // Create a file to write to.
        using (StreamWriter sw = File.CreateText(path)){
            sw.WriteLine("package DafnyClasses;");
            sw.WriteLine();
            sw.Write("public class Tuple");
            sw.Write(i);
            if (i != 0){
              sw.Write("<");
              for (int j = 0; j < i; j++){
                sw.Write("T" + j);
                if (j != i - 1)
                  sw.Write(", ");
                else{
                  sw.Write("> ");
                }
              }
            }
            sw.WriteLine("{");
            for (int j = 0; j < i; j++){
                sw.WriteLine(Indent() + "private T" + j + " _" + j+";");
            }

            sw.WriteLine();
            sw.Write(Indent() + "public Tuple" + i + "(");
            for (int j = 0; j < i; j++){
                sw.Write("T" + j + " _" + j);
                if (j != i - 1)
                    sw.Write(", ");
            }
            sw.WriteLine(") {");
            indent++;
            for (int j = 0; j < i; j++){
                sw.WriteLine(Indent() + "this._" + j + " = _" + j + ";");
            }

            indent--;
            sw.WriteLine(Indent() + "}");
            sw.WriteLine();
            sw.WriteLine(Indent() + "@Override");
            sw.WriteLine(Indent() + "public boolean equals(Object obj) {");
            indent++;
            sw.WriteLine(Indent() + "if (this == obj) return true;");
            sw.WriteLine(Indent() + "if (obj == null) return false;");
            sw.WriteLine(Indent() + "if (getClass() != obj.getClass()) return false;");
            
            if(i!= 0){
                sw.Write(Indent() + "Tuple" + i + "<");
              for (int j = 0; j < i; j++){
                sw.Write("T" + j);
                if (j != i - 1)
                  sw.Write(", ");
                else{
                  sw.Write("> o = (Tuple" + i + "<");
                }
              }

              for (int j = 0; j < i; j++){
                sw.Write("T" + j);
                if (j != i - 1)
                  sw.Write(", ");
                else{
                  sw.WriteLine(">) obj;");
                }
              }
              sw.Write(Indent() + "return ");
              for (int j = 0; j < i; j++){
                  sw.Write("this._" + j + ".equals(o._" + j + ")");
                  if (j != i - 1)
                      sw.Write(" && ");
                  else{
                      sw.WriteLine(";");
                  }
              }
            }
            else{
                sw.WriteLine(Indent() + "return true;");
            }
            

            indent--;
            sw.WriteLine(Indent() + "}");
            sw.WriteLine();
            sw.WriteLine(Indent() + "@Override");
            sw.WriteLine(Indent() + "public String toString() {");
            indent++;
            sw.WriteLine(Indent() + "StringBuilder sb = new StringBuilder();");
            sw.WriteLine(Indent() + "sb.append(\"(\");");
            for (int j = 0; j < i; j++){
                sw.WriteLine(Indent() + "sb.append(_" + j + ".toString());");
                if (j != i - 1)
                    sw.WriteLine(Indent() + "sb.append(\", \");");
            }

            sw.WriteLine(Indent() + "sb.append(\")\");");
            sw.WriteLine(Indent() + "return sb.toString();");
            indent--;
            sw.WriteLine(Indent() + "}");
            sw.WriteLine();
            sw.WriteLine(Indent() + "@Override");
            sw.WriteLine(Indent() + "public int hashCode() {");
            indent++;
            sw.WriteLine(Indent() + "// GetHashCode method (Uses the djb2 algorithm)");
            sw.WriteLine(Indent() + 
                "// https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm");
            sw.WriteLine(Indent() + "long hash = 5381;");
            sw.WriteLine(Indent() + "hash = ((hash << 5) + hash) + 0;");
            for (int j = 0; j < i; j++){
                sw.WriteLine(Indent() + "hash = ((hash << 5) + hash) + ((long) this._" + j + ".hashCode());");
            }
            sw.WriteLine(Indent() + "return (int) hash;");
            indent--;
            sw.WriteLine(Indent() + "}");
            for (int j = 0; j < i; j++){
                sw.WriteLine();
                sw.WriteLine(Indent() + "public T"+j+" dtor__"+j+"() { return this._"+j+"; }");
            }
            sw.WriteLine("}");
            sw.WriteLine();
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
        return "BigDecimal.ZERO";
      } else if (xType is BitvectorType) {
        var t = (BitvectorType)xType;
        return t.NativeType != null ? "0" : "BigInteger.ZERO";
      } else if (xType is CollectionType) {
        return "new " + TypeName(xType, wr, tok) + "()";
      }
      
      var udt = (UserDefinedType)xType;
      if (udt.ResolvedParam != null) {
//        return "Helpers.Default<" + TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ">()"; TODO: Implement Helpers.Default if necessary
        return "null";
      }
      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.NativeType != null) {
          return "0";
        } else {
          return TypeInitializationValue(td.BaseType, wr, tok, inAutoInitContext);
        }
      } else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl)cl;
        if (td.Witness != null) {
          return TypeName_UDT(FullTypeName(udt), udt.TypeArgs, wr, udt.tok) + ".Witness";
        } else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return string.Format("(({0}) null)", TypeName(xType, wr, udt.tok));
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) -> rangeDefaultValue)
            return string.Format("(({0}) -> {1})",
              Util.Comma(", ", udt.TypeArgs.Count - 1, i => string.Format("{0} x{1}", TypeName(udt.TypeArgs[i], wr, udt.tok), i)),
              rangeDefaultValue);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl)((NonNullTypeDecl)td).Class;
            string typeNameSansBrackets, brackets;
            TypeName_SplitArrayName(udt.TypeArgs[0], wr, udt.tok, out typeNameSansBrackets, out brackets);
            return string.Format("new {0}[{1}]{2}", typeNameSansBrackets, Util.Comma(arrayClass.Dims, _ => "0"), brackets);
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
          return string.Format("({0}) null", TypeName(xType, wr, udt.tok));
        }
      } else if (cl is DatatypeDecl) {
        var s = FullTypeName(udt);
        if (udt.TypeArgs.Count != 0) {
          s += "<" + TypeNames(udt.TypeArgs, wr, udt.tok) + ">";
        }

        if (cl is TupleTypeDecl) {
          return "(" + s + ")null";
        }
        return string.Format("{0}.Default()", s);
      }
      else{
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected type
      }
    }

    protected override TargetWriter DeclareLocalVar(string name, Type type, Bpl.IToken tok, TargetWriter wr)
    {
      wr.Write("{0} {1} = ", type != null ? TypeName(type, wr, tok) : "var", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs, bool useReturnStyleOuts, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, List<Type> typeArgs, Type bvType, TargetWriter wr) {
      var dtorName = FormalName(dtor, formalNonGhostIndex);
      wr.Write("(({0}){1}{2}).{3}", DtCtorName(ctor, typeArgs, wr), source, ctor.EnclosingDatatype is CoDatatypeDecl ? ".Get()" : "", dtorName);
    }
    
    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames, Type resultType, TargetWriter wr, bool untyped = false) {
      wr.Write('(');
      if (!untyped) {
        wr.Write("(Function<{0}{1}>)", Util.Comma("", inTypes, t => TypeName(t, wr, tok) + ", "), TypeName(resultType, wr, tok));
      }
      wr.Write("({0}) ->", Util.Comma(inNames, nm => nm));
      var w = wr.NewExprBlock("");
      wr.Write(").apply");
      return w;
    }
    
    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.WriteLine("continue TAIL_CALL_START;");
    }
    
    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      wr.Write("((Supplier<{0}>) () ->", TypeName(resultType, wr, resultTok));
      var w = wr.NewBigExprBlock("", ").get()");
      return w;
    }
    
    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr)
    {
      if (ct is SetType) {
        wr.Write("new ArrayList<{0}>()", TypeName(ct.Arg, wr, tok));
      } else if (ct is MapType) {
        var mt = (MapType)ct;
        var domtypeName = TypeName(mt.Domain, wr, tok);
        var rantypeName = TypeName(mt.Range, wr, tok);
        wr.Write("new ArrayList<Dafny.Pair<{0},{1}>>()", domtypeName, rantypeName);
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }
    
    protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type boundVarType, out TargetWriter collectionWriter,
      TargetWriter wr, string altBoundVarName = null, Type altVarType = null, Bpl.IToken tok = null) {
      wr.Write("for({0} {1} : ", TypeName(boundVarType, wr, tok), boundVar);
      collectionWriter = wr.Fork();
      if (altBoundVarName == null) {
        return wr.NewBlock(")");
      } else if (altVarType == null) {
        return wr.NewBlockWithPrefix(")", "{0} = {1};", altBoundVarName, boundVar);
      } else {
        return wr.NewBlockWithPrefix(")", "{2} {0} = ({2}){1};", altBoundVarName, boundVar, TypeName(altVarType, wr, tok));
      }
    }
    
    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("{0}.add(", collName);
        TrExpr(elmt, wr, inLetExprBody);
        wr.WriteLine(");");
      } else {
        Contract.Assume(false);  // unepxected collection type
      }
    }
    
    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName, TargetWriter wr) {
      if (ct is SetType) {
        var typeName = TypeName(ct.Arg, wr, tok);
        return string.Format("new DafnyClasses.DafnySet<{0}>({1})", typeName, collName);
      } else if (ct is MapType) {
        var mt = (MapType)ct;
        var domtypeName = TypeName(mt.Domain, wr, tok);
        var rantypeName = TypeName(mt.Range, wr, tok);
        return string.Format("new {3}<{0},{1}>({2})", domtypeName, rantypeName, collName, DafnyMapClass);
      } else {
        Contract.Assume(false);  // unepxected collection type
        throw new cce.UnreachableException();  // please compiler
      }
    }
    
    protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr) {
      return wr.NewNamedBlock("{0}:", label);
    }
    
    protected override void EmitBreak(string label, TargetWriter wr) {
      if (label == null) {
        wr.WriteLine("break;");
      } else {
        wr.WriteLine("break {0};", label);
      }
    }
    
    protected override void EmitAbsurd(string message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }
      wr.WriteLine("throw new IllegalArgumentException(\"{0}\");", message);
    }
    
    protected override void DeclareNewtype(NewtypeDecl nt, TargetWriter wr){
      var cw = CreateClass(IdName(nt), null, wr) as ClassWriter;
      var w = cw.StaticMemberWriter;
      if (nt.NativeType != null) {
        var nativeType = GetNativeTypeName(nt.NativeType);
        var wEnum = w.NewNamedBlock("public static ArrayList<{0}> IntegerRange(BigInteger lo, BigInteger hi)", nativeType);
        wEnum.WriteLine("ArrayList<{0}> arr = new ArrayList<>();", nativeType);
        nativeType = nativeType == "Integer" ? "int" : nativeType.ToLower();
        wEnum.WriteLine("for (BigInteger j = lo; j.compareTo(hi) < 0; j.add(new BigInteger(\"1\"))) {{ arr.add(j.{0}Value()); }}", nativeType);
        wEnum.WriteLine("return arr;");
      }
      if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        var witness = new TargetWriter(w.IndentLevel, true);
        TrExpr(nt.Witness, witness, false);
        if (nt.NativeType == null) {
          cw.DeclareField("Witness", true, true, nt.BaseType, nt.tok, witness.ToString());
        } else {
          w.Write("public static {0} Witness = ({0})(", GetNativeTypeName(nt.NativeType));
          w.Append(witness);
          w.WriteLine(");");
        }
      }
    }
    
    // ABSTRACT METHOD DECLARATIONS FOR THE SAKE OF BUILDING PROGRAM
    protected override string GetHelperModuleName()
    {
      throw new NotImplementedException();
    }
        
    protected override BlockTargetWriter CreateStaticMain(IClassWriter wr)
    {
      throw new NotImplementedException();
    }
    
    protected override void EmitYield(TargetWriter wr)
    {
      throw new NotImplementedException();
    }
    
    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr){
      throw new NotImplementedException();
    }

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function,
      List<Expression> arguments, bool inLetExprBody,
      TargetWriter wr){
      throw new NotImplementedException();
    }


    protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs,
      List<Type> boundTypes, Type resultType,
      Bpl.IToken resultTok, bool inLetExprBody, TargetWriter wr){
      throw new NotImplementedException();
    }
    
    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok,
      string bvName, TargetWriter wr){
      throw new NotImplementedException();
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType,
      Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr){
      throw new NotImplementedException();
    }

    protected override void EmitIsZero(string varName, TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term,
      bool inLetExprBody,
      TargetWriter wr){
      throw new NotImplementedException();
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr)
    {
      throw new NotImplementedException();
    }
    
    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      throw new NotImplementedException();
    }
    
    protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions, bool mustInitialize, TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr){
      throw new NotImplementedException();
    }

    protected override string GetQuantifierName(string bvType)
    {
      return string.Format("Dafny.Helpers.Quantifier<{0}>", bvType);
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr)
    {
      throw new NotImplementedException();
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr)
    {
      throw new NotImplementedException();
    }
        
    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr)
    {
      throw new NotImplementedException();
    }
        
    protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr)
    {
      throw new NotImplementedException();
    }
  }
}
