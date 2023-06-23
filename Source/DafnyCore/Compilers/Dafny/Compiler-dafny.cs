using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny.Compilers {

  class DafnyCompiler : SinglePassCompiler {
    public DafnyCompiler(DafnyOptions options, ErrorReporter reporter) : base(options, reporter) {
      if (Options?.CoverageLegendFile != null) {
        Imports.Add("DafnyProfiling");
      }
    }

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.UnboundedIntegers,
      Feature.RealNumbers,
      Feature.CollectionsOfTraits,
      Feature.Codatatypes,
      Feature.Multisets,
      Feature.ExternalClasses,
      Feature.Traits,
      Feature.Iterators,
      Feature.NonNativeNewtypes,
      Feature.RuntimeTypeDescriptors,
      Feature.MultiDimensionalArrays,
      Feature.CollectionsOfTraits,
      Feature.Quantifiers,
      Feature.NewObject,
      Feature.BitvectorRotateFunctions,
      Feature.NonSequentializableForallStatements,
      Feature.FunctionValues,
      Feature.ArrayLength,
      Feature.Ordinals,
      Feature.MapItems,
      Feature.Codatatypes,
      Feature.LetSuchThatExpressions,
      Feature.NonNativeNewtypes,
      Feature.TypeTests,
      Feature.SubsetTypeTests,
      Feature.SequenceDisplaysOfCharacters,
      Feature.MapComprehensions,
      Feature.ExactBoundedPool,
      Feature.RunAllTests,
      Feature.MethodSynthesis,
      Feature.UnicodeChars,
      Feature.ConvertingValuesToStrings
    };

    private readonly List<string> Imports = new() { DafnyDefaultModule };

    private const string DafnyRuntimeModule = "_dafny";
    private const string DafnyDefaultModule = "module_";

    protected override string AssignmentSymbol { get => " := "; }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
      wr.WriteLine($"// Dafny program {program.Name} compiled into Simple Dafny");
      wr.WriteLine();
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      wr.WriteLine("import opened i_module");
      var wrBody = wr.NewBlock("method Main()", "");
      wrBody.WriteLine("ii__default.iMain();");
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern,
        string libraryName, ConcreteSyntaxTree wr) {
      if (moduleName == "_System") {
        return wr;
      }
      if (!isDefault) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
      }
      return wr.NewBlock($"module {IdProtect(moduleName)}");
    }

    protected override string GetHelperModuleName() => DafnyRuntimeModule;

    private static string MangleName(string name) {
      return "i" + name;
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {

      var methodWriter = wr.NewBlock($"class {IdProtect(name)}");
      var block = methodWriter.NewBlock(header: $"constructor()");
      var constructorWriter = block.Fork();
      return new ClassWriter(this, constructorWriter, methodWriter);

    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TopLevelDecl trait, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    private class ClassWriter : IClassWriter {
      private readonly DafnyCompiler Compiler;
      public readonly ConcreteSyntaxTree ConstructorWriter;
      public readonly ConcreteSyntaxTree MethodWriter;

      public ClassWriter(DafnyCompiler compiler, ConcreteSyntaxTree constructorWriter, ConcreteSyntaxTree methodWriter) {
        Contract.Requires(compiler != null);
        Contract.Requires(methodWriter != null);
        Contract.Requires(constructorWriter != null);
        Compiler = compiler;
        ConstructorWriter = constructorWriter;
        MethodWriter = methodWriter;
      }

      public ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        return Compiler.CreateMethod(m, typeArgs, createBody, MethodWriter, forBodyInheritance, lookasideBody);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.MethodSynthesis);
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

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok,
          bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        return Compiler.CreateGetterSetter(name, createBody, out setterWriter, methodWriter: MethodWriter);
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IToken tok, string rhs, Field field) {
        Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, ConstructorWriter);
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();
      }

      public ConcreteSyntaxTree ErrorWriter() => MethodWriter;

      public void Finish() {

      }
    }

    private void DeclareField(string name, bool isStatic, bool isConst, Type type, IToken tok, string rhs,
        ConcreteSyntaxTree fieldWriter) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    private ConcreteSyntaxTree CreateGetterSetter(string name, bool createBody, out ConcreteSyntaxTree setterWriter, ConcreteSyntaxTree methodWriter) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    private ConcreteSyntaxTree CreateGetter(string name, Type resultType, IToken tok, bool isStatic, bool createBody, ConcreteSyntaxTree methodWriter) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    private ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      var wrBody = wr.NewBlock($"static method {IdProtect(m.FullDafnyName)}()");
      return wrBody;
    }

    private ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
      List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
      ConcreteSyntaxTree wr, bool forBodyInheritance, bool lookasideBody) {
      var wrBody = wr.NewBlock($"method {name}() returns (o: {resultType})");
      return wrBody;
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      type = DatatypeWrapperEraser.SimplifyType(Options, type, true);
      return type.ToString();
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      wr.Write("var ");
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
      return target;
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      var wStmts = wr.Fork();
      wr.Write("print(");
      EmitToString(wr, arg, wStmts);
      wr.WriteLine(");");
    }

    private void EmitToString(ConcreteSyntaxTree wr, Expression arg, ConcreteSyntaxTree wStmts) {
      wr = Expr(arg, false, wStmts);
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
      // var direction = goingUp ? "to" : "downto";
      // var lowWr = new ConcreteSyntaxTree();
      // wr.Format($"for {IdName(loopIndex)} := {lowWr} {direction} {endVarName}");
      // var bodyWr = wr.NewBlock();
      // TrStmtList(body, bodyWr);
      // return lowWr;
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr, string start = null) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override string GetQuantifierName(string bvType) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Quantifiers);
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<string> dimensions,
      bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      wr.Write(e.ToString());
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      if (str.Contains("\"") || str.Contains("\\") || !str.All(char.IsAscii)) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.UnicodeChars);
      } else {
        wr.Write($"\"{str}\"");
      }
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      throw new UnsupportedFeatureException(e0.tok, Feature.BitvectorRotateFunctions);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public override string PublicIdProtect(string name) {
      return MangleName(name);
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      wr.Write("this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
        out string compiledName, out string preString, out string postString) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
      string additionalCustomParameter = null, bool internalAccess = false) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(expr.tok, Feature.Multisets);
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function,
        List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Append(Expr(function, inLetExprBody, wStmts));
      TrExprList(arguments, wr, inLetExprBody, wStmts);
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
        List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override bool TargetLambdasRestrictedToExpressions => true;
    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(resultTok, Feature.LetSuchThatExpressions);
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(resultTok, Feature.LetSuchThatExpressions);
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Expression e0, Expression e1, IToken tok, Type resultType,
      out string opString,
      out string preOpString,
      out string postOpString,
      out string callString,
      out string staticCallString,
      out bool reverseArguments,
      out bool truncateResult,
      out bool convertE1_to_int,
      out bool coerceE1,
      ConcreteSyntaxTree errorWr) {

      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;
      coerceE1 = false;

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "<==>";
          break;
        case BinaryExpr.ResolvedOpcode.Imp:
          opString = "==>";
          break;
        case BinaryExpr.ResolvedOpcode.And:
          opString = "&&";
          break;
        case BinaryExpr.ResolvedOpcode.Or:
          opString = "||";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          opString = "&";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          opString = "|";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          opString = "^";
          break;
        case BinaryExpr.ResolvedOpcode.EqCommon:
          opString = "==";
          break;
        case BinaryExpr.ResolvedOpcode.NeqCommon:
          opString = "!=";
          break;
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
        case BinaryExpr.ResolvedOpcode.LeftShift:
          opString = "<<";
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          opString = ">>";
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          opString = "+";
          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          opString = "-";
          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          opString = "*";
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          opString = "/";
          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          opString = "%";
          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
          opString = "==";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
          opString = "==";
          break;
        case BinaryExpr.ResolvedOpcode.SeqEq:
          opString = "==";
          break;
        case BinaryExpr.ResolvedOpcode.MapEq:
          opString = "==";
          break;
        case BinaryExpr.ResolvedOpcode.ProperSubset:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.Subset:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
          opString = "!!";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          opString = "!!";
          break;
        case BinaryExpr.ResolvedOpcode.InSet:
          opString = "in";
          break;
        case BinaryExpr.ResolvedOpcode.InMultiSet:
          opString = "in";
          break;
        case BinaryExpr.ResolvedOpcode.InMap:
          opString = "in";
          break;
        case BinaryExpr.ResolvedOpcode.Union:
          opString = "+";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          opString = "+";
          break;
        case BinaryExpr.ResolvedOpcode.MapMerge:
          opString = "+";
          break;
        case BinaryExpr.ResolvedOpcode.Intersection:
          opString = "*";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          opString = "*";
          break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
          opString = "-";
          break;
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          opString = "-";
          break;
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          opString = "-";
          break;
        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.Concat:
          opString = "+";
          break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          opString = "in";
          break;
      }

    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      wr.Write(e.ToString());
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.TypeTests);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var (open, close) = ct switch {
        SeqType => ("[", "]"),
        _ => ("{", "}")
      };
      wr.Write(open);
      TrExprList(elements, wr, inLetExprBody, wStmts, parens: false);
      wr.Write(close);
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(tok, Feature.MapComprehensions);
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      throw new UnsupportedFeatureException(e.tok, Feature.MapComprehensions);
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.MapComprehensions);
    }

    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override Type EmitIntegerRange(Type type, out ConcreteSyntaxTree wLo, out ConcreteSyntaxTree wHi, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ExactBoundedPool);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

  }
}