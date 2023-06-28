using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Runtime.CompilerServices;
using Dafny;
using JetBrains.Annotations;
using DAST;

namespace Microsoft.Dafny.Compilers {

  class ProgramBuilder : ModuleContainer {
    readonly List<TopLevel> items = new();

    public void AddModule(Module item) {
      items.Add((TopLevel)TopLevel.create_Module(item));
    }

    public ModuleBuilder Module(string name) {
      return new ModuleBuilder(this, name);
    }

    public List<TopLevel> Finish() {
      return items;
    }
  }

  interface ModuleItemContainer {
    void AddModuleItem(ModuleItem item);
  }

  interface ModuleContainer {
    void AddModule(Module item);

    public ModuleBuilder Module(string name) {
      return new ModuleBuilder(this, name);
    }
  }

  class ModuleBuilder : ModuleContainer, ClassContainer {
    readonly ModuleContainer parent;
    readonly string name;
    List<ModuleItem> body = new List<ModuleItem>();

    public ModuleBuilder(ModuleContainer parent, string name) {
      this.parent = parent;
      this.name = name;
    }

    public void AddModule(Module item) {
      this.body.Add((ModuleItem)ModuleItem.create_Module(item));
    }

    public void AddClass(Class item) {
      this.body.Add((ModuleItem)ModuleItem.create_Class(item));
    }

    public Object Finish() {
      parent.AddModule((Module)Module.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<ModuleItem>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface ClassContainer {
    void AddClass(Class item);

    public ClassBuilder Class(string name) {
      return new ClassBuilder(this, name);
    }
  }

  class ClassBuilder : MethodContainer {
    readonly ClassContainer parent;
    readonly string name;
    readonly List<ClassItem> body = new();

    public ClassBuilder(ClassContainer parent, string name) {
      this.parent = parent;
      this.name = name;
    }

    public void AddMethod(DAST.Method item) {
      this.body.Add((ClassItem)ClassItem.create_Method(item));
    }

    public Object Finish() {
      parent.AddClass((Class)Class.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<ClassItem>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface MethodContainer {
    void AddMethod(DAST.Method item);

    public MethodBuilder Method(string name) {
      return new MethodBuilder(this, name);
    }
  }

  class MethodBuilder : StatementContainer {
    readonly MethodContainer parent;
    readonly string name;
    readonly List<DAST.Statement> body = new();

    public MethodBuilder(MethodContainer parent, string name) {
      this.parent = parent;
      this.name = name;
    }

    public void AddStatement(DAST.Statement item) {
      this.body.Add(item);
    }

    public Object Finish() {
      parent.AddMethod((DAST.Method)DAST.Method.create(Sequence<Rune>.UnicodeFromString(this.name), Sequence<DAST.Statement>.FromArray(body.ToArray())));
      return parent;
    }
  }

  interface StatementContainer {
    void AddStatement(DAST.Statement item);

    public void Print(DAST.Expression expr) {
      this.AddStatement((DAST.Statement)DAST.Statement.create_Print(expr));
    }
  }

  class DafnyCompiler : SinglePassCompiler {
    ProgramBuilder items;
    Object currentBuilder;

    public void Start() {
      if (items != null) {
        throw new InvalidOperationException("");
      }

      items = new ProgramBuilder();
      this.currentBuilder = items;
    }

    public List<TopLevel> Build() {
      var res = items.Finish();
      items = null;
      this.currentBuilder = null;
      return res;
    }

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
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, bool isExtern,
        string libraryName, ConcreteSyntaxTree wr) {
      if (currentBuilder is ModuleContainer moduleBuilder) {
        currentBuilder = moduleBuilder.Module(moduleName);
      } else {
        throw new NotImplementedException();
      }

      return wr;
    }

    protected override void FinishModule() {
      if (currentBuilder is ModuleBuilder builder) {
        currentBuilder = builder.Finish();
      } else {
        throw new NotImplementedException();
      }
    }

    protected override string GetHelperModuleName() => DafnyRuntimeModule;

    private static string MangleName(string name) {
      return name;
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      if (currentBuilder is ClassContainer builder) {
        return new ClassWriter(this, builder.Class(name));
      } else {
        throw new NotImplementedException();
      }
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TopLevelDecl trait, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      // Currently ignores subset types because they appear in the prelude
      // throw new NotImplementedException();
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      throw new NotImplementedException();
    }

    private class ClassWriter : IClassWriter {
      private readonly DafnyCompiler compiler;
      private readonly ClassBuilder builder;
      private readonly List<MethodBuilder> methods = new();

      public ClassWriter(DafnyCompiler compiler, ClassBuilder builder) {
        this.compiler = compiler;
        this.builder = builder;
      }

      public ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        var builder = ((MethodContainer)this.builder).Method(m.Name);
        methods.Add(builder);
        compiler.currentBuilder = builder;
        return new ConcreteSyntaxTree();
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {
        throw new NotImplementedException();
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok,
          bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        throw new NotImplementedException();
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok,
          bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        throw new NotImplementedException();
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IToken tok, string rhs, Field field) {
        throw new NotImplementedException();
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();
      }

      public ConcreteSyntaxTree ErrorWriter() => null;

      public void Finish() {
        foreach (var method in methods) {
          method.Finish();
        }
        compiler.currentBuilder = this.builder.Finish();
      }
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      type = DatatypeWrapperEraser.SimplifyType(Options, type, true);
      return type.ToString();
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl/*?*/ member = null) {
      throw new NotImplementedException();
    }

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      throw new NotImplementedException();
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      throw new NotImplementedException();
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      throw new NotImplementedException();
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      throw new NotImplementedException();
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      wr.Write("var ");
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
      return target;
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      if (currentBuilder is StatementContainer statementContainer) {
        statementContainer.Print((DAST.Expression)DAST.Expression.create_Literal(Literal.create_StringLiteral(Sequence<Rune>.UnicodeFromString(arg.ToString()))));
      } else {
        throw new NotImplementedException("");
      }
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
      // var direction = goingUp ? "to" : "downto";
      // var lowWr = new ConcreteSyntaxTree();
      // wr.Format($"for {IdName(loopIndex)} := {lowWr} {direction} {endVarName}");
      // var bodyWr = wr.NewBlock();
      // TrStmtList(body, bodyWr);
      // return lowWr;
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, string bound, ConcreteSyntaxTree wr, string start = null) {
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
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Quantifiers);
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type collectionElementType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<string> dimensions,
      bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      throw new NotImplementedException();
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
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
      throw new NotImplementedException();
    }

    protected override void EmitThis(ConcreteSyntaxTree wr) {
      wr.Write("this");
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      wr.Write(dtv.ToString());
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
        out string compiledName, out string preString, out string postString) {
      throw new NotImplementedException();
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
      string additionalCustomParameter = null, bool internalAccess = false) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<string> indices, Type elmtType, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
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
      throw new NotImplementedException();
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
        List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override bool TargetLambdasRestrictedToExpressions => true;
    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      throw new NotImplementedException();
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      throw new NotImplementedException();
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
      throw new NotImplementedException();
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
      throw new NotImplementedException();
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
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
      throw new NotImplementedException();
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      throw new UnsupportedFeatureException(e.tok, Feature.MapComprehensions);
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.MapComprehensions);
    }

    protected override string GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      throw new NotImplementedException();
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override Type EmitIntegerRange(Type type, out ConcreteSyntaxTree wLo, out ConcreteSyntaxTree wHi, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ExactBoundedPool);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

  }
}