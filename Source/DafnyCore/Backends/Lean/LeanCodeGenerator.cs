using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Numerics;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Type = Microsoft.Dafny.Type;

namespace DafnyCore.Backends.Lean;

public class LeanCodeGenerator(DafnyOptions options, ErrorReporter reporter) : SinglePassCodeGenerator(options, reporter) {
  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    throw new NotImplementedException();
  }

  public override string PublicIdProtect(string name) {
    throw new NotImplementedException();
  }
  
  // Easier to specify what we support, rather than what not
  public override IReadOnlySet<Feature> UnsupportedFeatures { 
    get
    {
      var ret = Enum.GetValues<Feature>().ToHashSet();
      // TODO incrementally remove things
      return ret;
    }
  }

  protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter wr, string argsParameterName) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree CreateModule(ModuleDefinition module, string moduleName, bool isDefault,
    ModuleDefinition externModule, string libraryName, Attributes moduleAttributes, ConcreteSyntaxTree wr) {
    return wr;
  }

  protected override string GetHelperModuleName() {
    throw new NotImplementedException();
  }

  protected override IClassWriter CreateClass(string moduleName, bool isExtern, string fullPrintName, List<TypeParameter> typeParameters, TopLevelDecl cls,
    List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
    return new NullClassWriter(this);
  }

  protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters, TraitDecl trait, List<Type> superClasses,
    IOrigin tok, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(tok, Feature.Traits);
  }

  protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(iter.StartToken, Feature.Iterators);
  }

  protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
    // TODO look at DeclareDatatype in CsharpCodeGenerator
    if (dt.Ctors.Count > 1)
    {
      // Inductive
      Contract.Assert(dt.Members.Count == 0); // This is to make sure that the inductive datatype has no function members
      wr.WriteLine($"inductive {dt.GetCompileName(Options)} where");
      foreach (var ctor in dt.Ctors) {
        wr.WriteLine($"| {ctor.GetCompileName(options)} {string.Join(" ", ctor.Formals.Select(formal => $"({formal.CompileName} : {TypeName(formal.Type, wr, formal.StartToken)})"))}");
      }
    }
    else
    {
      // Structure
      // REVIEW: do function members of dt need to do explicit `this` passing? Yes they do - Siva
      var structName = dt.GetCompileName(Options);
      wr.WriteLine($"structure {structName} where");
      foreach (var ctor in dt.Ctors)
      {
        var record = string.Join("\n  ", ctor.Formals.Select(formal => $"{formal.CompileName} : {TypeName(formal.Type, wr, formal.StartToken)}"));
        wr.WriteLine($"  {ctor.GetCompileName(Options)} ::\n  {record}");
      }
      foreach (var member in dt.Members) {
        switch (member) {
          case Function f:
            // TODO Handle the member functions
            // wr.WriteLine($"def {structName}.{f.GetCompileName(options)}()");
            EmitExpr(f.Body, false, wr, null);
            break;
          default:
            // Constant member of some kind
            break;
        }
      }
    }
    // TODO this might be incorrect
    return new NullClassWriter(this);
  }

  protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(nt.StartToken, 0, "newtype");
  }

  protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(sst.StartToken, Feature.SubsetTypeTests);
  }

  protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
    throw new NotImplementedException();
  }

  protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
    throw new UnsupportedFeatureException(Token.NoToken, Feature.RuntimeTypeDescriptors);
  }

  protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  internal override string TypeName(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl member = null) =>
    type switch {
      BoolType => "Bool",
      CharType => "Char",
      IntType => "Int",
      MapType { Domain: var domain, Range: var range } =>
        $"{TypeName(domain, wr, tok, member)} -> {TypeName(range, wr, tok, member)}",
      MultiSetType multiSetType => throw new NotImplementedException(),
      SeqType { Arg: var argType } => $"List ({TypeName(argType, wr, tok, member)})",
      SetType { Arg: var argType } => $"List ({TypeName(argType, wr, tok, member)})",
      UserDefinedType { Name: "nat" } => "Nat",
      UserDefinedType { Name: "_tuple#0" } => "Unit",
      UserDefinedType { Name: var name } => name,
      _ => throw new ArgumentOutOfRangeException(nameof(type))
    };

  protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IOrigin tok, bool usePlaceboValue,
    bool constructTypeParameterDefaultsFromTypeDescriptors) {
    throw new NotImplementedException();
  }

  protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance, List<Type> typeArgs, ConcreteSyntaxTree wr, IOrigin tok,
    bool omitTypeArguments) {
    throw new NotImplementedException();
  }

  internal override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl member) {
    throw new NotImplementedException();
  }

  protected override bool DeclareFormal(string prefix, string name, Type type, IOrigin tok, bool isInParam, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void DeclareLocalVar(string name, Type type, IOrigin tok, bool leaveRoomForRhs, string rhs, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IOrigin tok, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void DeclareLocalOutVar(string name, Type type, IOrigin tok, string rhs, bool useReturnStyleOuts,
    ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitActualTypeArgs(List<Type> typeArgs, IOrigin tok, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
    throw new NotImplementedException();
  }

  protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, 0, "imperative code");
  }

  protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, 0, "imperative code");
  }

  protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, 0, "imperative code");
  }

  protected override void EmitYield(ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, 0, "imperative code");
  }

  protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitHalt(IOrigin tok, Expression messageExpr, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, 0, "imperative code");
  }

  protected override ConcreteSyntaxTree EmitForStmt(IOrigin tok, IVariable loopIndex, bool goingUp, string endVarName, List<Statement> body,
    LList<Label> labels, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, Feature.ForLoops, "imperative code");
  }

  protected override ConcreteSyntaxTree CreateForLoop(string indexVar, Action<ConcreteSyntaxTree> bound, ConcreteSyntaxTree wr, string start = null) {
    throw new UnsupportedFeatureException(Token.NoToken, Feature.ForLoops, "imperative code");
  }

  protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, Feature.ForLoops, "imperative code");
  }

  protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, 0, "imperative code");
  }

  protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(Token.NoToken, 0, "imperative code");
  }

  protected override string GetQuantifierName(string bvType) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IOrigin tok,
    out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override Action<ConcreteSyntaxTree> GetSubtypeCondition(string tmpVarName, Type boundVarType, IOrigin tok, ConcreteSyntaxTree wPreconditions) {
    throw new NotImplementedException();
  }

  protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName, Type sourceType,
    bool introduceBoundVar, IOrigin tok, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
    out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitNew(Type type, IOrigin tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitNewArray(Type elementType, IOrigin tok, List<string> dimensions, bool mustInitialize, string exampleElement,
    ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
    switch(e)
    {
      case CharLiteralExpr { Value: var value }:
        wr.Write($"'{value}'");
        break;
      case StringLiteralExpr { Value: var value }:
        wr.Write($"\"{value}\"");
        break;
      case StaticReceiverExpr:
        throw new ArgumentOutOfRangeException(nameof(e));
      default:
        // NB: Integer/Decimal/Boolean literal
        wr.Write($"{e}");
        break;
    }
  }

  protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, NativeType nativeType, bool surroundByUnchecked,
    ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr, bool inLetExprBody,
    ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
    throw new NotImplementedException();
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

  protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
    throw new NotImplementedException();
  }

  protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember = false) {
    throw new NotImplementedException();
  }

  protected override void EmitDatatypeValue(DatatypeValue dtv, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType, out string compiledName, out string preString,
    out string postString) {
    throw new NotImplementedException();
  }

  protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member, List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap,
    Type expectedType, string additionalCustomParameter = null, bool internalAccess = false) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree EmitArraySelect(List<Action<ConcreteSyntaxTree>> indices, Type elmtType, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
    CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray, bool inLetExprBody,
    ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
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

  protected override void EmitApplyExpr(Type functionType, IOrigin tok, Expression function, List<Expression> arguments, bool inLetExprBody,
    ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments, List<Type> boundTypes, Type resultType, IOrigin resultTok,
    bool inLetExprBody, ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor, Func<List<Type>> getTypeArgs,
    Type bvType, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IOrigin tok, List<string> inNames, Type resultType, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts, bool untyped = false) {
    throw new NotImplementedException();
  }

  protected override void CreateIIFE(string bvName, Type bvType, IOrigin bvTok, Type bodyType, IOrigin bodyTok, ConcreteSyntaxTree wr,
    ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IOrigin resultTok, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IOrigin resultTok, string bvName, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitConversionExpr(Expression fromExpr, Type fromType, Type toType, bool inLetExprBody, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitTypeTest(string localName, Type fromType, Type toType, IOrigin tok, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void EmitIsIntegerTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitIsUnicodeScalarValueTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitIsInIntegerRange(Expression source, BigInteger lo, BigInteger hi, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitCollectionDisplay(CollectionType ct, IOrigin tok, List<Expression> elements, bool inLetExprBody, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitMapDisplay(MapType mt, IOrigin tok, List<MapDisplayEntry> elements, bool inLetExprBody, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
    throw new NotImplementedException();
  }

  protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
    throw new NotImplementedException();
  }

  protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody, ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IOrigin tok, string collName, Expression term, bool inLetExprBody,
    ConcreteSyntaxTree wr) {
    throw new NotImplementedException();
  }

  protected override void GetCollectionBuilder_Build(CollectionType ct, IOrigin tok, string collName, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmt) {
    throw new NotImplementedException();
  }

  protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, ConcreteSyntaxTree wr,
    ConcreteSyntaxTree wStmts) {
    throw new NotImplementedException();
  }

  protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
    throw new UnsupportedFeatureException(body.StartToken, 0);
  }
}