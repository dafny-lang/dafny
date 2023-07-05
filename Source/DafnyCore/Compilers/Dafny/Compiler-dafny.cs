using System;
using System.Collections.Generic;
using Dafny;
using JetBrains.Annotations;
using DAST;
using System.Data;
using System.Numerics;
using Microsoft.BaseTypes;

namespace Microsoft.Dafny.Compilers {

  class DafnyCompiler : SinglePassCompiler {
    ProgramBuilder items;
    public object currentBuilder;

    public void Start() {
      if (items != null) {
        throw new InvalidOperationException("");
      }

      items = new ProgramBuilder(this);
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
      Feature.Ordinals,
      Feature.FunctionValues,
      Feature.Iterators,
      Feature.CollectionsOfTraits,
      Feature.AllUnderscoreExternalModuleNames,
      Feature.Codatatypes,
      Feature.Multisets,
      Feature.RuntimeTypeDescriptors,
      Feature.MultiDimensionalArrays,
      Feature.MapComprehensions,
      Feature.Traits,
      Feature.LetSuchThatExpressions,
      Feature.NonNativeNewtypes,
      Feature.MethodSynthesis,
      Feature.ExternalClasses,
      Feature.NewObject,
      Feature.NonSequentializableForallStatements,
      Feature.ArrayLength,
      Feature.MapItems,
      Feature.RunAllTests,
      Feature.IntBoundedPool,
      Feature.ExactBoundedPool,
      Feature.SequenceDisplaysOfCharacters,
      Feature.TypeTests,
      Feature.SubsetTypeTests,
      Feature.Quantifiers,
      Feature.BitvectorRotateFunctions,
      Feature.ForLoops,
      Feature.ContinueStatements,
      Feature.AssignSuchThatWithNonFiniteBounds,
      Feature.SequenceUpdateExpressions,
      Feature.SequenceConstructionsWithNonLambdaInitializers,
      Feature.ExternalConstructors,
      Feature.TupleInitialization,
      Feature.SubtypeConstraintsInQuantifiers,
      Feature.TuplesWiderThan20,
    };

    private readonly List<string> Imports = new() { DafnyDefaultModule };

    private const string DafnyRuntimeModule = "_dafny";
    private const string DafnyDefaultModule = "module_";

    protected override string AssignmentSymbol { get => null; }

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
        throw new InvalidOperationException();
      }
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TraitDecl trait, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      if (currentBuilder is NewtypeContainer builder) {
        builder.AddNewtype((Newtype)Newtype.create_Newtype(
          Sequence<Rune>.UnicodeFromString(nt.Name),
          GenType(nt.BaseType)
        ));

        return new NullClassWriter();
      } else {
        throw new InvalidOperationException();
      }
    }

    private DAST.Type GenType(Type typ) {
      // TODO(shadaj): this is leaking Rust types into the AST, but we do need native types
      if (typ is IntType) {
        return (DAST.Type)DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("i32"));
      } else {
        return (DAST.Type)(AsNativeType(typ).Sel switch {
          NativeType.Selection.Byte => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("u8")),
          NativeType.Selection.SByte => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("i8")),
          NativeType.Selection.Short => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("u16")),
          NativeType.Selection.UShort => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("i16")),
          NativeType.Selection.Int => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("u32")),
          NativeType.Selection.UInt => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("i32")),
          NativeType.Selection.Long => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("u64")),
          NativeType.Selection.ULong => DAST.Type.create_Ident(Sequence<Rune>.UnicodeFromString("i64")),
          _ => throw new InvalidOperationException(),
        });
      }
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
        compiler.currentBuilder = builder.Finish();
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
      var xType = DatatypeWrapperEraser.SimplifyType(Options, type);

      if (xType.IsObjectQ) {
        return "object";
      }

      switch (xType) {
        case BoolType:
          return "bool";
        case CharType:
          return "str";
        case IntType or BigOrdinalType or BitvectorType:
          return "int";
        case RealType:
          return $"{DafnyRuntimeModule}.BigRational";
        case UserDefinedType udt: {
            var s = FullTypeName(udt, member);
            return TypeName_UDT(s, udt, wr, udt.tok);
          }
        case CollectionType:
          throw new NotImplementedException();
      }

      throw new cce.UnreachableException();
    }

    // sometimes, the compiler generates the initial value before the declaration,
    // so we buffer it here
    DAST.Expression bufferedInitializationValue = null;

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      if (bufferedInitializationValue != null) {
        throw new InvalidOperationException();
      } else {
        throw new NotImplementedException();
        // bufferedInitializationValue = (DAST.Expression)DAST.Expression.create_PassThroughExpr(
        //   Sequence<Rune>.UnicodeFromString("TODO")
        // );

        return null; // used by DeclareLocal(Out)Var
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      return fullCompileName;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
      if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
          DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) {
        var s = FullTypeName(udt, member);
        return TypeName_UDT(s, udt, wr, udt.tok);
      } else {
        return TypeName(type, wr, tok, member);
      }
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      throw new NotImplementedException();
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      if (currentBuilder is StatementContainer statementContainer) {
        var typ = GenType(type);

        if (bufferedInitializationValue == null) {
          // we expect an initializer to come *after* this declaration
          currentBuilder = statementContainer.DeclareAndAssign(typ);
        } else {
          var rhsValue = bufferedInitializationValue;
          bufferedInitializationValue = null;

          statementContainer.AddStatement(
            (DAST.Statement)DAST.Statement.create_DeclareVar(
              Sequence<Rune>.UnicodeFromString(name),
              typ,
              rhsValue
            )
          );
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, true, rhs, wr);
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override string GenerateLhsDecl(string target, Type type, ConcreteSyntaxTree wr, IToken tok) {
      throw new NotImplementedException();
    }

    private class BuilderLvalue : ILvalue {
      readonly DafnyCompiler compiler;
      readonly string name;

      public BuilderLvalue(DafnyCompiler compiler, string name) {
        this.compiler = compiler;
        this.name = name;
      }

      public void EmitRead(ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
      }

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        if (compiler.currentBuilder is AssignBuilder builder) {
          builder.SetName(name);
          return new ConcreteSyntaxTree();
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    protected override ILvalue VariableLvalue(IVariable var) {
      return new BuilderLvalue(this, IdName(var));
    }

    protected override ConcreteSyntaxTree EmitAssignment(ILvalue wLhs, Type lhsType /*?*/, Type rhsType /*?*/,
      ConcreteSyntaxTree wr, IToken tok) {
      if (currentBuilder is AssignBuilder) {
        // do nothing (we are assigning to variable that is being declared)
      } else if (currentBuilder is StatementContainer builder) {
        currentBuilder = builder.Assign();
      } else {
        throw new InvalidOperationException();
      }

      return base.EmitAssignment(wLhs, lhsType, rhsType, wr, tok);
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      if (currentBuilder is StatementContainer statementContainer) {
        ExprBuffer buffer = new(this);
        currentBuilder = buffer;
        Console.WriteLine(this.currentBuilder);
        Expr(arg, false, new ConcreteSyntaxTree());
        statementContainer.Print(buffer.Finish());
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
      if (currentBuilder is ExprContainer builder) {
        switch (e) {
          case CharLiteralExpr:
            throw new NotImplementedException();
            break;
          case StringLiteralExpr str:
            builder.AddExpr((DAST.Expression) DAST.Expression.create_Literal(DAST.Literal.create_StringLiteral(
              Sequence<Rune>.UnicodeFromString(str.AsStringLiteral())
            )));
            break;
          case StaticReceiverExpr:
            throw new NotImplementedException();
            break;
          default:
            switch (e.Value) {
              case null:
                throw new NotImplementedException();
                break;
              case bool value:
                throw new NotImplementedException();
                break;
              case BigInteger integer:
                builder.AddExpr((DAST.Expression) DAST.Expression.create_Literal(DAST.Literal.create_IntLiteral(integer)));
                break;
              case BigDec n:
                throw new NotImplementedException();
                break;
              default:
                // TODO: This may not be exhaustive
                throw new cce.UnreachableException();
            }
            break;
        }
      } else {
        throw new InvalidOperationException("Cannot emit literal expression outside of expression context: " + currentBuilder);
      }
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
      if (udt is ArrowType) {
        throw new NotImplementedException();
      }

      var cl = udt.ResolvedClass;
      return cl switch {
        TypeParameter => throw new NotImplementedException(),
        ArrayClassDecl => throw new NotImplementedException(),
        TupleTypeDecl => throw new NotImplementedException(),
        _ => IdProtect(cl.GetFullCompileName(Options))
      };
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember) {
      throw new NotImplementedException();
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, ConcreteSyntaxTree wr) {
      if (currentBuilder is ExprBuffer builder) {
        List<DAST.Expression> contents = builder.PopN(dtv.Arguments.Count);
        builder.AddExpr((DAST.Expression) DAST.Expression.create_DatatypeValue(
          Sequence<DAST.Expression>.FromArray(contents.ToArray())
        ));
      } else {
        throw new InvalidOperationException("Cannot emit datatype value outside of expression context: " + currentBuilder);
      }
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
      throw new NotImplementedException();
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

      opString = op switch {
        BinaryExpr.ResolvedOpcode.Iff => "<==>",
        BinaryExpr.ResolvedOpcode.Imp => "==>",
        BinaryExpr.ResolvedOpcode.And => "&&",
        BinaryExpr.ResolvedOpcode.Or => "||",
        BinaryExpr.ResolvedOpcode.BitwiseAnd => "&",
        BinaryExpr.ResolvedOpcode.BitwiseOr => "|",
        BinaryExpr.ResolvedOpcode.BitwiseXor => "^",
        BinaryExpr.ResolvedOpcode.EqCommon => "==",
        BinaryExpr.ResolvedOpcode.NeqCommon => "!=",
        BinaryExpr.ResolvedOpcode.Lt => "<",
        BinaryExpr.ResolvedOpcode.Le => "<=",
        BinaryExpr.ResolvedOpcode.Ge => ">=",
        BinaryExpr.ResolvedOpcode.Gt => ">",
        BinaryExpr.ResolvedOpcode.LeftShift => "<<",
        BinaryExpr.ResolvedOpcode.RightShift => ">>",
        BinaryExpr.ResolvedOpcode.Add => "+",
        BinaryExpr.ResolvedOpcode.Sub => "-",
        BinaryExpr.ResolvedOpcode.Mul => "*",
        BinaryExpr.ResolvedOpcode.Div => "/",
        BinaryExpr.ResolvedOpcode.Mod => "%",
        BinaryExpr.ResolvedOpcode.SetEq => "==",
        BinaryExpr.ResolvedOpcode.MultiSetEq => "==",
        BinaryExpr.ResolvedOpcode.SeqEq => "==",
        BinaryExpr.ResolvedOpcode.MapEq => "==",
        BinaryExpr.ResolvedOpcode.ProperSubset => "<",
        BinaryExpr.ResolvedOpcode.ProperMultiSubset => "<",
        BinaryExpr.ResolvedOpcode.Subset => "<=",
        BinaryExpr.ResolvedOpcode.MultiSubset => "<=",
        BinaryExpr.ResolvedOpcode.Disjoint => "!!",
        BinaryExpr.ResolvedOpcode.MultiSetDisjoint => "!!",
        BinaryExpr.ResolvedOpcode.InSet => "in",
        BinaryExpr.ResolvedOpcode.InMultiSet => "in",
        BinaryExpr.ResolvedOpcode.InMap => "in",
        BinaryExpr.ResolvedOpcode.Union => "+",
        BinaryExpr.ResolvedOpcode.MultiSetUnion => "+",
        BinaryExpr.ResolvedOpcode.MapMerge => "+",
        BinaryExpr.ResolvedOpcode.Intersection => "*",
        BinaryExpr.ResolvedOpcode.MultiSetIntersection => "*",
        BinaryExpr.ResolvedOpcode.SetDifference => "-",
        BinaryExpr.ResolvedOpcode.MultiSetDifference => "-",
        BinaryExpr.ResolvedOpcode.MapSubtraction => "-",
        BinaryExpr.ResolvedOpcode.ProperPrefix => "<=",
        BinaryExpr.ResolvedOpcode.Prefix => "<",
        BinaryExpr.ResolvedOpcode.Concat => "+",
        BinaryExpr.ResolvedOpcode.InSeq => "in",
        _ => throw new NotImplementedException(),
      };

      throw new NotImplementedException();
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      throw new NotImplementedException();
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      throw new NotImplementedException();
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
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
      throw new NotImplementedException();
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

  }
}
