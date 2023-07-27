using System;
using System.Collections.Generic;
using Dafny;
using JetBrains.Annotations;
using DAST;
using System.Numerics;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using System.Linq;

namespace Microsoft.Dafny.Compilers {

  class BuilderSyntaxTree<T> : ConcreteSyntaxTree {
    public readonly T Builder;

    public BuilderSyntaxTree(T builder) {
      Builder = builder;
    }

    public override ConcreteSyntaxTree Fork(int relativeIndent = 0) {
      return new BuilderSyntaxTree<T>(Builder);
    }

    public override ConcreteSyntaxTree ForkInParens() {
      // TODO(shadaj): perhaps should check if we are an expr container
      return new BuilderSyntaxTree<T>(Builder);
    }
  }

  class DafnyCompiler : SinglePassCompiler {
    ProgramBuilder items;
    public object currentBuilder;

    public void Start() {
      if (items != null) {
        throw new InvalidOperationException("");
      }

      items = new ProgramBuilder();
      this.currentBuilder = items;
    }

    public List<Module> Build() {
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

    public override void EndStmt(ConcreteSyntaxTree wr) {
      if (currentBuilder is CallStmtBuilder callBuilder) {
        callBuilder.Finish();
        currentBuilder = callBuilder.returnTo;
      } else {
        throw new InvalidOperationException("Unxpected current builder when ending statement: " + currentBuilder);
      }
    }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
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
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Traits);
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      if (currentBuilder is DatatypeContainer builder) {
        List<DAST.Type> typeParams = new();
        foreach (var tp in dt.TypeArgs) {
          typeParams.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(IdProtect(tp.GetCompileName(Options)))));
        }

        List<DAST.DatatypeCtor> ctors = new();
        foreach (var ctor in dt.Ctors) {
          List<DAST.Formal> args = new();
          foreach (var arg in ctor.Formals) {
            if (!arg.IsGhost) {
              args.Add((DAST.Formal)DAST.Formal.create_Formal(Sequence<Rune>.UnicodeFromString(arg.CompileName), GenType(arg.Type)));
            }
          }
          ctors.Add((DAST.DatatypeCtor)DAST.DatatypeCtor.create_DatatypeCtor(Sequence<Rune>.UnicodeFromString(ctor.GetCompileName(Options)), Sequence<DAST.Formal>.FromArray(args.ToArray()), ctor.Formals.Count > 0));
        }

        return new ClassWriter(this, builder.Datatype(dt.GetCompileName(Options), Sequence<Rune>.UnicodeFromString(dt.EnclosingModuleDefinition.GetCompileName(Options)), typeParams, ctors));
      } else {
        throw new InvalidOperationException("Cannot declare datatype outside of a module: " + currentBuilder);
      }
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      if (currentBuilder is NewtypeContainer builder) {
        return new ClassWriter(this, builder.Newtype(nt.GetCompileName(Options), GenType(nt.BaseType)));
      } else {
        throw new InvalidOperationException();
      }
    }

    private DAST.Type GenType(Type typ) {
      // TODO(shadaj): this is leaking Rust types into the AST, but we do need native types
      var xType = DatatypeWrapperEraser.SimplifyType(Options, typ);

      if (xType is BoolType) {
        return (DAST.Type)DAST.Type.create_Primitive(DAST.Primitive.create_Bool());
      } else if (xType is IntType) {
        return (DAST.Type)DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("i32"));
      } else if (xType is RealType) {
        return (DAST.Type)DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("f32"));
      } else if (xType.IsStringType) {
        return (DAST.Type)DAST.Type.create_Primitive(DAST.Primitive.create_String());
      } else if (xType is UserDefinedType udt) {
        if (udt.ResolvedClass is TypeParameter tp) {
          if (thisContext != null && thisContext.ParentFormalTypeParametersToActuals.TryGetValue(tp, out var instantiatedTypeParameter)) {
            return GenType(instantiatedTypeParameter);
          }
        }

        return FullTypeNameAST(udt, null);
      } else if (AsNativeType(typ) != null) {
        return (DAST.Type)(AsNativeType(typ).Sel switch {
          NativeType.Selection.Byte => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("u8")),
          NativeType.Selection.SByte => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("i8")),
          NativeType.Selection.Short => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("i16")),
          NativeType.Selection.UShort => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("u16")),
          NativeType.Selection.Int => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("i32")),
          NativeType.Selection.UInt => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("u32")),
          NativeType.Selection.Long => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("i64")),
          NativeType.Selection.ULong => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("u64")),
          _ => throw new InvalidOperationException(),
        });
      } else {
        throw new NotImplementedException("Type name for " + typ);
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      // TODO(shadaj): currently ignores subset types because they appear in the prelude
      // throw new NotImplementedException();
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      throw new NotImplementedException();
    }

    private class ClassWriter : IClassWriter {
      private readonly DafnyCompiler compiler;
      private readonly ClassLike builder;
      private readonly List<MethodBuilder> methods = new();

      public ClassWriter(DafnyCompiler compiler, ClassLike builder) {
        this.compiler = compiler;
        this.builder = builder;
      }

      public ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        List<DAST.Type> astTypeArgs = new();
        foreach (var typeArg in typeArgs) {
          astTypeArgs.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(typeArg.Formal.GetCompileName(compiler.Options)))));
        }

        List<DAST.Formal> params_ = new();
        foreach (var param in m.Ins) {
          if (param is not ImplicitFormal) {
            params_.Add((DAST.Formal)DAST.Formal.create_Formal(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(param.CompileName)), compiler.GenType(param.Type)));
          }
        }

        List<ISequence<Rune>> outVars = new();
        List<DAST.Type> outTypes = new();
        foreach (var outVar in m.Outs) {
          if (!outVar.IsGhost) {
            outVars.Add(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(outVar.CompileName)));
            outTypes.Add(compiler.GenType(outVar.Type));
          }
        }

        var builder = this.builder.Method(m.IsStatic, m.GetCompileName(compiler.Options), astTypeArgs, params_, outTypes, outVars);
        methods.Add(builder);
        return new BuilderSyntaxTree<StatementContainer>(builder);
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {
        List<DAST.Type> astTypeArgs = new();
        foreach (var typeArg in typeArgs) {
          astTypeArgs.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(typeArg.Formal.GetCompileName(compiler.Options)))));
        }

        List<DAST.Formal> params_ = new();
        foreach (var param in formals) {
          params_.Add((DAST.Formal)DAST.Formal.create_Formal(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(param.CompileName)), compiler.GenType(param.Type)));
        }

        var builder = this.builder.Method(isStatic, name, astTypeArgs, params_, new() {
          compiler.GenType(resultType)
        }, null);
        methods.Add(builder);
        return new BuilderSyntaxTree<StatementContainer>(builder);
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
        DAST.Expression rhsExpr = null;
        if (rhs != null) {
          rhsExpr = compiler.bufferedInitializationValue;
          compiler.bufferedInitializationValue = null;

          if (rhsExpr == null) {
            throw new InvalidOperationException();
          }
        }

        // TODO(shadaj): do something with rhsExpr

        builder.AddField((DAST.Formal)DAST.Formal.create_Formal(
          Sequence<Rune>.UnicodeFromString(name),
          compiler.GenType(type)
        ));
      }

      public void InitializeField(Field field, Type instantiatedFieldType, TopLevelDeclWithMembers enclosingClass) {
        throw new cce.UnreachableException();
      }

      public ConcreteSyntaxTree ErrorWriter() => null;

      public void Finish() {
        foreach (var method in methods) {
          builder.AddMethod(method.Build());
        }

        compiler.currentBuilder = builder.Finish();
      }
    }

    protected override ConcreteSyntaxTree EmitReturnExpr(ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        return new BuilderSyntaxTree<ExprContainer>(stmtContainer.Builder.Return());
      } else {
        throw new InvalidOperationException();
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
        bufferedInitializationValue = (DAST.Expression)DAST.Expression.create_InitializationValue(GenType(type));
        return ""; // used by DeclareLocal(Out)Var
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      return fullCompileName;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      type = UserDefinedType.UpcastToMemberEnclosingType(type, member);

      ExprContainer actualBuilder;
      if (wr is BuilderSyntaxTree<ExprContainer> st) {
        actualBuilder = st.Builder;
      } else if (currentBuilder is CallStmtBuilder builder) {
        actualBuilder = builder;
      } else {
        throw new InvalidOperationException();
      }

      if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
          DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) {
        actualBuilder.AddExpr((DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(udt.ResolvedClass)));
        return "";
      } else {
        actualBuilder.AddExpr((DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(type.AsTopLevelTypeWithMembers)));
        return "";
      }
    }

    protected override void EmitNameAndActualTypeArgs(string protectedName, List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> st && st.Builder is CallExprBuilder callExpr) {
        callExpr.SetName(protectedName);
      } else if (currentBuilder is CallStmtBuilder call) {
        call.SetName(protectedName);
      } else {
        throw new InvalidOperationException();
      }

      base.EmitNameAndActualTypeArgs(protectedName, typeArgs, tok, wr);
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      needsTypeParameter = false;
      needsTypeDescriptor = false;
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void DeclareLocalVar(string name, Type type, IToken tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var typ = GenType(type);

        if (rhs == null) {
          // we expect an initializer to come *after* this declaration
          var variable = stmtContainer.Builder.DeclareAndAssign(typ);
          variable.SetName(name);

          if (leaveRoomForRhs) {
            throw new InvalidOperationException();
          } else {
            variable.AddExpr(null);
          }
        } else {
          if (bufferedInitializationValue == null) {
            throw new InvalidOperationException("Expected a buffered value to have been populated because rhs != null");
          }

          var rhsValue = bufferedInitializationValue;
          bufferedInitializationValue = null;

          stmtContainer.Builder.AddStatement(
            (DAST.Statement)DAST.Statement.create_DeclareVar(
              Sequence<Rune>.UnicodeFromString(name),
              typ,
              DAST.Optional<DAST._IExpression>.create_Some(rhsValue)
            )
          );
        }
      } else {
        throw new InvalidOperationException("Cannot declare local var outside of a statement container: " + wr);
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var variable = stmtContainer.Builder.DeclareAndAssign(GenType(type));
        variable.SetName(name);
        return new BuilderSyntaxTree<ExprContainer>(variable);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IToken tok, string rhs, bool useReturnStyleOuts,
        ConcreteSyntaxTree wr) {
      DeclareLocalVar(name, type, tok, true, rhs, wr);
    }

    protected override void EmitCallReturnOuts(List<string> outTmps, ConcreteSyntaxTree wr) {
      if (currentBuilder is CallStmtBuilder call) {
        call.SetOuts(outTmps.Select(i => Sequence<Rune>.UnicodeFromString(i)).ToList());
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void TrCallStmt(CallStmt s, string receiverReplacement, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        currentBuilder = stmtContainer.Builder.Call(currentBuilder);
        base.TrCallStmt(s, receiverReplacement, wr);
        // finished by EndStmt, because the call needs to be finished
        // before followup assignments should be emitted
      } else {
        throw new InvalidOperationException("Cannot call statement in this context: " + currentBuilder);
      }
    }

    protected override void CompileFunctionCallExpr(FunctionCallExpr e, ConcreteSyntaxTree wr, bool inLetExprBody,
        ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var callBuilder = builder.Builder.Call();
        base.CompileFunctionCallExpr(e, new BuilderSyntaxTree<ExprContainer>(callBuilder), inLetExprBody, wStmts, tr);
        callBuilder.Finish();
      } else {
        throw new InvalidOperationException("Cannot call function in this context: " + currentBuilder);
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> st && st.Builder is CallExprBuilder callExpr) {
        callExpr.SetTypeArgs(typeArgs.Select(GenType).ToList());
      } else if (currentBuilder is CallStmtBuilder callStmt) {
        callStmt.SetTypeArgs(typeArgs.Select(GenType).ToList());
      } else {
        throw new InvalidOperationException("Cannot emit actual type args in this context: " + currentBuilder);
      }
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
        if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
          var assign = stmtContainer.Builder.Assign();
          assign.SetName(name);
          return new BuilderSyntaxTree<ExprContainer>(assign);
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    private class ExprLvalue : ILvalue {
      readonly DAST.Expression expr;

      public ExprLvalue(DAST.Expression expr) {
        this.expr = expr;
      }

      public void EmitRead(ConcreteSyntaxTree wr) {
        if (wr is BuilderSyntaxTree<ExprContainer> exprContainer) {
          exprContainer.Builder.AddExpr(expr);
        } else {
          throw new InvalidOperationException();
        }
      }

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
      }
    }

    protected override ILvalue VariableLvalue(IVariable var) {
      return new BuilderLvalue(this, IdName(var));
    }

    protected override ILvalue SeqSelectLvalue(SeqSelectExpr ll, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        ExprBuffer buffer = new(currentBuilder);
        EmitExpr(arg, false, new BuilderSyntaxTree<ExprContainer>(buffer), wr);
        stmtContainer.Builder.Print(buffer.Finish());
      } else {
        throw new InvalidOperationException("Cannot print outside of a statement container: " + currentBuilder);
      }
    }

    protected override void EmitReturn(List<Formal> outParams, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        stmtContainer.Builder.AddStatement((DAST.Statement)DAST.Statement.create_EarlyReturn());
      } else {
        throw new InvalidOperationException("Cannot return outside of a statement container: " + currentBuilder);
      }
    }

    protected override ConcreteSyntaxTree CreateLabeledCode(string label, bool createContinueLabel, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ContinueStatements);
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

    private ElseBuilder builderForElse = null;

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      if (builderForElse != null) { // else-if
        var ifBuilder = ((StatementContainer)builderForElse).IfElse();
        builderForElse = null;

        if (hasElse) {
          builderForElse = ifBuilder.Else();
        }

        guardWriter = new BuilderSyntaxTree<ExprContainer>(ifBuilder);
        return new BuilderSyntaxTree<StatementContainer>(ifBuilder);
      } else if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var ifBuilder = statementContainer.Builder.IfElse();
        if (hasElse) {
          builderForElse = ifBuilder.Else();
        }

        guardWriter = new BuilderSyntaxTree<ExprContainer>(ifBuilder);
        return new BuilderSyntaxTree<StatementContainer>(ifBuilder);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      if (builderForElse != null) {
        var ret = new BuilderSyntaxTree<StatementContainer>(builderForElse);
        builderForElse = null;
        return ret;
      } else {
        throw new NotImplementedException();
      }
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
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ForLoops);
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ForLoops);
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

    protected override void EmitIdentifier(string ident, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(
          Sequence<Rune>.UnicodeFromString(ident)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        switch (e) {
          case CharLiteralExpr:
            throw new NotImplementedException();
          case StringLiteralExpr str:
            builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_StringLiteral(
              Sequence<Rune>.UnicodeFromString(str.AsStringLiteral())
            )));
            break;
          case StaticReceiverExpr:
            throw new NotImplementedException();
          default:
            switch (e.Value) {
              case null:
                throw new NotImplementedException();
              case bool value:
                builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(value)));
                break;
              case BigInteger integer:
                builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_IntLiteral(integer)));
                break;
              case BigDec n:
                builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_DecLiteral(
                  Sequence<Rune>.UnicodeFromString(n.ToString())
                )));
                break;
              default:
                // TODO: This may not be exhaustive
                throw new cce.UnreachableException();
            }
            break;
        }
      } else {
        throw new InvalidOperationException("Cannot emit literal expression outside of expression context: " + wr.GetType());
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
      throw new NotImplementedException();
    }

    private DAST.Type FullTypeNameAST(UserDefinedType udt, MemberDecl member = null) {
      if (udt is ArrowType) {
        throw new NotImplementedException();
      }

      var cl = udt.ResolvedClass;
      switch (cl) {
        case TypeParameter:
          return (DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(IdProtect(udt.GetCompileName(Options))));
        case ArrayClassDecl:
          throw new NotImplementedException();
        case TupleTypeDecl:
          return (DAST.Type)DAST.Type.create_Tuple(Sequence<DAST.Type>.FromArray(
            udt.TypeArgs.Select(m => GenType(m)).ToArray()
          ));
        default:
          return TypeNameASTFromTopLevel(cl, udt.TypeArgs);
      }
    }

    private ISequence<ISequence<Rune>> PathFromTopLevel(TopLevelDecl topLevel) {
      List<ISequence<Rune>> path = new();
      path.Add(Sequence<Rune>.UnicodeFromString(topLevel.EnclosingModuleDefinition.GetCompileName(Options)));
      path.Add(Sequence<Rune>.UnicodeFromString(topLevel.GetCompileName(Options)));
      return Sequence<ISequence<Rune>>.FromArray(path.ToArray());
    }

    private DAST.Type TypeNameASTFromTopLevel(TopLevelDecl topLevel, List<Type> typeArgs) {
      var path = PathFromTopLevel(topLevel);

      ResolvedType resolvedType;
      if (topLevel is NewtypeDecl) {
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Newtype();
      } else if (topLevel is TraitDecl) {
        // TODO(shadaj): have a separate type when we properly support traits
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Newtype();
      } else if (topLevel is DatatypeDecl) {
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Datatype(path);
      } else if (topLevel is ClassDecl) {
        // TODO(shadaj): have a separate type when we properly support classes
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Datatype(path);
      } else {
        throw new InvalidOperationException(topLevel.GetType().ToString());
      }

      return (DAST.Type)DAST.Type.create_Path(
        path,
        Sequence<DAST.Type>.FromArray(typeArgs.Select(m => GenType(m)).ToArray()),
        resolvedType
      );
    }

    public override ConcreteSyntaxTree Expr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
      if (currentBuilder is ExprContainer container) {
        base.EmitExpr(expr, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(container), wStmts);
        return new ConcreteSyntaxTree();
      } else {
        throw new InvalidOperationException();
      }
    }

    public override void EmitExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var actualWr = wr;
      if (currentBuilder is CallStmtBuilder call && wr is not BuilderSyntaxTree<ExprContainer>) {
        // the writers are not currently wired properly for TrCallStmt
        actualWr = new BuilderSyntaxTree<ExprContainer>(call);
      } else if (currentBuilder is ExprBuffer buf && wr is not BuilderSyntaxTree<ExprContainer>) {
        // the writers are not currently wired properly for DatatypeValue
        actualWr = new BuilderSyntaxTree<ExprContainer>(buf);
      }

      if (expr is DatatypeValue) {
        ExprBuffer buffer = new(currentBuilder);
        var origBuilder = currentBuilder;
        currentBuilder = buffer;
        base.EmitExpr(expr, inLetExprBody, actualWr, wStmts);

        if (currentBuilder == buffer) {
          // sometimes, we don't actually call EmitDatatypeValue
          currentBuilder = origBuilder;
        }
      } else {
        base.EmitExpr(expr, inLetExprBody, actualWr, wStmts);
      }
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember) {
      throw new NotImplementedException();
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder && currentBuilder is ExprBuffer buf) {
        List<DAST.Expression> contents = buf.PopAll();
        currentBuilder = buf.parent; // pop early to make sure the receiving builder is in the expected state
        List<_System._ITuple2<ISequence<Rune>, DAST.Expression>> namedContents = new();

        int argI = 0;
        for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
          var formal = dtv.Ctor.Formals[i];
          if (formal.IsGhost) {
            continue;
          }

          var actual = contents[argI];
          namedContents.Add(_System.Tuple2<ISequence<Rune>, DAST.Expression>.create(
            Sequence<Rune>.UnicodeFromString(formal.CompileName),
            actual
          ));

          argI++;
        }

        if (argI != contents.Count) {
          throw new InvalidOperationException("Datatype constructor " + dtv.Ctor.Name + " expects " + dtv.Ctor.Formals.Count + " arguments, but " + contents.Count + " were provided");
        }

        if (dtv.Ctor.EnclosingDatatype is TupleTypeDecl tupleDecl) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Tuple(
            Sequence<DAST.Expression>.FromArray(namedContents.Select(x => x.dtor__1).ToArray())
          ));
        } else {
          var dtPath = PathFromTopLevel(dtv.Ctor.EnclosingDatatype);
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_DatatypeValue(
            dtPath,
            Sequence<Rune>.UnicodeFromString(dtv.Ctor.GetCompileName(Options)),
            Sequence<_System._ITuple2<ISequence<Rune>, DAST.Expression>>.FromArray(namedContents.ToArray())
          ));
        }
      } else {
        throw new InvalidOperationException("Cannot emit datatype value outside of expression context: " + wr.GetType());
      }
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, Type receiverType,
        out string compiledName, out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = (string)idParam;
          break;
        default:
          throw new NotImplementedException("Special field: " + id);
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
      string additionalCustomParameter = null, bool internalAccess = false) {
      var objReceiver = new ExprBuffer(null);
      obj(new BuilderSyntaxTree<ExprContainer>(objReceiver));
      var objExpr = objReceiver.Finish();

      var memberStatus = DatatypeWrapperEraser.GetMemberStatus(Options, member);

      if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.Identity) {
        return new ExprLvalue(objExpr);
      } else if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue) {
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(true)));
      } else if (member is DatatypeDestructor dtor) {
        if (dtor.EnclosingClass is TupleTypeDecl) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_TupleSelect(
            objExpr,
            int.Parse(dtor.CorrespondingFormals[0].NameForCompilation)
          ));
        } else {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member.EnclosingClass is DatatypeDecl
          ));
        }
      } else if (member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(compiledName),
          member.EnclosingClass is DatatypeDecl
        ));
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_TypeTest(
          objExpr,
          PathFromTopLevel(objType.AsTopLevelTypeWithMembers),
          Sequence<Rune>.UnicodeFromString(fieldName.Substring(3))
        ));
      } else {
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
          member.EnclosingClass is DatatypeDecl
        ));
      }
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
      if (errorWr is BuilderSyntaxTree<ExprContainer> builder) {
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

        currentBuilder = builder.Builder.BinOp(opString, this, currentBuilder);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        throw new NotImplementedException();
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        throw new NotImplementedException();
      } else {
        throw new InvalidOperationException();
      }
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
