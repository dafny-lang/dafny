using System;
using System.Collections.Generic;
using Dafny;
using JetBrains.Annotations;
using DAST;
using System.Numerics;
using Microsoft.BaseTypes;
using System.Linq;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Compilers {

  class BuilderSyntaxTree<T> : ConcreteSyntaxTree {
    public readonly T Builder;

    public BuilderSyntaxTree(T builder) {
      Builder = builder;
    }

    public override ConcreteSyntaxTree Fork(int relativeIndent = 0) {
      if (Builder is StatementContainer statementContainer) {
        return new BuilderSyntaxTree<StatementContainer>(statementContainer.Fork());
      } else {
        throw new InvalidOperationException("Cannot fork builder of type " + Builder.GetType());
      }
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
      Feature.Ordinals,
      Feature.Iterators,
      Feature.Multisets,
      Feature.MapComprehensions,
      Feature.LetSuchThatExpressions,
      Feature.MethodSynthesis,
      Feature.ExternalClasses,
      Feature.NewObject,
      Feature.NonSequentializableForallStatements,
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
      Feature.SubtypeConstraintsInQuantifiers,
      Feature.TuplesWiderThan20,
    };

    private readonly List<string> Imports = new() { DafnyDefaultModule };

    private const string DafnyRuntimeModule = "_dafny";
    private const string DafnyDefaultModule = "module_";

    protected override string AssignmentSymbol { get => null; }

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

    protected override ConcreteSyntaxTree EmitCoercionIfNecessary(Type from, Type to, IToken tok, ConcreteSyntaxTree wr) {
      if (from != null && to != null && from.IsNonNullRefType != to.IsNonNullRefType) {
        if (wr is BuilderSyntaxTree<ExprContainer> stmt) {
          var nullConvert = stmt.Builder.Convert(GenType(from), GenType(to));

          if (from is UserDefinedType fromUdt && fromUdt.ResolvedClass is NonNullTypeDecl fromNonNull) {
            from = fromNonNull.RhsWithArgument(fromUdt.TypeArgs);
          }

          if (to is UserDefinedType toUdt && toUdt.ResolvedClass is NonNullTypeDecl toNonNull) {
            to = toNonNull.RhsWithArgument(toUdt.TypeArgs);
          }

          return EmitCoercionIfNecessary(from, to, tok, new BuilderSyntaxTree<ExprContainer>(nullConvert));
        } else {
          return base.EmitCoercionIfNecessary(from, to, tok, wr);
        }
      } else if (from != null && to != null && from.AsSubsetType == null && to.AsSubsetType != null) {
        if (wr is BuilderSyntaxTree<ExprContainer> stmt) {
          return new BuilderSyntaxTree<ExprContainer>(stmt.Builder.Convert(GenType(from), GenType(to)));
        } else {
          return base.EmitCoercionIfNecessary(from, to, tok, wr);
        }
      } else if (from != null && to != null && from.AsSubsetType != null && to.AsSubsetType == null) {
        if (wr is BuilderSyntaxTree<ExprContainer> stmt) {
          return new BuilderSyntaxTree<ExprContainer>(stmt.Builder.Convert(GenType(from), GenType(to)));
        } else {
          return base.EmitCoercionIfNecessary(from, to, tok, wr);
        }
      } else {
        return base.EmitCoercionIfNecessary(from, to, tok, wr);
      }
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      if (currentBuilder is ClassContainer builder) {
        List<DAST.Type> typeParams = new();
        foreach (var tp in typeParameters) {
          if (tp.Variance == TypeParameter.TPVariance.Contra) {
            throw new NotImplementedException("Contravariance in type parameters");
          }

          typeParams.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(IdProtect(tp.GetCompileName(Options)))));
        }

        return new ClassWriter(this, builder.Class(name, moduleName, typeParams, superClasses.Select(t => GenType(t)).ToList()));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TraitDecl trait, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      if (currentBuilder is TraitContainer builder) {
        List<DAST.Type> typeParams = new();
        foreach (var tp in trait.TypeArgs) {
          typeParams.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(IdProtect(tp.GetCompileName(Options)))));
        }

        return new ClassWriter(this, builder.Trait(name, typeParams));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.Iterators);
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      if (currentBuilder is DatatypeContainer builder) {
        List<DAST.Type> typeParams = new();
        foreach (var tp in dt.TypeArgs) {
          if (tp.Variance == TypeParameter.TPVariance.Contra) {
            throw new NotImplementedException("Contravariance in type parameters");
          }

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

        return new ClassWriter(this, builder.Datatype(
          dt.GetCompileName(Options),
          dt.EnclosingModuleDefinition.GetCompileName(Options),
          typeParams,
          ctors,
          dt is CoDatatypeDecl
        ));
      } else {
        throw new InvalidOperationException("Cannot declare datatype outside of a module: " + currentBuilder);
      }
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      if (currentBuilder is NewtypeContainer builder) {
        List<DAST.Statement> witnessStmts = new();
        DAST.Expression witness = null;
        if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          var buf = new ExprBuffer(null);
          var statementBuf = new StatementBuffer();
          EmitExpr(nt.Witness, false, new BuilderSyntaxTree<ExprContainer>(buf), new BuilderSyntaxTree<StatementContainer>(statementBuf));
          witness = buf.Finish();
          witnessStmts = statementBuf.PopAll();
        }

        return new ClassWriter(this, builder.Newtype(nt.GetCompileName(Options), new(), GenType(nt.BaseType), witnessStmts, witness));
      } else {
        throw new InvalidOperationException();
      }
    }

    private DAST.Type GenType(Type typ) {
      // TODO(shadaj): this is leaking Rust types into the AST, but we do need native types
      var xType = DatatypeWrapperEraser.SimplifyType(Options, typ, true);

      if (xType is BoolType) {
        return (DAST.Type)DAST.Type.create_Primitive(DAST.Primitive.create_Bool());
      } else if (xType is IntType) {
        return (DAST.Type)DAST.Type.create_Primitive(DAST.Primitive.create_Int());
      } else if (xType is RealType) {
        return (DAST.Type)DAST.Type.create_Primitive(DAST.Primitive.create_Real());
      } else if (xType.IsStringType) {
        return (DAST.Type)DAST.Type.create_Primitive(DAST.Primitive.create_String());
      } else if (xType.IsCharType) {
        return (DAST.Type)DAST.Type.create_Primitive(DAST.Primitive.create_Char());
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
      } else if (xType is SeqType seq) {
        var argType = seq.Arg;
        return (DAST.Type)DAST.Type.create_Seq(GenType(argType));
      } else if (xType is SetType set) {
        var argType = set.Arg;
        return (DAST.Type)DAST.Type.create_Set(GenType(argType));
      } else if (xType is MultiSetType multiSet) {
        var argType = multiSet.Arg;
        return (DAST.Type)DAST.Type.create_Multiset(GenType(argType));
      } else if (xType is MapType map) {
        var keyType = map.Domain;
        var valueType = map.Range;
        return (DAST.Type)DAST.Type.create_Map(GenType(keyType), GenType(valueType));
      } else if (xType is BitvectorType) {
        throw new NotImplementedException("Bitvector types");
      } else {
        throw new NotImplementedException("Type name for " + xType + " (" + typ.GetType() + ")");
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      if (currentBuilder is NewtypeContainer builder) {
        List<DAST.Statement> witnessStmts = new();
        DAST.Expression witness = null;
        if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          var statementBuf = new StatementBuffer();
          var buf = new ExprBuffer(null);
          EmitExpr(sst.Witness, false, new BuilderSyntaxTree<ExprContainer>(buf), new BuilderSyntaxTree<StatementContainer>(statementBuf));
          witness = buf.Finish();
          witnessStmts = statementBuf.PopAll();
        }

        List<DAST.Type> typeParams = new();
        foreach (var tp in sst.TypeArgs) {
          if (tp.Variance == TypeParameter.TPVariance.Contra) {
            throw new NotImplementedException("Contravariance in type parameters");
          }

          typeParams.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(tp.Name)));
        }

        builder.Newtype(sst.GetCompileName(Options), typeParams, GenType(sst.Rhs), witnessStmts, witness).Finish();
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      name = null;
      literalSuffix = null;
      needsCastAfterArithmetic = false;
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
        if (m.IsStatic) {
          foreach (var typeArg in typeArgs) {
            if (typeArg.Formal.Variance == TypeParameter.TPVariance.Contra) {
              throw new NotImplementedException("Contravariance in type parameters");
            }

            astTypeArgs.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(typeArg.Formal.GetCompileName(compiler.Options)))));
          }
        }

        List<DAST.Formal> params_ = new();
        foreach (var param in m.Ins) {
          if (param is not ImplicitFormal && !param.IsGhost) {
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

        var overridingTrait = m.OverriddenMethod?.EnclosingClass;
        var builder = this.builder.Method(
          m.IsStatic, createBody,
          overridingTrait != null ? compiler.PathFromTopLevel(overridingTrait) : null,
          m.GetCompileName(compiler.Options),
          astTypeArgs, params_,
          outTypes, outVars
        );
        methods.Add(builder);

        if (createBody) {
          return new BuilderSyntaxTree<StatementContainer>(builder);
        } else {
          // TODO(shadaj): actually create a trait
          return null;
        }
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        throw new UnsupportedFeatureException(Token.NoToken, Feature.MethodSynthesis);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {
        List<DAST.Type> astTypeArgs = new();
        foreach (var typeArg in typeArgs) {
          if (typeArg.Formal.Variance == TypeParameter.TPVariance.Contra) {
            throw new NotImplementedException("Contravariance in type parameters");
          }

          astTypeArgs.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(typeArg.Formal.GetCompileName(compiler.Options)))));
        }

        List<DAST.Formal> params_ = new();
        foreach (var param in formals) {
          if (!param.IsGhost) {
            params_.Add((DAST.Formal)DAST.Formal.create_Formal(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(param.CompileName)), compiler.GenType(param.Type)));
          }
        }

        var overridingTrait = member.OverriddenMember?.EnclosingClass;

        var builder = this.builder.Method(
          isStatic, createBody,
          overridingTrait != null ? compiler.PathFromTopLevel(overridingTrait) : null,
          name,
          astTypeArgs, params_,
          new() {
            compiler.GenType(resultType)
          }, null
        );
        methods.Add(builder);

        if (createBody) {
          return new BuilderSyntaxTree<StatementContainer>(builder);
        } else {
          return null;
        }
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok,
          bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        var overridingTrait = member.OverriddenMember?.EnclosingClass;

        var builder = this.builder.Method(
          isStatic, createBody,
          overridingTrait != null ? compiler.PathFromTopLevel(overridingTrait) : null,
          name,
          new(), new(),
          new() {
            compiler.GenType(resultType)
          }, null
        );
        methods.Add(builder);

        if (createBody) {
          return new BuilderSyntaxTree<StatementContainer>(builder);
        } else {
          return null;
        }
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

        builder.AddField((DAST.Formal)DAST.Formal.create_Formal(
          Sequence<Rune>.UnicodeFromString(name),
          compiler.GenType(type)
        ), rhsExpr);
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

    protected override void EmitReturnExpr(string returnExpr, ConcreteSyntaxTree wr) {
      if (returnExpr == "PLACEBO") {
        if (bufferedInitializationValue == null) {
          throw new InvalidOperationException("Expected a buffered value to have been populated because rhs != null");
        }

        var rhsValue = bufferedInitializationValue;
        bufferedInitializationValue = null;

        if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
          var returnBuilder = stmtContainer.Builder.Return();
          returnBuilder.AddExpr(rhsValue);
        } else {
          throw new InvalidOperationException();
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IToken tok) {
      type = DatatypeWrapperEraser.SimplifyType(Options, type);
      return type.ToString();
    }

    protected override ConcreteSyntaxTree EmitMethodReturns(Method m, ConcreteSyntaxTree wr) {
      var beforeReturnBlock = wr.Fork();
      EmitReturn(m.Outs, wr);
      return beforeReturnBlock;
    }

    protected override ConcreteSyntaxTree EmitTailCallStructure(MemberDecl member, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var recBuilder = stmtContainer.Builder.TailRecursive();
        return new BuilderSyntaxTree<StatementContainer>(recBuilder);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        stmtContainer.Builder.AddStatement((DAST.Statement)DAST.Statement.create_JumpTailCallStart());
      } else {
        throw new InvalidOperationException();
      }
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
        type = type.NormalizeExpandKeepConstraints();
        if (type.AsNewtype != null && type.AsNewtype.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          var buf = new ExprBuffer(null);
          EmitExpr(type.AsNewtype.Witness, false, new BuilderSyntaxTree<ExprContainer>(buf), null);
          bufferedInitializationValue = buf.Finish();
        } else if (type.AsSubsetType != null && type.AsSubsetType.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          var buf = new ExprBuffer(null);
          EmitExpr(type.AsSubsetType.Witness, false, new BuilderSyntaxTree<ExprContainer>(buf), null);
          bufferedInitializationValue = buf.Finish();
        } else if (type.AsDatatype != null && type.AsDatatype.Ctors.Count == 1 && type.AsDatatype.Ctors[0].EnclosingDatatype is TupleTypeDecl tupleDecl) {
          var elems = new List<DAST.Expression>();
          for (var i = 0; i < tupleDecl.Ctors[0].Formals.Count; i++) {
            if (!tupleDecl.Ctors[0].Formals[i].IsGhost) {
              TypeInitializationValue(type.TypeArgs[i], wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
              elems.Add(bufferedInitializationValue);
              bufferedInitializationValue = null;
            }
          }

          bufferedInitializationValue = (DAST.Expression)DAST.Expression.create_Tuple(Sequence<DAST.Expression>.FromArray(elems.ToArray()));
        } else {
          bufferedInitializationValue = (DAST.Expression)DAST.Expression.create_InitializationValue(GenType(type));
        }
        return "PLACEBO"; // used by DeclareLocal(Out)Var
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IToken tok, bool omitTypeArguments) {
      return fullCompileName;
    }

    protected override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IToken tok, MemberDecl member) {
      ExprContainer actualBuilder;
      if (wr is BuilderSyntaxTree<ExprContainer> st) {
        actualBuilder = st.Builder;
      } else {
        throw new InvalidOperationException();
      }

      EmitTypeName_Companion(type, new BuilderSyntaxTree<ExprContainer>(actualBuilder), wr, tok, member);
      return "";
    }

    protected override void EmitTypeName_Companion(Type type, ConcreteSyntaxTree wr, ConcreteSyntaxTree surrounding, IToken tok, MemberDecl member) {
      if (wr is BuilderSyntaxTree<ExprContainer> container) {
        type = UserDefinedType.UpcastToMemberEnclosingType(type, member);

        if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
            DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) {
          container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(udt.ResolvedClass)));
        } else {
          container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(type.AsTopLevelTypeWithMembers)));
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitNameAndActualTypeArgs(string protectedName, List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> st && st.Builder is CallExprBuilder callExpr) {
        callExpr.SetName(protectedName);
      } else if (wr is BuilderSyntaxTree<ExprContainer> st2 && st2.Builder is CallStmtBuilder callStmt) {
        callStmt.SetName(protectedName);
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
          var variable = stmtContainer.Builder.DeclareAndAssign(typ, name);

          if (leaveRoomForRhs) {
            throw new InvalidOperationException();
          }
        } else if (rhs == "PLACEBO") {
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
        } else {
          throw new InvalidOperationException();
        }
      } else {
        throw new InvalidOperationException("Cannot declare local var outside of a statement container: " + wr);
      }
    }

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IToken tok, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var variable = stmtContainer.Builder.DeclareAndAssign(GenType(type), name);
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
      if (wr is BuilderSyntaxTree<ExprContainer> builder && builder.Builder is CallStmtBuilder call) {
        call.SetOuts(outTmps.Select(i => Sequence<Rune>.UnicodeFromString(i)).ToList());
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void TrCallStmt(CallStmt s, string receiverReplacement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wrStmts, ConcreteSyntaxTree wrStmtsAfterCall) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        if (s.Method == enclosingMethod && enclosingMethod.IsTailRecursive) {
          base.TrCallStmt(s, receiverReplacement, wr, wrStmts, wrStmtsAfterCall);
        } else {
          var callBuilder = stmtContainer.Builder.Call();
          base.TrCallStmt(s, receiverReplacement, new BuilderSyntaxTree<ExprContainer>(callBuilder), wrStmts, wrStmtsAfterCall);
        }
      } else {
        throw new InvalidOperationException("Cannot call statement in this context: " + currentBuilder);
      }
    }

    protected override void EmitCallToInheritedMethod(Method method, [CanBeNull] TopLevelDeclWithMembers heir, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, ConcreteSyntaxTree wStmtsAfterCall) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var callBuilder = stmtContainer.Builder.Call();
        base.EmitCallToInheritedMethod(method, heir, new BuilderSyntaxTree<ExprContainer>(callBuilder), wStmts, wStmtsAfterCall);
      } else {
        throw new InvalidOperationException("Cannot call statement in this context: " + currentBuilder);
      }
    }

    protected override void EmitMultiReturnTuple(List<Formal> outs, List<Type> outTypes, List<string> outTmps, IToken methodToken, ConcreteSyntaxTree wr) {
      // nothing to do, we auto-emit a return for the method
    }

    protected override void CompileFunctionCallExpr(FunctionCallExpr e, ConcreteSyntaxTree wr, bool inLetExprBody,
        ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var callBuilder = builder.Builder.Call();
        base.CompileFunctionCallExpr(e, new BuilderSyntaxTree<ExprContainer>(callBuilder), inLetExprBody, wStmts, tr);
      } else {
        throw new InvalidOperationException("Cannot call function in this context: " + currentBuilder);
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> st && st.Builder is CallExprBuilder callExpr) {
        callExpr.SetTypeArgs(typeArgs.Select(GenType).ToList());
      } else if (wr is BuilderSyntaxTree<ExprContainer> st2 && st2.Builder is CallStmtBuilder callStmt) {
        callStmt.SetTypeArgs(typeArgs.Select(GenType).ToList());
      } else {
        throw new InvalidOperationException("Cannot emit actual type args in this context: " + currentBuilder);
      }
    }

    private class BuilderLvalue : ILvalue {
      readonly string name;

      public BuilderLvalue(string name) {
        this.name = name;
      }

      public void EmitRead(ConcreteSyntaxTree wr) {
        throw new NotImplementedException();
      }

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
          var assign = stmtContainer.Builder.Assign();
          assign.SetLhs((DAST.AssignLhs)DAST.AssignLhs.create_Ident(Sequence<Rune>.UnicodeFromString(name)));
          return new BuilderSyntaxTree<ExprContainer>(assign);
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    private class ExprLvalue : ILvalue {
      readonly DAST.Expression expr;
      readonly DAST.AssignLhs assignExpr;

      public ExprLvalue(DAST.Expression expr, DAST.AssignLhs assignExpr) {
        this.expr = expr;
        this.assignExpr = assignExpr;
      }

      public void EmitRead(ConcreteSyntaxTree wr) {
        if (wr is BuilderSyntaxTree<ExprContainer> exprContainer) {
          exprContainer.Builder.AddExpr(expr);
        } else {
          throw new InvalidOperationException();
        }
      }

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        if (assignExpr == null) {
          throw new NotImplementedException();
        }

        if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
          var assign = stmtContainer.Builder.Assign();
          assign.SetLhs(assignExpr);
          return new BuilderSyntaxTree<ExprContainer>(assign);
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    protected override void EmitAssignment(string lhs, Type/*?*/ lhsType, string rhs, Type/*?*/ rhsType, ConcreteSyntaxTree wr) {
      throw new InvalidOperationException("Cannot use stringified version of assignment");
    }

    protected override ILvalue IdentLvalue(string var) {
      return new BuilderLvalue(var);
    }

    protected override ILvalue SeqSelectLvalue(SeqSelectExpr ll, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var sourceBuf = new ExprBuffer(null);
      EmitExpr(ll.Seq, false, new BuilderSyntaxTree<ExprContainer>(sourceBuf), wStmts);

      var indexBuf = new ExprBuffer(null);
      EmitExpr(ll.E0, false, new BuilderSyntaxTree<ExprContainer>(indexBuf), wStmts);

      var source = sourceBuf.Finish();
      var index = indexBuf.Finish();

      return new ExprLvalue(
        (DAST.Expression)DAST.Expression.create_Index(source, index),
        (DAST.AssignLhs)DAST.AssignLhs.create_Index(source, index)
      );
    }

    protected override ILvalue MultiSelectLvalue(MultiSelectExpr ll, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        ExprBuffer buffer = new(null);
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
      if (createContinueLabel) {
        return wr;
      }

      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var labelBuilder = stmtContainer.Builder.Labeled(label);
        return new BuilderSyntaxTree<StatementContainer>(labelBuilder);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        stmtContainer.Builder.AddStatement((DAST.Statement)DAST.Statement.create_Break(
          label == null ? Optional<ISequence<Rune>>.create_None() : Optional<ISequence<Rune>>.create_Some(Sequence<Rune>.UnicodeFromString(label))
        ));
      } else {
        throw new InvalidOperationException();
      }
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
      if (wr is BuilderSyntaxTree<StatementContainer> container) {
        container.Builder.AddStatement((DAST.Statement)DAST.Statement.create_Halt());
      } else {
        throw new InvalidOperationException();
      }
    }

    private readonly Stack<ElseBuilder> elseBuilderStack = new();

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var ifBuilder = statementContainer.Builder.IfElse();
        if (hasElse) {
          elseBuilderStack.Push(ifBuilder.Else());
        }

        guardWriter = new BuilderSyntaxTree<ExprContainer>(ifBuilder);
        return new BuilderSyntaxTree<StatementContainer>(ifBuilder);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      if (elseBuilderStack.Count > 0) {
        return new BuilderSyntaxTree<StatementContainer>(elseBuilderStack.Pop());
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
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var whileBuilder = statementContainer.Builder.While();
        guardWriter = new BuilderSyntaxTree<ExprContainer>(whileBuilder);
        return new BuilderSyntaxTree<StatementContainer>(whileBuilder);
      } else {
        throw new InvalidOperationException();
      }
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
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var ctor = (Constructor)initCall?.Method;
        var arguments = Enumerable.Empty<DAST.Expression>();
        if (ctor != null && ctor.IsExtern(Options, out _, out _)) {
          // the arguments of any external constructor are placed here
          arguments = ctor.Ins.Select((f, i) => (f, i))
            .Where(tp => !tp.f.IsGhost)
            .Select(tp => {
              var buf = new ExprBuffer(null);
              var localWriter = new BuilderSyntaxTree<ExprContainer>(buf);
              EmitExpr(initCall.Args[tp.i], false, localWriter, wStmts);
              return buf.Finish();
            });
        }

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_New(
          PathFromTopLevel(type.AsTopLevelTypeWithMembers),
          Sequence<DAST.Expression>.FromArray(arguments.ToArray())
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<string> dimensions,
      bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new InvalidOperationException();
    }

    protected override void EmitNewArray(Type elementType, IToken tok, List<Expression> dimensions, bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var dimensionsAST = dimensions.Select(d => {
          var buf = new ExprBuffer(null);
          var localWriter = new BuilderSyntaxTree<ExprContainer>(buf);
          EmitExpr(d, false, localWriter, wStmts);
          return buf.Finish();
        }).ToArray();

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_NewArray(
          Sequence<DAST.Expression>.FromArray(dimensionsAST)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitIdentifier(string ident, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(
          Sequence<Rune>.UnicodeFromString(ident)
        ));
      } else {
        throw new InvalidOperationException("Expected ExprContainer, got " + wr.GetType());
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        DAST.Expression baseExpr;

        switch (e) {
          case CharLiteralExpr c:
            var codePoint = Util.UnescapedCharacters(Options, (string)c.Value, false).Single();
            baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_CharLiteral(
              new Rune(codePoint)
            ));
            break;
          case StringLiteralExpr str:
            baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_StringLiteral(
              Sequence<Rune>.UnicodeFromString(str.AsStringLiteral())
            ));
            break;
          case StaticReceiverExpr:
            if (e.Type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
                DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) {
              baseExpr = (DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(udt.ResolvedClass));
            } else {
              baseExpr = (DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(e.Type.AsTopLevelTypeWithMembers));
            }
            break;
          default:
            DAST.Type baseType;
            if (e.Type.AsNewtype != null) {
              baseType = GenType(e.Type.AsNewtype.BaseType);
            } else if (e.Type.AsSubsetType != null) {
              baseType = GenType(e.Type.AsSubsetType.Rhs);
            } else {
              baseType = GenType(e.Type);
            }

            switch (e.Value) {
              case null:
                baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_Null());
                break;
              case bool value:
                baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(value));
                break;
              case BigInteger integer:
                baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_IntLiteral(
                  Sequence<Rune>.UnicodeFromString(integer.ToString()),
                  baseType
                ));
                break;
              case BigDec n:
                var mantissaStr = n.Mantissa.ToString();
                var denominator = "1";
                if (n.Exponent > 0) {
                  for (var i = 0; i < n.Exponent; i++) {
                    mantissaStr += "0";
                  }
                } else {
                  for (var i = 0; i < -n.Exponent; i++) {
                    denominator += "0";
                  }
                }

                baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_DecLiteral(
                  Sequence<Rune>.UnicodeFromString(mantissaStr),
                  Sequence<Rune>.UnicodeFromString(denominator),
                  baseType
                ));
                break;
              default:
                // TODO: This may not be exhaustive
                throw new cce.UnreachableException();
            }
            break;
        }

        if (e.Type.AsNewtype != null) {
          baseExpr = (DAST.Expression)DAST.Expression.create_Convert(baseExpr, GenType(e.Type.AsNewtype.BaseType), GenType(e.Type));
        } else if (e.Type.AsSubsetType != null) {
          baseExpr = (DAST.Expression)DAST.Expression.create_Convert(baseExpr, GenType(e.Type.AsSubsetType.Rhs), GenType(e.Type));
        }

        builder.Builder.AddExpr(baseExpr);
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
      if (udt.IsArrowType) {
        var arrow = udt.AsArrowType;
        return (DAST.Type)DAST.Type.create_Arrow(
          Sequence<DAST.Type>.FromArray(arrow.Args.Select(m => GenType(m)).ToArray()),
          GenType(arrow.Result)
        );
      } else if (udt.IsArrayType) {
        return (DAST.Type)DAST.Type.create_Array(GenType(udt.TypeArgs[0]));
      }

      var cl = udt.ResolvedClass;
      switch (cl) {
        case TypeParameter:
          return (DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(IdProtect(udt.GetCompileName(Options))));
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

      bool nonNull = true;
      if (topLevel is NonNullTypeDecl non) {
        topLevel = non.Rhs.AsTopLevelTypeWithMembers;
      } else if (topLevel is ClassLikeDecl) {
        nonNull = false;
      }

      ResolvedType resolvedType;
      if (topLevel is NewtypeDecl newType) {
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Newtype(GenType(newType.BaseType));
      } else if (topLevel is TraitDecl) {
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Trait(path);
      } else if (topLevel is DatatypeDecl) {
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Datatype(path);
      } else if (topLevel is ClassDecl) {
        // TODO(shadaj): have a separate type when we properly support classes
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Datatype(path);
      } else if (topLevel is SubsetTypeDecl subsetType) {
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Newtype(GenType(subsetType.Rhs));
      } else {
        throw new InvalidOperationException(topLevel.GetType().ToString());
      }

      DAST.Type baseType = (DAST.Type)DAST.Type.create_Path(
        path,
        Sequence<DAST.Type>.FromArray(typeArgs.Select(m => GenType(m)).ToArray()),
        resolvedType
      );

      if (nonNull) {
        return baseType;
      } else {
        return (DAST.Type)DAST.Type.create_Nullable(baseType);
      }
    }

    public override ConcreteSyntaxTree Expr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
      if (currentBuilder is ExprContainer container) {
        EmitExpr(expr, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(container), wStmts);
        return new ConcreteSyntaxTree();
      } else {
        throw new InvalidOperationException();
      }
    }

    public override void EmitExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var actualWr = wr;
      if (currentBuilder is ExprBuffer buf && wr is not BuilderSyntaxTree<ExprContainer>) {
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
      } else if (expr is BinaryExpr bin) {
        var origBuilder = currentBuilder;
        base.EmitExpr(expr, inLetExprBody, actualWr, wStmts);
        currentBuilder = origBuilder;
      } else if (expr is IdentifierExpr) {
        // we don't need to create a copy of the identifier, that's language specific
        base.EmitExpr(expr, false, actualWr, wStmts);
      } else {
        base.EmitExpr(expr, inLetExprBody, actualWr, wStmts);
      }
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_This());
      } else {
        throw new InvalidOperationException();
      }
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
            dtv.Ctor.EnclosingDatatype is CoDatatypeDecl,
            Sequence<_System._ITuple2<ISequence<Rune>, DAST.Expression>>.FromArray(namedContents.ToArray())
          ));
        }
      } else {
        throw new InvalidOperationException("Cannot emit datatype value outside of expression context: " + wr.GetType() + ", " + currentBuilder);
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
        case SpecialField.ID.ArrayLength:
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
        return new ExprLvalue(objExpr, null);
      } else if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue) {
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(true)), null);
      } else if (member is DatatypeDestructor dtor) {
        if (dtor.EnclosingClass is TupleTypeDecl) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_TupleSelect(
            objExpr,
            int.Parse(dtor.CorrespondingFormals[0].NameForCompilation)
          ), null);
        } else {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member is ConstantField,
            member.EnclosingClass is DatatypeDecl
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options))
          ));
        }
      } else if (member is SpecialField arraySpecial && arraySpecial.SpecialId == SpecialField.ID.ArrayLength) {
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_ArrayLen(objExpr), null);
      } else if (member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(compiledName),
          member is ConstantField,
          member.EnclosingClass is DatatypeDecl
        ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(compiledName)
        ));
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_TypeTest(
          objExpr,
          PathFromTopLevel(objType.AsTopLevelTypeWithMembers),
          Sequence<Rune>.UnicodeFromString(fieldName.Substring(3))
        ), null);
      } else {
        if (expectedType.IsArrowType) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_SelectFn(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member.EnclosingClass is DatatypeDecl,
            member.IsStatic,
            expectedType.AsArrowType.Arity
          ), null);
        } else if (internalAccess && (member is ConstantField || member.EnclosingClass is TraitDecl)) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString("_" + member.GetCompileName(Options)),
            false,
            member.EnclosingClass is DatatypeDecl
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString("_" + member.GetCompileName(Options))
          ));
        } else {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member is ConstantField,
            member.EnclosingClass is DatatypeDecl
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options))
          ));
        }
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
      var sourceBuf = new ExprBuffer(null);
      EmitExpr(source, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(sourceBuf), wStmts);

      var indexBuf = new ExprBuffer(null);
      EmitExpr(index, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(indexBuf), wStmts);

      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Index(
          sourceBuf.Finish(),
          indexBuf.Finish()
        ));
      } else {
        throw new InvalidOperationException();
      }
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
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var argsAST = new List<DAST.Expression>();
        foreach (var arg in arguments) {
          var argReceiver = new ExprBuffer(null);
          EmitExpr(arg, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(argReceiver), wStmts);
          argsAST.Add(argReceiver.Finish());
        }

        var funcReceiver = new ExprBuffer(null);
        EmitExpr(function, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(funcReceiver), wStmts);
        var funcAST = funcReceiver.Finish();

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Apply(funcAST, Sequence<DAST.Expression>.FromArray(argsAST.ToArray())));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      throw new NotImplementedException();
    }

    protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
        List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, ctor.EnclosingDatatype, out var coreDtor)) {
          Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
          Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
          source(wr);
        } else {
          var buf = new ExprBuffer(null);
          source(new BuilderSyntaxTree<ExprContainer>(buf));
          var sourceAST = buf.Finish();
          if (ctor.EnclosingDatatype is TupleTypeDecl) {
            builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_TupleSelect(
              sourceAST,
              int.Parse(dtor.NameForCompilation)
            ));
          } else {
            builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Select(
              sourceAST,
              Sequence<Rune>.UnicodeFromString(dtor.CompileName),
              false,
              true
            ));
          }
        }
      }
    }

    protected override bool TargetLambdasRestrictedToExpressions => true;
    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var formals = new List<DAST.Formal>();
        for (int i = 0; i < inTypes.Count; ++i) {
          formals.Add((DAST.Formal)DAST.Formal.create_Formal(
            Sequence<Rune>.UnicodeFromString(inNames[i]),
            GenType(inTypes[i])
          ));
        }

        var retType = GenType(resultType);

        return new BuilderSyntaxTree<StatementContainer>(builder.Builder.Lambda(formals, retType));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitLambdaApply(ConcreteSyntaxTree wr, out ConcreteSyntaxTree wLambda, out ConcreteSyntaxTree wArg) {
      if (wr is BuilderSyntaxTree<StatementContainer> builder) {
        var lambda = builder.Builder.Call();
        wLambda = new BuilderSyntaxTree<ExprContainer>(lambda);
        wArg = new BuilderSyntaxTree<ExprContainer>(lambda);
      } else if (wr is BuilderSyntaxTree<ExprContainer> exprBuilder) {
        var lambda = exprBuilder.Builder.Call();
        wLambda = new BuilderSyntaxTree<ExprContainer>(lambda);
        wArg = new BuilderSyntaxTree<ExprContainer>(lambda);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var iife = builder.Builder.IIFE(bvName, GenType(bvType));
        wrRhs = new BuilderSyntaxTree<ExprContainer>(iife.RhsBuilder());
        wrBody = new BuilderSyntaxTree<ExprContainer>(iife);
      } else {
        throw new InvalidOperationException("Invalid context for IIFE: " + wr.GetType());
      }
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
      if (wr is BuilderSyntaxTree<ExprContainer> container) {
        var buf = new ExprBuffer(null);
        EmitExpr(expr, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(buf), null);

        switch (op) {
          case ResolvedUnaryOp.BoolNot: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_Not(),
                buf.Finish()
              ));
              break;
            }
          case ResolvedUnaryOp.BitwiseNot: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_BitwiseNot(),
                buf.Finish()
              ));
              break;
            }
          case ResolvedUnaryOp.Cardinality: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_Cardinality(),
                buf.Finish()
              ));
              break;
            }
        }
      } else {
        throw new InvalidOperationException();
      }
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

        currentBuilder = builder.Builder.BinOp(opString);
        // cleaned up by EmitExpr
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var guardBuffer = new ExprBuffer(null);
        var thnBuffer = new ExprBuffer(null);
        var elsBuffer = new ExprBuffer(null);
        EmitExpr(guard, false, new BuilderSyntaxTree<ExprContainer>(guardBuffer), wStmts);
        EmitExpr(thn, false, new BuilderSyntaxTree<ExprContainer>(thnBuffer), wStmts);
        EmitExpr(els, false, new BuilderSyntaxTree<ExprContainer>(elsBuffer), wStmts);
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Ite(
          guardBuffer.Finish(),
          thnBuffer.Finish(),
          elsBuffer.Finish()
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      throw new NotImplementedException();
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        if (e.ToType.Equals(e.E.Type)) {
          EmitExpr(e.E, inLetExprBody, builder, wStmts);
        } else {
          EmitExpr(e.E, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(builder.Builder.Convert(
            GenType(e.E.Type),
            GenType(e.ToType)
          )), wStmts);
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_TypeTest(
          DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(source)),
          PathFromTopLevel(ctor.EnclosingDatatype),
          Sequence<Rune>.UnicodeFromString(ctor.GetCompileName(Options))
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IToken tok, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(tok, Feature.TypeTests);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var elementsAST = new List<DAST.Expression>();
        foreach (var e in elements) {
          var buffer = new ExprBuffer(null);
          EmitExpr(e, false, new BuilderSyntaxTree<ExprContainer>(buffer), wStmts);
          elementsAST.Add(buffer.Finish());
        }

        if (ct is SetType set) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SetValue(
            Sequence<DAST.Expression>.FromArray(elementsAST.ToArray())
          ));
        } else if (ct is MultiSetType multiSet) {
          throw new NotImplementedException();
        } else if (ct is SeqType seq) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SeqValue(
            Sequence<DAST.Expression>.FromArray(elementsAST.ToArray())
          ));
        } else {
          throw new InvalidOperationException();
        }
      } else {
        throw new InvalidOperationException();
      }
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
      throw new UnsupportedFeatureException(Token.NoToken, Feature.ExactBoundedPool);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      throw new UnsupportedFeatureException(Token.NoToken, Feature.RunAllTests);
    }

  }
}
