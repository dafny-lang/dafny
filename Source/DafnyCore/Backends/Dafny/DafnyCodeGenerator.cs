using System;
using System.Collections.Generic;
using System.Diagnostics;
using Dafny;
using JetBrains.Annotations;
using DAST;
using System.Numerics;
using Microsoft.BaseTypes;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using DAST.Format;
using Std.Wrappers;

namespace Microsoft.Dafny.Compilers {

  class DafnyCodeGenerator : SinglePassCodeGenerator {
    ProgramBuilder items;
    public object currentBuilder;
    public bool emitUncompilableCode;
    public bool preventShadowing;

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

    public DafnyCodeGenerator(DafnyOptions options, ErrorReporter reporter, bool preventShadowing, bool canEmitUncompilableCode) : base(options, reporter) {
      options.SystemModuleTranslationMode = CommonOptionBag.SystemModuleMode.Include;
      if (Options?.CoverageLegendFile != null) {
        Imports.Add("DafnyProfiling");
      }

      emitUncompilableCode = options.Get(CommonOptionBag.EmitUncompilableCode) && canEmitUncompilableCode;
      this.preventShadowing = preventShadowing;
    }

    protected override string GetCompileNameNotProtected(IVariable v) {
      return preventShadowing ? v.CompileName : v.SanitizedNameShadowable;
    }

    public void AddUnsupported(string why) {
      if (emitUncompilableCode && currentBuilder is Container container) {
        container.AddUnsupported(why);
      } else {
        throw new UnsupportedInvalidOperationException(why);
      }
    }

    public void AddUnsupportedFeature(IToken token, Feature feature) {
      if (emitUncompilableCode && currentBuilder is Container container) {
        container.AddUnsupported("<i>" + feature.ToString() + "</i>");
      } else {
        throw new RecoverableUnsupportedFeatureException(token, feature);
      }
    }

    public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
      Feature.Ordinals,
      Feature.Iterators,
      Feature.Multisets,
      Feature.MapComprehensions,
      Feature.MethodSynthesis,
      Feature.ExternalClasses,
      Feature.NewObject,
      Feature.NonSequentializableForallStatements,
      Feature.MapItems,
      Feature.RunAllTests,
      Feature.ExactBoundedPool,
      Feature.SequenceDisplaysOfCharacters,
      Feature.TypeTests,
      Feature.SubsetTypeTests,
      Feature.BitvectorRotateFunctions,
      Feature.AssignSuchThatWithNonFiniteBounds,
      Feature.SequenceUpdateExpressions,
      Feature.SequenceConstructionsWithNonLambdaInitializers,
      Feature.ExternalConstructors,
      Feature.SubtypeConstraintsInQuantifiers,
      Feature.TuplesWiderThan20,
      Feature.ForLoops,
      Feature.Traits,
      Feature.RuntimeCoverageReport,
      Feature.MultiDimensionalArrays,
      Feature.NonNativeNewtypes
    };

    private readonly List<string> Imports = new() { DafnyDefaultModule };

    private const string DafnyRuntimeModule = "_dafny";
    private const string DafnyDefaultModule = "module_";

    protected override string AssignmentSymbol { get => null; }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>Call to main</i>");
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      AddUnsupported("<i>create static main</i>");
      return new BuilderSyntaxTree<ExprContainer>(
        new ExprBuffer(this), this);
    }

    protected override ConcreteSyntaxTree CreateModule(string moduleName, bool isDefault, ModuleDefinition externModule,
      string libraryName, ConcreteSyntaxTree wr) {
      if (currentBuilder is ModuleContainer moduleBuilder) {
        currentBuilder = moduleBuilder.Module(moduleName, externModule != null);
      } else {
        throw new InvalidOperationException();
      }

      return wr;
    }

    protected override void FinishModule() {
      if (currentBuilder is ModuleBuilder builder) {
        currentBuilder = builder.Finish();
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override string GetHelperModuleName() => DafnyRuntimeModule;

    private static string MangleName(string name) {
      return name;
    }

    protected override ConcreteSyntaxTree EmitCoercionIfNecessary(Type from, Type to, IToken tok, ConcreteSyntaxTree wr, Type toOrig = null) {
      if (currentBuilder is ExprBuffer buf && wr is not BuilderSyntaxTree<ExprContainer>) {
        // the writers are not currently wired properly for DatatypeValue
        wr = new BuilderSyntaxTree<ExprContainer>(buf, this);
      }

      if (from == to) {
        return wr;
      }

      if (from != null && to != null && from.IsNonNullRefType != to.IsNonNullRefType) {
        if (wr is BuilderSyntaxTree<ExprContainer> stmt) {
          var nullConvert = stmt.Builder.Convert(GenType(from), GenType(to));

          if (from is UserDefinedType fromUdt && fromUdt.ResolvedClass is NonNullTypeDecl fromNonNull) {
            from = fromNonNull.RhsWithArgument(fromUdt.TypeArgs);
          }

          if (to is UserDefinedType toUdt && toUdt.ResolvedClass is NonNullTypeDecl toNonNull) {
            to = toNonNull.RhsWithArgument(toUdt.TypeArgs);
          }

          return EmitCoercionIfNecessary(from, to, tok, new BuilderSyntaxTree<ExprContainer>(nullConvert, this));
        } else {
          return base.EmitCoercionIfNecessary(from, to, tok, wr);
        }
      } else if (from != null && to != null && (from.AsSubsetType != null || to.AsSubsetType != null)) {
        if (wr is BuilderSyntaxTree<ExprContainer> stmt) {
          return new BuilderSyntaxTree<ExprContainer>(stmt.Builder.Convert(GenType(from), GenType(to)), this);
        } else {
          return base.EmitCoercionIfNecessary(from, to, tok, wr);
        }
      } else {
        if (from == null || to == null || from.Equals(to, true)) {
          return wr;
        } else {
          AddUnsupported($"<i>Coercion</i> from {from} to {to}");
          return new BuilderSyntaxTree<ExprContainer>(
            new ExprBuffer(this), this);
        }
      }
    }

    protected override IClassWriter CreateClass(string moduleName, string name, bool isExtern, string fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IToken tok, ConcreteSyntaxTree wr) {
      if (currentBuilder is ClassContainer builder) {
        List<DAST.Type> typeParams = new();
        foreach (var tp in typeParameters) {
          var compileName = IdProtect(tp.GetCompileName(Options));
          if (!isTpSupported(tp, out var why)) {
            AddUnsupported(why);
          }

          typeParams.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compileName)));
        }

        return new ClassWriter(this, typeParams.Count > 0, builder.Class(name, moduleName, typeParams, superClasses.Select(t => GenType(t)).ToList()));
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

        return new ClassWriter(this, typeParameters.Any(), builder.Trait(name, typeParams));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(iter.tok, Feature.Iterators);
      return wr;
    }

    private static bool isTpSupported(TypeParameter tp, [CanBeNull] out string why) {
      if (tp.Variance != TypeParameter.TPVariance.Non) {
        why = $"<b>Unsupported: <i>Type variance {tp.Variance} not supported</i></b>";
        return false;
      }

      if (tp.Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified) {
        why = $"<b>Unsupported: <i>Type parameter Equality support {tp.Characteristics.EqualitySupport} not supported for type parameters</i></b>";
        return false;
      }

      why = null;
      return true;
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      if (currentBuilder is DatatypeContainer builder) {
        List<DAST.Type> typeParams = new();
        foreach (var tp in dt.TypeArgs) {
          var compileName = IdProtect(tp.GetCompileName(Options));
          if (!isTpSupported(tp, out var why) && !(dt is TupleTypeDecl)) {
            AddUnsupported(why);
          }

          typeParams.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compileName)));
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

        return new ClassWriter(this, typeParams.Count > 0, builder.Datatype(
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
        var erasedType = EraseNewtypeLayers(nt);

        List<DAST.Statement> witnessStmts = new();
        DAST.Expression witness = null;
        var buf = new ExprBuffer(null);
        var statementBuf = new StatementBuffer();
        if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          EmitExpr(
            nt.Witness, false,
            EmitCoercionIfNecessary(nt.Witness.Type, erasedType, null,
              new BuilderSyntaxTree<ExprContainer>(buf, this)),
            new BuilderSyntaxTree<StatementContainer>(statementBuf, this)
          );
          witness = buf.Finish();
          witnessStmts = statementBuf.PopAll();
        }

        return new ClassWriter(this, false, builder.Newtype(
          nt.GetCompileName(Options), new(),
          GenType(erasedType), NativeTypeToNewtypeRange(nt.NativeType), witnessStmts, witness));
      } else {
        throw new InvalidOperationException();
      }
    }

    private DAST.Type GenType(Type typ) {
      // TODO(shadaj): this is leaking Rust types into the AST, but we do need native types
      var xType = DatatypeWrapperEraser.SimplifyTypeAndTrimSubsetTypes(Options, typ);

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
          NativeType.Selection.DoubleLong => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("i128")),
          NativeType.Selection.UDoubleLong => DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("u128")),
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
        AddUnsupported("<i>Bitvector types</i>");
        return (DAST.Type)DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("Missing feature: Bitvector types"));
      } else {
        var why = "<i>Type name for " + xType + " (" + typ.GetType() + ")</i>";
        AddUnsupported(why);
        return (DAST.Type)DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString($"<b>Unsupported: {why}</b>"));
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      if (currentBuilder is NewtypeContainer builder) {
        var erasedType = EraseNewtypeLayers(sst);

        List<DAST.Statement> witnessStmts = new();
        DAST.Expression witness = null;
        var statementBuf = new StatementBuffer();
        var buf = new ExprBuffer(null);
        if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          EmitExpr(
            sst.Witness, false,
            EmitCoercionIfNecessary(sst.Witness.Type, erasedType, null, new BuilderSyntaxTree<ExprContainer>(buf, this)),
            new BuilderSyntaxTree<StatementContainer>(statementBuf, this)
          );
          witness = buf.Finish();
          witnessStmts = statementBuf.PopAll();
        }
        string baseName = sst.Var.CompileName;
        DAST.Expression baseConstraint = buf.Finish();
        var baseConstraintStmts = statementBuf.PopAll(); // TODO: Integrate in AST.

        List<DAST.Type> typeParams = new();
        foreach (var tp in sst.TypeArgs) {
          var compileName = tp.Name;
          if (!isTpSupported(tp, out var why)) {
            AddUnsupported(why);
          }

          typeParams.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compileName)));
        }

        builder.Newtype(sst.GetCompileName(Options), typeParams,
          GenType(erasedType), (NewtypeRange)NewtypeRange.create_NoRange(), witnessStmts, witness).Finish();
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
      private readonly DafnyCodeGenerator compiler;
      private readonly ClassLike builder;
      private readonly bool hasTypeArgs;
      private readonly List<MethodBuilder> methods = new();

      public ClassWriter(DafnyCodeGenerator compiler, bool hasTypeArgs, ClassLike builder) {
        this.compiler = compiler;
        this.hasTypeArgs = hasTypeArgs;
        this.builder = builder;
      }

      public ConcreteSyntaxTree CreateMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        if (m.IsStatic && this.hasTypeArgs) {
          compiler.AddUnsupported("<i>Static methods with type arguments</i>");
          return new ConcreteSyntaxTree();
        }

        List<DAST.Type> astTypeArgs = new();
        foreach (var typeArg in typeArgs) {
          var compileName = compiler.IdProtect(typeArg.Formal.GetCompileName(compiler.Options));
          if (!isTpSupported(typeArg.Formal, out var why)) {
            compiler.AddUnsupported(why);
          }

          astTypeArgs.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compileName)));
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
          return new BuilderSyntaxTree<StatementContainer>(builder, this.compiler);
        } else {
          // TODO(shadaj): actually create a trait
          return null;
        }
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        compiler.AddUnsupportedFeature(m.tok, Feature.MethodSynthesis);
        return new ConcreteSyntaxTree();
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IToken tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {
        if (isStatic && this.hasTypeArgs) {
          compiler.AddUnsupported("<i>Static functions with type arguments</i>");
          return new ConcreteSyntaxTree();
        }

        List<DAST.Type> astTypeArgs = new();
        foreach (var typeArg in typeArgs) {
          var compileName = compiler.IdProtect(typeArg.Formal.GetCompileName(compiler.Options));
          if (!isTpSupported(typeArg.Formal, out var why)) {
            compiler.AddUnsupported(why);
          }

          astTypeArgs.Add((DAST.Type)DAST.Type.create_TypeArg(Sequence<Rune>.UnicodeFromString(compileName)));
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
          return new BuilderSyntaxTree<StatementContainer>(builder, this.compiler);
        } else {
          return null;
        }
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IToken tok,
          bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        if (isStatic && this.hasTypeArgs) {
          compiler.AddUnsupported("<i>Static fields with type arguments</i>");
          return new ConcreteSyntaxTree();
        }

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
          return new BuilderSyntaxTree<StatementContainer>(builder, this.compiler);
        } else {
          return null;
        }
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IToken tok,
          bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        compiler.AddUnsupported("<i>Create Getter Setter</i>");
        if (createBody) {
          setterWriter = new ConcreteSyntaxTree();
          return new ConcreteSyntaxTree();
        } else {
          setterWriter = null;
          return null;
        }
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IToken tok, string rhs, Field field) {
        _IOption<DAST._IExpression> rhsExpr = null;
        if (rhs != null) {
          rhsExpr = compiler.bufferedInitializationValue;
          compiler.bufferedInitializationValue = null;

          if (rhsExpr == null) {
            throw new InvalidOperationException();
          }
        } else {
          rhsExpr = Option<DAST._IExpression>.create_None();
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
        return new BuilderSyntaxTree<ExprContainer>(stmtContainer.Builder.Return(), this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitReturnExpr(string returnExpr, ConcreteSyntaxTree wr) {
      if (returnExpr == "BUFFERED") {
        if (bufferedInitializationValue == null) {
          throw new InvalidOperationException("Expected a buffered value to have been populated because rhs != null");
        }

        var rhsValue = bufferedInitializationValue;
        bufferedInitializationValue = null;

        if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
          var returnBuilder = stmtContainer.Builder.Return();
          returnBuilder.AddExpr((DAST.Expression)rhsValue.dtor_value);
        } else {
          throw new InvalidOperationException();
        }
      } else {
        // TODO(shadaj): this may not be robust, we should use the writer version directly
        EmitIdentifier(returnExpr, EmitReturnExpr(wr));
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
        return new BuilderSyntaxTree<StatementContainer>(recBuilder, this);
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
      return "PLACEBO_TYPE";
    }

    // sometimes, the compiler generates the initial value before the declaration,
    // so we buffer it here
    _IOption<DAST._IExpression> bufferedInitializationValue = null;

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IToken tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      if (bufferedInitializationValue != null) {
        throw new InvalidOperationException();
      } else {
        type = type.NormalizeExpandKeepConstraints();
        if (usePlaceboValue) {
          bufferedInitializationValue = Option<DAST._IExpression>.create_None();
        } else {
          if (type.AsNewtype != null && type.AsNewtype.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
            var buf = new ExprBuffer(null);
            EmitExpr(type.AsNewtype.Witness, false, new BuilderSyntaxTree<ExprContainer>(buf, this), null);
            bufferedInitializationValue = Option<DAST._IExpression>.create_Some(buf.Finish());
          } else if (type.AsSubsetType != null && type.AsSubsetType.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
            var buf = new ExprBuffer(null);
            EmitExpr(type.AsSubsetType.Witness, false, new BuilderSyntaxTree<ExprContainer>(buf, this), null);
            bufferedInitializationValue = Option<DAST._IExpression>.create_Some(buf.Finish());
          } else if (type.AsDatatype != null && type.AsDatatype.Ctors.Count == 1 && type.AsDatatype.Ctors[0].EnclosingDatatype is TupleTypeDecl tupleDecl) {
            var elems = new List<DAST._IExpression>();
            for (var i = 0; i < tupleDecl.Ctors[0].Formals.Count; i++) {
              if (!tupleDecl.Ctors[0].Formals[i].IsGhost) {
                TypeInitializationValue(type.TypeArgs[i], wr, tok, usePlaceboValue, constructTypeParameterDefaultsFromTypeDescriptors);
                elems.Add(bufferedInitializationValue.dtor_value);
                bufferedInitializationValue = null;
              }
            }

            if (elems.Count == 1) {
              bufferedInitializationValue = Option<DAST._IExpression>.create_Some(elems[0]);
            } else {
              bufferedInitializationValue = Option<DAST._IExpression>.create_Some(
                DAST.Expression.create_Tuple(Sequence<DAST._IExpression>.FromArray(elems.ToArray()))
              );
            }
          } else if (type.IsArrowType) {
            if (emitUncompilableCode) {
              this.AddUnsupported("<i>Initializer for arrow type</i>");
            } else {
              throw new UnsupportedInvalidOperationException("<i>Initializer for arrow type</i>");
            }
          } else {
            bufferedInitializationValue = Option<DAST._IExpression>.create_Some(
              DAST.Expression.create_InitializationValue(GenType(type))
            );
          }
        }
        return "BUFFERED"; // used by DeclareLocal(Out)Var
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

      EmitTypeName_Companion(type, new BuilderSyntaxTree<ExprContainer>(actualBuilder, this), wr, tok, member);
      return "";
    }

    protected override void EmitTypeName_Companion(Type type, ConcreteSyntaxTree wr, ConcreteSyntaxTree surrounding, IToken tok, MemberDecl member) {
      if (wr is BuilderSyntaxTree<ExprContainer> container) {
        type = UserDefinedType.UpcastToMemberEnclosingType(type, member);

        if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
            DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) {
          container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(udt.ResolvedClass)));
        } else {
          if (type.AsTopLevelTypeWithMembers == null) { // git-issues/git-issue-697g.dfy while iterating over "nat"
            throw new UnsupportedFeatureException(tok, Feature.RunAllTests);
          }
          container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(type.AsTopLevelTypeWithMembers)));
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitNameAndActualTypeArgs(string protectedName, List<Type> typeArgs, IToken tok,
     Expression replacementReceiver, bool receiverAsArgument, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var st) && st.Builder is CallExprBuilder callExpr) {
        callExpr.SetName((DAST.CallName)DAST.CallName.create_Name(Sequence<Rune>.UnicodeFromString(protectedName)));
      } else if (GetExprBuilder(wr, out var st2) && st2.Builder is CallStmtBuilder callStmt) {
        callStmt.SetName((DAST.CallName)DAST.CallName.create_Name(Sequence<Rune>.UnicodeFromString(protectedName)));
      } else {
        AddUnsupported("Builder issue: wr is as " + wr.GetType() +
                                (GetExprBuilder(wr, out var st3) ?
                                  " and its builder is a " + st3.Builder.GetType() : ""
                                  ));
        return;
      }

      base.EmitNameAndActualTypeArgs(protectedName, typeArgs, tok, replacementReceiver, receiverAsArgument, wr);
    }

    protected override void TypeArgDescriptorUse(bool isStatic, bool lookasideBody, TopLevelDeclWithMembers cl, out bool needsTypeParameter, out bool needsTypeDescriptor) {
      needsTypeParameter = false;
      needsTypeDescriptor = false;
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, IToken tok, bool isInParam, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>Declare formal</i>");
      return true;
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
        } else if (rhs == "BUFFERED") {
          if (bufferedInitializationValue == null) {
            throw new InvalidOperationException(
              "Expected a buffered value to have been populated because rhs != null");
          }

          var rhsValue = bufferedInitializationValue;
          bufferedInitializationValue = null;

          stmtContainer.Builder.AddStatement(
            (DAST.Statement)DAST.Statement.create_DeclareVar(
              Sequence<Rune>.UnicodeFromString(name),
              typ,
              rhsValue
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
        return new BuilderSyntaxTree<ExprContainer>(variable, this);
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
      if (GetExprBuilder(wr, out var builder) && builder.Builder is CallStmtBuilder call) {
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
          base.TrCallStmt(s, receiverReplacement, new BuilderSyntaxTree<ExprContainer>(callBuilder, this), wrStmts, wrStmtsAfterCall);
        }
      } else {
        throw new InvalidOperationException("Cannot call statement in this context: " + currentBuilder);
      }
    }

    protected override void EmitCallToInheritedMethod(Method method, [CanBeNull] TopLevelDeclWithMembers heir, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, ConcreteSyntaxTree wStmtsAfterCall) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var callBuilder = stmtContainer.Builder.Call();
        base.EmitCallToInheritedMethod(method, heir, new BuilderSyntaxTree<ExprContainer>(callBuilder, this), wStmts, wStmtsAfterCall);
      } else {
        AddUnsupported("<i>Cannot call statement in this context</i>: " + currentBuilder);
      }
    }

    protected override void EmitMultiReturnTuple(List<Formal> outs, List<Type> outTypes, List<string> outTmps, IToken methodToken, ConcreteSyntaxTree wr) {
      // nothing to do, we auto-emit a return for the method
    }

    protected override void CompileFunctionCallExpr(FunctionCallExpr e, ConcreteSyntaxTree wr, bool inLetExprBody,
        ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr, bool alreadyCoerced) {
      var toType = thisContext == null ? e.Type : e.Type.Subst(thisContext.ParentFormalTypeParametersToActuals);
      wr = EmitCoercionIfNecessary(e.Function.Original.ResultType, toType, e.tok, wr);

      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var callBuilder = builder.Builder.Call();
        base.CompileFunctionCallExpr(e, new BuilderSyntaxTree<ExprContainer>(callBuilder, this), inLetExprBody, wStmts, tr, true);
      } else {
        throw new InvalidOperationException("Cannot call function in this context: " + currentBuilder);
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IToken tok, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var st) && st.Builder is CallExprBuilder callExpr) {
        callExpr.SetTypeArgs(typeArgs.Select(GenType).ToList());
      } else if (GetExprBuilder(wr, out var st2) && st2.Builder is CallStmtBuilder callStmt) {
        callStmt.SetTypeArgs(typeArgs.Select(GenType).ToList());
      } else {
        throw new InvalidOperationException("Cannot emit actual type args in this context: " + currentBuilder);
      }
    }

    private class BuilderLvalue : ILvalue {
      readonly string name;
      private readonly DafnyCodeGenerator compiler;

      public BuilderLvalue(string name, DafnyCodeGenerator compiler) {
        this.name = name;
        this.compiler = compiler;
      }

      public void EmitRead(ConcreteSyntaxTree wr) {
        throw new InvalidOperationException();
      }

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
          var assign = stmtContainer.Builder.Assign();
          assign.AddLhs((DAST.AssignLhs)DAST.AssignLhs.create_Ident(Sequence<Rune>.UnicodeFromString(name)));
          return new BuilderSyntaxTree<ExprContainer>(assign, this.compiler);
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    private class ExprLvalue : ILvalue {
      readonly DAST.Expression expr;
      readonly DAST.AssignLhs assignExpr;
      private readonly DafnyCodeGenerator compiler;

      public ExprLvalue(DAST.Expression expr, DAST.AssignLhs assignExpr, DafnyCodeGenerator compiler) {
        this.expr = expr;
        this.assignExpr = assignExpr;
        this.compiler = compiler;
      }

      public void EmitRead(ConcreteSyntaxTree wr) {
        if (GetExprBuilder(wr, out var exprContainer)) {
          exprContainer.Builder.AddExpr(expr);
        } else {
          compiler.AddUnsupported("<i>EmitRead</i> without ExprContainer builder");
        }
      }

      public ConcreteSyntaxTree EmitWrite(ConcreteSyntaxTree wr) {
        if (assignExpr == null) {
          throw new InvalidOperationException();
        }

        if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
          var assign = stmtContainer.Builder.Assign();
          assign.AddLhs(assignExpr);
          return new BuilderSyntaxTree<ExprContainer>(assign, this.compiler);
        } else {
          throw new InvalidOperationException();
        }
      }
    }

    protected override void EmitAssignment(string lhs, Type/*?*/ lhsType, string rhs, Type/*?*/ rhsType, ConcreteSyntaxTree wr) {
      throw new InvalidOperationException("Cannot use stringified version of assignment");
    }

    protected override ILvalue IdentLvalue(string var) {
      return new BuilderLvalue(var, this);
    }

    protected override ILvalue SeqSelectLvalue(SeqSelectExpr ll, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var sourceBuf = new ExprBuffer(null);
      EmitExpr(
        ll.Seq, false,
        EmitCoercionIfNecessary(
          ll.Seq.Type,
          ll.Seq.Type.IsNonNullRefType || !ll.Seq.Type.IsRefType ? null : UserDefinedType.CreateNonNullType((UserDefinedType)ll.Seq.Type.NormalizeExpand()),
          null, new BuilderSyntaxTree<ExprContainer>(sourceBuf, this)
        ),
        wStmts
      );

      var indexBuf = new ExprBuffer(null);
      EmitExpr(ll.E0, false, new BuilderSyntaxTree<ExprContainer>(indexBuf, this), wStmts);

      var source = sourceBuf.Finish();
      var index = indexBuf.Finish();


      DAST._ICollKind collKind;
      if (ll.Seq.Type.IsArrayType) {
        collKind = DAST.CollKind.create_Array();
      } else if (ll.Seq.Type.IsMapType) {
        collKind = DAST.CollKind.create_Map();
      } else {
        collKind = DAST.CollKind.create_Seq();
      }

      return new ExprLvalue(
        (DAST.Expression)DAST.Expression.create_Index(source, collKind, Sequence<DAST.Expression>.FromElements(index)),
        (DAST.AssignLhs)DAST.AssignLhs.create_Index(source, Sequence<DAST.Expression>.FromElements(index)),
        this
      );
    }

    protected override ILvalue MultiSelectLvalue(MultiSelectExpr ll, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(ll.tok, Feature.MultiDimensionalArrays);
    }

    protected override void EmitPrintStmt(ConcreteSyntaxTree wr, Expression arg) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        ExprBuffer buffer = new(null);
        EmitExpr(arg, false, new BuilderSyntaxTree<ExprContainer>(buffer, this), wr);
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
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var labelBuilder = stmtContainer.Builder.Labeled((createContinueLabel ? "continue_" : "goto_") + label);
        return new BuilderSyntaxTree<StatementContainer>(labelBuilder, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitBreak(string label, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        stmtContainer.Builder.AddStatement((DAST.Statement)DAST.Statement.create_Break(
          label == null ? Option<ISequence<Rune>>.create_None() : Option<ISequence<Rune>>.create_Some(Sequence<Rune>.UnicodeFromString("goto_" + label))
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitContinue(string label, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        stmtContainer.Builder.AddStatement((DAST.Statement)DAST.Statement.create_Break(
          Option<ISequence<Rune>>.create_Some(Sequence<Rune>.UnicodeFromString("continue_" + label))
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitYield(ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(Token.NoToken, Feature.Iterators);
    }

    protected override void EmitAbsurd(string message, ConcreteSyntaxTree wr) {
      // TODO(shadaj): emit correct message
      if (wr is BuilderSyntaxTree<StatementContainer> container) {
        container.Builder.AddStatement((DAST.Statement)DAST.Statement.create_Halt());
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitHalt(IToken tok, Expression messageExpr, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> container) {
        container.Builder.AddStatement((DAST.Statement)DAST.Statement.create_Halt());
      } else {
        throw new InvalidOperationException();
      }
    }

    private readonly Stack<(ElseBuilder, StatementContainer)> elseBuilderStack = new();

    protected override ConcreteSyntaxTree EmitIf(out ConcreteSyntaxTree guardWriter, bool hasElse, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var containingBuilder = statementContainer.Builder;
        if (elseBuilderStack.Count > 0 && elseBuilderStack.Peek().Item2 == statementContainer.Builder) {
          var popped = elseBuilderStack.Pop();
          statementContainer = new BuilderSyntaxTree<StatementContainer>(popped.Item1, this);
          containingBuilder = popped.Item2;
        }

        var ifBuilder = statementContainer.Builder.IfElse();
        if (hasElse) {
          elseBuilderStack.Push((ifBuilder.Else(), containingBuilder));
        }

        guardWriter = new BuilderSyntaxTree<ExprContainer>(ifBuilder, this);
        return new BuilderSyntaxTree<StatementContainer>(ifBuilder, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitBlock(ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        if (elseBuilderStack.Count > 0 && elseBuilderStack.Peek().Item2 == statementContainer.Builder) {
          return new BuilderSyntaxTree<StatementContainer>(elseBuilderStack.Pop().Item1, this);
        } else {
          return wr.Fork();
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitForStmt(IToken tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, LList<Label> labels, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(tok, Feature.ForLoops);
      return wr;
    }

    protected override ConcreteSyntaxTree CreateWhileLoop(out ConcreteSyntaxTree guardWriter, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var whileBuilder = statementContainer.Builder.While();
        guardWriter = new BuilderSyntaxTree<ExprContainer>(whileBuilder, this);
        return new BuilderSyntaxTree<StatementContainer>(whileBuilder, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar, Action<ConcreteSyntaxTree> bound, ConcreteSyntaxTree wr, string start = null) {
      AddUnsupportedFeature(Token.NoToken, Feature.ForLoops);
      return wr;
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(Token.NoToken, Feature.ForLoops);
      return wr;
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>EmitIncrementVar</i>");
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>EmitDecrementVar</i>");
    }

    protected override ConcreteSyntaxTree EmitQuantifierExpr(Action<ConcreteSyntaxTree> collection, bool isForall, Type collectionElementType, BoundVar bv, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        var collectionBuf = new ExprBuffer(null);
        collection(new BuilderSyntaxTree<ExprContainer>(collectionBuf, this));
        var collectionAST = collectionBuf.Finish();

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(false)));

        return new BuilderSyntaxTree<ExprContainer>(new ExprBuffer(null), this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override string GetQuantifierName(string bvType) {
      throw new InvalidOperationException();
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IToken tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var foreachBuilder = statementContainer.Builder.Foreach(tmpVarName, GenType(collectionElementType));
        collectionWriter = new BuilderSyntaxTree<ExprContainer>(foreachBuilder, this);
        return new BuilderSyntaxTree<StatementContainer>(foreachBuilder, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitDowncast(Type from, Type to, IToken tok, ConcreteSyntaxTree wr) {
      return EmitCoercionIfNecessary(from, to, tok, wr);
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type sourceType, bool introduceBoundVar, IToken tok, ConcreteSyntaxTree wr) {
      var w = introduceBoundVar ? DeclareLocalVar(boundVarName, boundVarType, tok, wr) : IdentLvalue(boundVarName).EmitWrite(wr);
      EmitIdentifier(tmpVarName, EmitCoercionIfNecessary(sourceType, boundVarType, tok, w));
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>CreateForeachIngredientLoop</i>");
      throw new InvalidOperationException();
    }

    protected override void EmitNew(Type type, IToken tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var ctor = (Constructor)initCall?.Method;
        var arguments = Enumerable.Empty<DAST.Expression>();
        if (ctor != null && ctor.IsExtern(Options, out _, out _)) {
          // the arguments of any external constructor are placed here
          arguments = ctor.Ins.Select((f, i) => (f, i))
            .Where(tp => !tp.f.IsGhost)
            .Select(tp => {
              var buf = new ExprBuffer(null);
              var localWriter = new BuilderSyntaxTree<ExprContainer>(buf, this);
              EmitExpr(initCall.Args[tp.i], false, localWriter, wStmts);
              return buf.Finish();
            });
        }

        var typeArgs = type.TypeArgs.Select(GenType).ToArray();

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_New(
          PathFromTopLevel(type.AsTopLevelTypeWithMembers),
          Sequence<DAST.Type>.FromArray(typeArgs),
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
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var dimensionsAST = dimensions.Select(convert).ToArray();

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_NewArray(
          Sequence<DAST.Expression>.FromArray(dimensionsAST),
          GenType(elementType)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitIdentifier(string ident, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(
          Sequence<Rune>.UnicodeFromString(ident)
        ));
      } else {
        AddUnsupported("Expected ExprContainer, got " + wr.GetType());
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (GetExprBuilder(wr, out var builder)) {
        DAST.Expression baseExpr;

        switch (e) {
          case CharLiteralExpr c:
            if (UnicodeCharEnabled) {
              var codePoint = Util.UnescapedCharacters(Options, (string)c.Value, false).Single();
              baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_CharLiteral(
                new Rune(codePoint)
              ));
            } else {
              AddUnsupported("<i>Char literal without unicode char enabled</i>");
              return;
            }
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
            DAST.Type baseType = GenType(e.Type.NormalizeToAncestorType());

            switch (e.Value) {
              case null:
                baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_Null(GenType(e.Type)));
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
      } else if (emitUncompilableCode && GetStatementBuilder(wr, out var builder2)) {
        builder2.Builder.AddStatement(StatementContainer.UnsupportedToStatement($"Cannot emit literal expression {e} outside of expression context: " + wr.GetType()));
      } else {
        throw new InvalidOperationException("Cannot emit literal expression outside of expression context: " + wr.GetType());
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      throw new UnsupportedInvalidOperationException("<i>EmitStringLiteral</i>");
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, [CanBeNull] NativeType nativeType,
      bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      throw new UnsupportedInvalidOperationException("<i>EmitBitvectorTruncation</i>");
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      AddUnsupportedFeature(e0.tok, Feature.BitvectorRotateFunctions);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override ConcreteSyntaxTree EmitIngredients(ConcreteSyntaxTree wr, string ingredients, int L,
      string tupleTypeArgs, ForallStmt s, AssignStmt s0, Expression rhs) {
      AddUnsupportedFeature(Token.NoToken, Feature.NonSequentializableForallStatements);
      return wr;
    }
    protected override ConcreteSyntaxTree EmitAddTupleToList(string ingredients, string tupleTypeArgs, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(Token.NoToken, Feature.NonSequentializableForallStatements);
      return wr;
    }

    protected override void EmitTupleSelect(string prefix, int i, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public override string PublicIdProtect(string name) {
      return MangleName(name);
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl member = null) {
      AddUnsupported("<i>FullTypeName</i>");
      throw new InvalidOperationException();
    }

    private DAST.Type FullTypeNameAST(UserDefinedType udt, MemberDecl member = null) {
      if (udt.IsArrowType) {
        var arrow = udt.AsArrowType;
        return (DAST.Type)DAST.Type.create_Arrow(
          Sequence<DAST.Type>.FromArray(arrow.Args.Select(m => GenType(m)).ToArray()),
          GenType(arrow.Result)
        );
      } else if (udt.AsArrayType is var array && array != null) {
        if (udt.IsNonNullRefType) {
          return (DAST.Type)DAST.Type.create_Array(GenType(udt.TypeArgs[0]), array.Dims);
        } else {
          return (DAST.Type)DAST.Type.create_Nullable(
            (DAST.Type)DAST.Type.create_Array(GenType(udt.TypeArgs[0]), array.Dims)
          );
        }
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

    private DAST.NewtypeRange NativeTypeToNewtypeRange(NativeType nativeType) {
      return (DAST.NewtypeRange)(nativeType?.Sel switch {
        NativeType.Selection.Byte => NewtypeRange.create_U8(),
        NativeType.Selection.SByte => NewtypeRange.create_I8(),
        NativeType.Selection.UShort => NewtypeRange.create_U16(),
        NativeType.Selection.Short => NewtypeRange.create_I16(),
        NativeType.Selection.UInt => NewtypeRange.create_U32(),
        NativeType.Selection.Int => NewtypeRange.create_I32(),
        NativeType.Selection.ULong => NewtypeRange.create_U64(),
        NativeType.Selection.Long => NewtypeRange.create_I64(),
        NativeType.Selection.UDoubleLong => NewtypeRange.create_U128(),
        NativeType.Selection.DoubleLong => NewtypeRange.create_I128(),
        _ => NewtypeRange.create_NoRange()
      });
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
        var range = NativeTypeToNewtypeRange(newType.NativeType);
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Newtype(
          GenType(EraseNewtypeLayers(topLevel)), range, true);
      } else if (topLevel is TypeSynonymDecl typeSynonym) { // Also SubsetTypeDecl
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Newtype(GenType(EraseNewtypeLayers(topLevel)), NewtypeRange.create_NoRange(), true);
      } else if (topLevel is TraitDecl) {
        AddUnsupportedFeature(Token.NoToken, Feature.Traits);
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Newtype(
          DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString("<b>Unsupported: <i>Traits</i></b>")),
          NewtypeRange.create_NoRange(), true
        );
        // traits need a bit more work

        // resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Trait(path);
      } else if (topLevel is DatatypeDecl) {
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Datatype(path);
      } else if (topLevel is ClassDecl) {
        // TODO(Mikael): have a separate type when we properly support classes
        resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_Datatype(path);
      } else {
        // SubsetTypeDecl are covered by TypeSynonymDecl
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

    private static Type EraseNewtypeLayers(TopLevelDecl topLevel) {
      var topLevelType = UserDefinedType.FromTopLevelDecl(topLevel.tok, topLevel);
      return topLevelType.NormalizeToAncestorType();
    }

    public override ConcreteSyntaxTree Expr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
      if (currentBuilder is ExprContainer container) {
        EmitExpr(expr, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(container, this), wStmts);
        return new ConcreteSyntaxTree();
      } else {
        throw new InvalidOperationException();
      }
    }

    public override void EmitExpr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var actualWr = wr;
      if (currentBuilder is ExprBuffer buf && wr is not BuilderSyntaxTree<ExprContainer>) {
        // the writers are not currently wired properly for DatatypeValue
        actualWr = new BuilderSyntaxTree<ExprContainer>(buf, this);
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
      } else if (expr is QuantifierExpr) {
        AddUnsupported("<i>QuantifierExpr</i>");
      } else {
        base.EmitExpr(expr, inLetExprBody, actualWr, wStmts);
      }
    }

    protected override void EmitThis(ConcreteSyntaxTree wr, bool callToInheritedMember) {
      if (GetExprBuilder(wr, out var builder)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_This());
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string typeDescriptorArguments, string arguments, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder) && currentBuilder is ExprBuffer buf) {
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
          contents.Insert(0,
            ExprContainer.UnsupportedToExpr(
              "Datatype constructor "
              + dtv.Ctor.Name + " expects " + dtv.Ctor.Formals.Count + " arguments, but "
              + contents.Count + " were provided"));
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Tuple(
            Sequence<DAST.Expression>.FromArray(contents.ToArray())
            ));
          return;
        }

        if (dtv.Ctor.EnclosingDatatype is TupleTypeDecl tupleDecl) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Tuple(
            Sequence<DAST.Expression>.FromArray(namedContents.Select(x => x.dtor__1).ToArray())
          ));
        } else {
          var dtPath = PathFromTopLevel(dtv.Ctor.EnclosingDatatype);
          var dtTypeArgs = Sequence<DAST.Type>.FromArray(dtv.InferredTypeArgs.Select(m => GenType(m)).ToArray());
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_DatatypeValue(
            dtPath,
            dtTypeArgs,
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
        case SpecialField.ID.Keys:
          break;
        case SpecialField.ID.Values:
          break;
        default:
          AddUnsupported("<i>Special field: " + id + "</i>");
          break;//throw new InvalidOperationException();
      }
    }

    protected override ILvalue EmitMemberSelect(Action<ConcreteSyntaxTree> obj, Type objType, MemberDecl member,
      List<TypeArgumentInstantiation> typeArgs, Dictionary<TypeParameter, Type> typeMap, Type expectedType,
      string additionalCustomParameter = null, bool internalAccess = false) {
      var objReceiver = new ExprBuffer(null);

      var memberStatus = DatatypeWrapperEraser.GetMemberStatus(Options, member);

      if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.Identity) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();
        return new ExprLvalue(objExpr, null, this);
      } else if (memberStatus == DatatypeWrapperEraser.MemberCompileStatus.AlwaysTrue) {
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(true)), null, this);
      } else if (member is DatatypeDestructor dtor) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();
        if (dtor.EnclosingClass is TupleTypeDecl) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_TupleSelect(
            objExpr,
            int.Parse(dtor.CorrespondingFormals[0].NameForCompilation)
          ), null, this);
        } else {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member is ConstantField,
            member.EnclosingClass is DatatypeDecl
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options))
          ), this);
        }
      } else if (member is SpecialField arraySpecial && arraySpecial.SpecialId == SpecialField.ID.ArrayLength) {
        obj(EmitCoercionIfNecessary(
            objType,
            objType.IsNonNullRefType || !objType.IsRefType ? null : UserDefinedType.CreateNonNullType((UserDefinedType)objType.NormalizeExpand()),
          null, new BuilderSyntaxTree<ExprContainer>(objReceiver, this)
        ));
        var objExpr = objReceiver.Finish();

        return new ExprLvalue((DAST.Expression)DAST.Expression.create_ArrayLen(
          objExpr,
          arraySpecial.IdParam != null ? ((int)arraySpecial.IdParam) : 0
        ), null, this);
      } else if (member is SpecialField { SpecialId: SpecialField.ID.Keys }) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_MapKeys(
          objExpr), null, this);
      } else if (member is SpecialField { SpecialId: SpecialField.ID.Values }) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_MapValues(
          objExpr), null, this);
      } else if (member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();

        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(compiledName),
          member is ConstantField,
          member.EnclosingClass is DatatypeDecl
        ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(compiledName)
        ), this);
      } else if (member is SpecialField sf2 && sf2.SpecialId == SpecialField.ID.UseIdParam && sf2.IdParam is string fieldName && fieldName.StartsWith("is_")) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();

        return new ExprLvalue((DAST.Expression)DAST.Expression.create_TypeTest(
          objExpr,
          PathFromTopLevel(objType.AsTopLevelTypeWithMembers),
          Sequence<Rune>.UnicodeFromString(fieldName.Substring(3))
        ), null, this);
      } else {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();

        if (expectedType.IsArrowType) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_SelectFn(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member.EnclosingClass is DatatypeDecl,
            member.IsStatic,
            expectedType.AsArrowType.Arity
          ), null, this);
        } else if (internalAccess && (member is ConstantField || member.EnclosingClass is TraitDecl)) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(InternalFieldPrefix + member.GetCompileName(Options)),
            false,
            member.EnclosingClass is DatatypeDecl
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(InternalFieldPrefix + member.GetCompileName(Options))
          ), this);
        } else {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member is ConstantField,
            member.EnclosingClass is DatatypeDecl
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options))
          ), this);
        }
      }
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Action<ConcreteSyntaxTree>> indices, Type elmtType, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        var indicesAST = indices.Select(i => {
          var buf = new ExprBuffer(null);
          var localWriter = new BuilderSyntaxTree<ExprContainer>(buf, this);
          i(localWriter);
          return buf.Finish();
        }).ToList();

        return new BuilderSyntaxTree<ExprContainer>(builder.Builder.Index(indicesAST, DAST.CollKind.create_Array()), this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var indicesAST = indices.Select(convert).ToList();

        return new BuilderSyntaxTree<ExprContainer>(builder.Builder.Index(
          indicesAST, DAST.CollKind.create_Array()), this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override (ConcreteSyntaxTree wArray, ConcreteSyntaxTree wRhs) EmitArrayUpdate(List<Action<ConcreteSyntaxTree>> indices, Type elmtType, ConcreteSyntaxTree wr) {
      if (GetStatementBuilder(wr, out var builder)) {
        var indicesAST = indices.Select(i => {
          var buf = new ExprBuffer(null);
          var localWriter = new BuilderSyntaxTree<ExprContainer>(buf, this);
          i(localWriter);
          return buf.Finish();
        }).ToList();

        var assign = builder.Builder.Assign();

        return (new BuilderSyntaxTree<ExprContainer>(((LhsContainer)assign).Array(indicesAST), this), new BuilderSyntaxTree<ExprContainer>(assign, this));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitExprAsNativeInt(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      EmitExpr(expr, inLetExprBody, wr, wStmts);
    }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var sourceBuf = new ExprBuffer(null);
      EmitExpr(source, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(sourceBuf, this), wStmts);

      var indexBuf = new ExprBuffer(null);
      EmitExpr(index, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(indexBuf, this), wStmts);

      DAST._ICollKind collKind;
      if (source.Type.IsArrayType) {
        collKind = DAST.CollKind.create_Array();
      } else if (source.Type.NormalizeToAncestorType().IsMapType) {
        collKind = DAST.CollKind.create_Map();
      } else {
        collKind = DAST.CollKind.create_Seq();
      }

      if (GetExprBuilder(wr, out var builder)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Index(
          sourceBuf.Finish(),
          collKind,
          Sequence<DAST.Expression>.FromElements(indexBuf.Finish())
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected static bool GetStatementBuilder(ConcreteSyntaxTree wStmts,
      out BuilderSyntaxTree<StatementContainer> statementBuilder) {
      if (wStmts is BuilderSyntaxTree<StatementContainer> s) {
        statementBuilder = s;
        return true;
      }
      statementBuilder = null;
      return false;
    }

    protected static bool GetExprBuilder(ConcreteSyntaxTree wr,
      out BuilderSyntaxTree<ExprContainer> builder) {
      if (wr is BuilderSyntaxTree<ExprContainer> exprBuilder) {
        builder = exprBuilder;
        return true;
      }
      builder = null;
      return false;
    }

    protected bool GetExprConverter(ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts,
      out BuilderSyntaxTree<ExprContainer> builder,
      out Func<Expression, DAST.Expression> converter) {
      if (wr is BuilderSyntaxTree<ExprContainer> b) {
        converter = (Expression expr) => ConvertExpression(expr, wStmts);
        builder = b;
        return true;
      }
      converter = null;
      builder = null;
      return false;
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      CollectionType resultCollectionType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        if (resultCollectionType.AsSeqType is { }) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SeqUpdate(
            convert(source), convert(index), convert(value)
          ));
        } else if (resultCollectionType.AsMapType is { }) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_MapUpdate(
            convert(source), convert(index), convert(value)
          ));
        } else {
          AddUnsupported("<i>EmitIndexCollectionUpdate for " + resultCollectionType.ToString() + "</i>");
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      var sourceBuf = new ExprBuffer(null);
      EmitExpr(
        source,
        inLetExprBody,
        EmitCoercionIfNecessary(
          source.Type,
          source.Type.IsNonNullRefType || !source.Type.IsRefType ? null : UserDefinedType.CreateNonNullType((UserDefinedType)source.Type.NormalizeExpand()),
          null, new BuilderSyntaxTree<ExprContainer>(sourceBuf, this)
        ),
        wStmts
      );
      var sourceExpr = sourceBuf.Finish();

      DAST.Expression loExpr = null;
      if (lo != null) {
        var loBuf = new ExprBuffer(null);
        EmitExpr(lo, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(loBuf, this), wStmts);
        loExpr = loBuf.Finish();
      }

      DAST.Expression hiExpr = null;
      if (hi != null) {
        var hiBuf = new ExprBuffer(null);
        EmitExpr(hi, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(hiBuf, this), wStmts);
        hiExpr = hiBuf.Finish();
      }

      if (GetExprBuilder(wr, out var builder)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_IndexRange(
          sourceExpr,
          fromArray,
          loExpr != null ? Option<DAST._IExpression>.create_Some(loExpr) : Option<DAST._IExpression>.create_None(),
          hiExpr != null ? Option<DAST._IExpression>.create_Some(hiExpr) : Option<DAST._IExpression>.create_None()
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var size = expr.N;
        if (size.Type.AsNewtype is { }) {
          size = new ConversionExpr(expr.N.tok, size, new IntType());
        }
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SeqConstruct(
          convert(size),
          convert(expr.Initializer)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, ConcreteSyntaxTree wr,
      ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_ToMultiset(
          convert(expr.E)));
      } else {
        AddUnsupportedFeature(expr.tok, Feature.Multisets);
      }
    }

    protected override void EmitApplyExpr(Type functionType, IToken tok, Expression function,
        List<Expression> arguments, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Apply(
          convert(function),
          Sequence<DAST.Expression>.FromArray(
            arguments.Select(arg => convert(arg)).ToArray())));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitBetaRedex(List<string> boundVars, List<Expression> arguments,
      List<Type> boundTypes, Type resultType, IToken resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var argsAST = arguments.Select((t, i) =>
          (_System.Tuple2<DAST.Formal, DAST.Expression>)
          _System.Tuple2<DAST.Formal, DAST.Expression>.create(
            (DAST.Formal)DAST.Formal.create_Formal(Sequence<Rune>.UnicodeFromString(boundVars[i]),
              GenType(boundTypes[i])), convert(t))).ToList();

        var retType = GenType(resultType);

        return new BuilderSyntaxTree<ExprContainer>(builder.Builder.BetaRedex(
          argsAST, retType
        ), this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
        List<Type> typeArgs, Type bvType, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        if (DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, ctor.EnclosingDatatype, out var coreDtor)) {
          Contract.Assert(coreDtor.CorrespondingFormals.Count == 1);
          Contract.Assert(dtor == coreDtor.CorrespondingFormals[0]); // any other destructor is a ghost
          source(wr);
        } else {
          var buf = new ExprBuffer(null);
          source(new BuilderSyntaxTree<ExprContainer>(buf, this));
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

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IToken tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      if (GetExprBuilder(wr, out var builder)) {
        var formals = new List<DAST.Formal>();
        for (int i = 0; i < inTypes.Count; ++i) {
          formals.Add((DAST.Formal)DAST.Formal.create_Formal(
            Sequence<Rune>.UnicodeFromString(inNames[i]),
            GenType(inTypes[i])
          ));
        }

        var retType = GenType(resultType);

        return new BuilderSyntaxTree<StatementContainer>(builder.Builder.Lambda(formals, retType), this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitLambdaApply(ConcreteSyntaxTree wr, out ConcreteSyntaxTree wLambda, out ConcreteSyntaxTree wArg) {
      if (GetExprBuilder(wr, out var exprBuilder)) {
        var lambda = exprBuilder.Builder.Apply();
        wLambda = new BuilderSyntaxTree<ExprContainer>(lambda, this);
        wArg = new BuilderSyntaxTree<ExprContainer>(lambda, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitAnd(Action<ConcreteSyntaxTree> lhs, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        var binOp = builder.Builder.BinOp((DAST.BinOp)DAST.BinOp.create_Passthrough(
          Sequence<Rune>.UnicodeFromString("&&")
        ));
        lhs(new BuilderSyntaxTree<ExprContainer>(binOp, this));

        return new BuilderSyntaxTree<ExprContainer>(binOp, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitBoolBoundedPool(bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprBuilder(wr, out var exprBuilder)) {
        exprBuilder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_BoolBoundedPool());
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitCharBoundedPool(bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported("<i>EmitCharBoundedPool</i>");
    }

    protected override void EmitWiggleWaggleBoundedPool(bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported("<i>EmitWiggleWaggleBoundedPool</i>");
    }

    protected override void EmitSetBoundedPool(Expression of, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var exprBuilder, out var convert)) {
        exprBuilder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SetBoundedPool(
          convert(of)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitMultiSetBoundedPool(Expression of, bool includeDuplicates, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported("<i>EmitMultiSetBoundedPool</i>");
    }

    protected override void EmitSubSetBoundedPool(Expression of, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported("<i>EmitSubSetBoundedPool</i>");
    }

    protected override void EmitMapBoundedPool(Expression map, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported("<i>EmitMapBoundedPool</i>");
    }

    protected override void EmitSeqBoundedPool(Expression of, bool includeDuplicates, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var exprBuilder, out var convert)) {
        exprBuilder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SeqBoundedPool(
          convert(of),
          includeDuplicates
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitDatatypeBoundedPool(IVariable bv, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported("<i>EmitDatatypeBoundedPool</i>");
    }

    protected override void CreateIIFE(string bvName, Type bvType, IToken bvTok, Type bodyType, IToken bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      if (GetExprBuilder(wr, out var builder)) {
        var iife = builder.Builder.IIFE(bvName, GenType(bvType));
        wrRhs = new BuilderSyntaxTree<ExprContainer>(iife.RhsBuilder(), this);
        wrBody = new BuilderSyntaxTree<ExprContainer>(iife, this);
      } else {
        throw new InvalidOperationException("Invalid context for IIFE: " + wr.GetType());
      }
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IToken resultTok, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      EmitLambdaApply(wr, out var wLambda, out var wArg);
      return CreateLambda(new(), null, new(), resultType, wLambda, wStmts);
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IToken resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      EmitLambdaApply(wr, out var wLambda, out var wArg);
      var ret = CreateLambda(new() { Type.Int }, null, new() { bvName }, resultType, wLambda, wStmts);
      EmitLiteralExpr(wArg, new LiteralExpr(null, source) {
        Type = Type.Int
      });
      return ret;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var container, out var convert)) {
        switch (op) {
          case ResolvedUnaryOp.BoolNot: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_Not(),
                convert(expr),
                new UnaryOpFormat_NoFormat()
              ));
              break;
            }
          case ResolvedUnaryOp.BitwiseNot: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_BitwiseNot(),
                convert(expr),
                new UnaryOpFormat_NoFormat()
              ));
              break;
            }
          case ResolvedUnaryOp.Cardinality: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_Cardinality(),
                convert(expr),
                new UnaryOpFormat_NoFormat()
              ));
              break;
            }
        }
      } else {
        AddUnsupported("<i>UnaryExpr " + op + "</i>");
      }
    }

    // A few helpers to reduce the size of expressions
    private static DAST.Expression Not(_IExpression expr, bool mergeInner = true) {
      return (DAST.Expression)DAST.Expression.create_UnOp(
        new UnaryOp_Not(),
        (DAST.Expression)expr,
        mergeInner ? new UnaryOpFormat_CombineFormat() : new UnaryOpFormat_NoFormat());
    }

    private static DAST.Expression BinaryOp(_IBinOp op, _IExpression left, _IExpression right, _IBinaryOpFormat format = null) {
      format ??= new BinaryOpFormat_NoFormat();

      return (DAST.Expression)DAST.Expression.create_BinOp(
        op, left, right, format
      );
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
          BinaryExpr.ResolvedOpcode.Iff => "==",
          BinaryExpr.ResolvedOpcode.And => "&&",
          BinaryExpr.ResolvedOpcode.Or => "||",
          BinaryExpr.ResolvedOpcode.BitwiseAnd => "&",
          BinaryExpr.ResolvedOpcode.BitwiseOr => "|",
          BinaryExpr.ResolvedOpcode.BitwiseXor => "^",
          BinaryExpr.ResolvedOpcode.Lt => "<",
          BinaryExpr.ResolvedOpcode.LtChar => "<",
          BinaryExpr.ResolvedOpcode.Le => "<=",
          BinaryExpr.ResolvedOpcode.LeChar => "<=",
          BinaryExpr.ResolvedOpcode.Ge => ">=",
          BinaryExpr.ResolvedOpcode.GeChar => ">=",
          BinaryExpr.ResolvedOpcode.Gt => ">",
          BinaryExpr.ResolvedOpcode.GtChar => ">",
          BinaryExpr.ResolvedOpcode.LeftShift => "<<",
          BinaryExpr.ResolvedOpcode.RightShift => ">>",
          BinaryExpr.ResolvedOpcode.Add => "+",
          BinaryExpr.ResolvedOpcode.Sub => "-",
          BinaryExpr.ResolvedOpcode.Mul => "*",
          BinaryExpr.ResolvedOpcode.SetEq => "==",
          BinaryExpr.ResolvedOpcode.SetNeq => "!=",
          BinaryExpr.ResolvedOpcode.MultiSetEq => "==",
          BinaryExpr.ResolvedOpcode.MultiSetNeq => "!=",
          BinaryExpr.ResolvedOpcode.SeqEq => "==",
          BinaryExpr.ResolvedOpcode.SeqNeq => "!=",
          BinaryExpr.ResolvedOpcode.MapEq => "==",
          BinaryExpr.ResolvedOpcode.MapNeq => "!=",
          BinaryExpr.ResolvedOpcode.ProperSubset => "<",
          BinaryExpr.ResolvedOpcode.ProperMultiSubset => "<",
          BinaryExpr.ResolvedOpcode.Subset => "<=",
          BinaryExpr.ResolvedOpcode.MultiSubset => "<=",
          BinaryExpr.ResolvedOpcode.Disjoint => "!!",
          BinaryExpr.ResolvedOpcode.MultiSetDisjoint => "!!",
          BinaryExpr.ResolvedOpcode.InMultiSet => "in",
          BinaryExpr.ResolvedOpcode.InMap => "in",
          BinaryExpr.ResolvedOpcode.NotInMap => "notin",
          BinaryExpr.ResolvedOpcode.Union => "+",
          BinaryExpr.ResolvedOpcode.MultiSetUnion => "+",
          BinaryExpr.ResolvedOpcode.MapMerge => "+",
          BinaryExpr.ResolvedOpcode.Intersection => "*",
          BinaryExpr.ResolvedOpcode.MultiSetIntersection => "*",
          BinaryExpr.ResolvedOpcode.MultiSetDifference => "-",
          BinaryExpr.ResolvedOpcode.MapSubtraction => "-",
          BinaryExpr.ResolvedOpcode.ProperPrefix => "<=",
          BinaryExpr.ResolvedOpcode.Prefix => "<",
          _ => null
        };

        object B(_IBinOp binOp) {
          return builder.Builder.BinOp((DAST.BinOp)binOp);
        }

        var opStringClosure = opString;
        object C(System.Func<DAST.Expression, DAST.Expression, DAST.Expression> callback) {
          return builder.Builder.BinOp(opStringClosure, callback);
        }

        var newBuilder = op switch {
          BinaryExpr.ResolvedOpcode.EqCommon => B((BinOp)BinOp.create_Eq(
            e0.Type.IsRefType,
            !e0.Type.IsNonNullRefType
          )),
          BinaryExpr.ResolvedOpcode.SetEq => B((BinOp)BinOp.create_Eq(false, false)),
          BinaryExpr.ResolvedOpcode.MapEq => B((BinOp)BinOp.create_Eq(false, false)),
          BinaryExpr.ResolvedOpcode.SeqEq => B((BinOp)BinOp.create_Eq(false, false)),
          BinaryExpr.ResolvedOpcode.MultiSetEq => B((BinOp)BinOp.create_Eq(false, false)),
          BinaryExpr.ResolvedOpcode.NeqCommon => C((left, right) =>
            Not(BinaryOp(
              BinOp.create_Eq(
                e0.Type.IsRefType,
                !e0.Type.IsNonNullRefType
              ), left, right))),
          BinaryExpr.ResolvedOpcode.SetNeq => C((left, right) =>
            Not(BinaryOp(BinOp.create_Eq(false, false), left, right))),
          BinaryExpr.ResolvedOpcode.SeqNeq => C((left, right) =>
            Not(BinaryOp(BinOp.create_Eq(false, false), left, right))),
          BinaryExpr.ResolvedOpcode.MultiSetNeq => C((left, right) =>
            Not(BinaryOp(BinOp.create_Eq(false, false), left, right))),

          BinaryExpr.ResolvedOpcode.Div =>
            B(NeedsEuclideanDivision(resultType) ? BinOp.create_EuclidianDiv() : BinOp.create_Div()),
          BinaryExpr.ResolvedOpcode.Mod =>
            B(NeedsEuclideanDivision(resultType) ? BinOp.create_EuclidianMod() : BinOp.create_Mod()),
          BinaryExpr.ResolvedOpcode.Imp =>
            C((left, right) =>
              BinaryOp(
                DAST.BinOp.create_Or(),
                Not(left, false), right, new BinaryOpFormat_ImpliesFormat()
              )),
          BinaryExpr.ResolvedOpcode.Iff =>
            C((left, right) =>
              BinaryOp(
                BinOp.create_Eq(false, false),
                left, right, new BinaryOpFormat_EquivalenceFormat()
              )),
          BinaryExpr.ResolvedOpcode.InSet => B(DAST.BinOp.create_In()), // TODO: Differentiate?
          BinaryExpr.ResolvedOpcode.InSeq => B(DAST.BinOp.create_In()),
          BinaryExpr.ResolvedOpcode.InMap => B(DAST.BinOp.create_In()),
          BinaryExpr.ResolvedOpcode.InMultiSet => B(DAST.BinOp.create_In()),


          BinaryExpr.ResolvedOpcode.Union =>
            B(DAST.BinOp.create_SetMerge()),
          BinaryExpr.ResolvedOpcode.SetDifference =>
            B(DAST.BinOp.create_SetSubtraction()),
          BinaryExpr.ResolvedOpcode.Intersection =>
            B(DAST.BinOp.create_SetIntersection()),
          BinaryExpr.ResolvedOpcode.Disjoint =>
            B(DAST.BinOp.create_SetDisjoint()),
          BinaryExpr.ResolvedOpcode.ProperSubset =>
            B(DAST.BinOp.create_ProperSubset()),
          BinaryExpr.ResolvedOpcode.Subset =>
            B(DAST.BinOp.create_Subset()),
          BinaryExpr.ResolvedOpcode.Superset =>
            C((left, right) =>
              BinaryOp(new BinOp_Subset(), right, left,
                new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.ProperSuperset =>
            C((left, right) =>
              BinaryOp(new BinOp_ProperSubset(), right, left,
                new BinaryOpFormat_ReverseFormat())),

          BinaryExpr.ResolvedOpcode.MultiSetUnion =>
            B(DAST.BinOp.create_MultisetMerge()),
          BinaryExpr.ResolvedOpcode.MultiSetDifference =>
            B(DAST.BinOp.create_MultisetSubtraction()),
          BinaryExpr.ResolvedOpcode.MultiSetIntersection =>
            B(DAST.BinOp.create_MultisetIntersection()),
          BinaryExpr.ResolvedOpcode.MultiSetDisjoint =>
            B(DAST.BinOp.create_MultisetDisjoint()),
          BinaryExpr.ResolvedOpcode.ProperMultiSubset =>
            B(DAST.BinOp.create_ProperSubmultiset()),
          BinaryExpr.ResolvedOpcode.MultiSubset =>
            B(DAST.BinOp.create_Submultiset()),
          BinaryExpr.ResolvedOpcode.MultiSuperset =>
            C((left, right) =>
              BinaryOp(new BinOp_Submultiset(), right, left,
                new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.ProperMultiSuperset =>
            C((left, right) =>
              BinaryOp(new BinOp_ProperSubmultiset(), right, left,
                new BinaryOpFormat_ReverseFormat())),

          BinaryExpr.ResolvedOpcode.MapMerge =>
            B(DAST.BinOp.create_MapMerge()),
          BinaryExpr.ResolvedOpcode.MapSubtraction =>
            B(DAST.BinOp.create_MapSubtraction()),

          BinaryExpr.ResolvedOpcode.ProperPrefix =>
            B(DAST.BinOp.create_SeqProperPrefix()),
          BinaryExpr.ResolvedOpcode.Prefix =>
            B(DAST.BinOp.create_SeqPrefix()),

          BinaryExpr.ResolvedOpcode.NotInMap =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_In(), left, right))),
          BinaryExpr.ResolvedOpcode.NotInSet =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_In(), left, right))),
          BinaryExpr.ResolvedOpcode.NotInSeq =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_In(), left, right))),
          BinaryExpr.ResolvedOpcode.NotInMultiSet =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_In(), left, right))),
          BinaryExpr.ResolvedOpcode.Concat => B(BinOp.create_Concat()),
          BinaryExpr.ResolvedOpcode.And => B(BinOp.create_And()),
          BinaryExpr.ResolvedOpcode.Or => B(BinOp.create_Or()),
          BinaryExpr.ResolvedOpcode.Add => B(BinOp.create_Plus()),
          BinaryExpr.ResolvedOpcode.Sub => B(BinOp.create_Minus()),
          BinaryExpr.ResolvedOpcode.Mul => B(BinOp.create_Times()),
          BinaryExpr.ResolvedOpcode.BitwiseAnd => B(BinOp.create_BitwiseAnd()),
          BinaryExpr.ResolvedOpcode.BitwiseOr => B(BinOp.create_BitwiseOr()),
          BinaryExpr.ResolvedOpcode.BitwiseXor => B(BinOp.create_BitwiseXor()),
          BinaryExpr.ResolvedOpcode.LeftShift => B(BinOp.create_BitwiseShiftLeft()),
          BinaryExpr.ResolvedOpcode.RightShift => B(BinOp.create_BitwiseShiftRight()),
          BinaryExpr.ResolvedOpcode.Lt =>
            B(BinOp.create_Lt()),
          BinaryExpr.ResolvedOpcode.LtChar =>
            B(BinOp.create_LtChar()),
          BinaryExpr.ResolvedOpcode.Le =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_Lt(), right, left,
                new BinaryOpFormat_ReverseFormat()))),
          BinaryExpr.ResolvedOpcode.LeChar =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_LtChar(), right, left,
                new BinaryOpFormat_ReverseFormat()))),
          BinaryExpr.ResolvedOpcode.Gt =>
            C((left, right) =>
              BinaryOp(new BinOp_Lt(), right, left, new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.GtChar =>
            C((left, right) =>
              BinaryOp(new BinOp_LtChar(), right, left, new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.Ge =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_Lt(), left, right))),
          BinaryExpr.ResolvedOpcode.GeChar =>
            C((left, right) =>
              Not(BinaryOp(new BinOp_LtChar(), left, right))),

          _ => B(DAST.BinOp.create_Passthrough(Sequence<Rune>.UnicodeFromString($"<b>Unsupported: <i>Operator {op}</i></b>"))),
        };

        opString = "";

        currentBuilder = newBuilder;
        // cleaned up by EmitExpr
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Ite(
          convert(guard),
          convert(thn),
          convert(els)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>EmitIsZero</i>");
    }

    protected override void EmitConversionExpr(Expression fromExpr, Type fromType, Type toType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprBuilder(wr, out var builder)) {
        if (toType.Equals(fromType)) {
          EmitExpr(fromExpr, inLetExprBody, builder, wStmts);
        } else {
          EmitExpr(fromExpr, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(builder.Builder.Convert(
            GenType(fromType),
            GenType(toType)
          ), this), wStmts);
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
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
      AddUnsupportedFeature(tok, Feature.TypeTests);
    }

    protected override void EmitIsIntegerTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(source.Tok, Feature.TypeTests);
    }

    protected override void EmitIsUnicodeScalarValueTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(source.Tok, Feature.TypeTests);
    }

    protected override void EmitIsInIntegerRange(Expression source, BigInteger lo, BigInteger hi, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new UnsupportedFeatureException(source.Tok, Feature.TypeTests);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IToken tok, List<Expression> elements,
      bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var elementsAST = elements.Select(convert).ToArray();

        if (ct is SetType set) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SetValue(
            Sequence<DAST.Expression>.FromArray(elementsAST)
          ));
        } else if (ct is MultiSetType multiSet) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_MultisetValue(
            Sequence<DAST.Expression>.FromArray(elementsAST)
          ));
        } else if (ct is SeqType seq) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_SeqValue(
            Sequence<DAST.Expression>.FromArray(elementsAST),
            GenType(ct.TypeArgs[0])
          ));
        } else {
          throw new InvalidOperationException();
        }
      } else {
        throw new InvalidOperationException();//TODO
      }
    }

    protected override void EmitMapDisplay(MapType mt, IToken tok, List<ExpressionPair> elements, bool inLetExprBody,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var converter)) {
        var elementsAST = new List<_System.Tuple2<DAST.Expression, DAST.Expression>>();
        foreach (var e in elements) {
          elementsAST.Add((_System.Tuple2<DAST.Expression, DAST.Expression>)_System.Tuple2<DAST.Expression, DAST.Expression>.create(
            converter(e.A),
            converter(e.B)
          ));
        }

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_MapValue(
          Sequence<_System.Tuple2<DAST.Expression, DAST.Expression>>.FromArray(elementsAST.ToArray())
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      if (GetStatementBuilder(wr, out var builder)) {
        var eType = e.Type.AsSetType;
        if (eType == null) {// dafny0/GeneralNewtypeCollections
          throw new UnsupportedFeatureException(e.tok, Feature.NonNativeNewtypes);
        }
        var elemType = GenType(eType.Arg);
        var setBuilderType = DAST.Type.create_SetBuilder(elemType);
        builder.Builder.AddStatement(
          (DAST.Statement)DAST.Statement.create_DeclareVar(
            Sequence<Rune>.UnicodeFromString(collectionName),
            setBuilderType,
            Option<_IExpression>.create_Some(
              DAST.Expression.create_SetBuilder(elemType)
            )
          ));
      } else {
        AddUnsupported("<i>EmitSetBuilder_New</i>");
      }
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      if (GetStatementBuilder(wr, out var builder)) {
        var eType = e.Type.AsMapType;
        var keyType = GenType(eType.Range);
        var valueType = GenType(eType.Domain);
        var mapType = DAST.Type.create_MapBuilder(keyType, valueType);
        builder.Builder.AddStatement(
          (DAST.Statement)DAST.Statement.create_DeclareVar(
            Sequence<Rune>.UnicodeFromString(collectionName),
            mapType,
            Option<_IExpression>.create_Some(
              DAST.Expression.create_MapBuilder(keyType, valueType)
              )
            ));
      } else {
        AddUnsupported("<i>EmitMapBuilder_New (non-statement)</i>");
      }
      //throw new InvalidOperationException();
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      if (GetStatementBuilder(wr, out var builder)) {
        var stmtBuilder = new CallStmtBuilder();
        stmtBuilder.SetName((DAST.CallName)DAST.CallName.create_SetBuilderAdd());
        stmtBuilder.SetTypeArgs(new List<DAST.Type> { });
        stmtBuilder.SetOuts(new List<ISequence<Rune>> { }); ;
        stmtBuilder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(collName)));
        stmtBuilder.AddExpr(ConvertExpression(elmt, builder));
        builder.Builder.AddBuildable(stmtBuilder);
      } else {
        AddUnsupported("<i>EmitSetBuilder_Add</i>");
      }
      //throw new InvalidOperationException();
    }

    // Normally wStmt is a BuilderSyntaxTree<StatementContainer> but it might not while the compiler is being developed
    private DAST.Expression ConvertExpression(Expression term, ConcreteSyntaxTree wStmt) {
      var buffer0 = new ExprBuffer(null);
      EmitExpr(term, false, new BuilderSyntaxTree<ExprContainer>(buffer0, this), wStmt);
      return buffer0.Finish();
    }

    private BuilderSyntaxTree<ExprContainer> CreateExprBuilder() {
      var exprBuffer = new ExprBuffer(null);
      var exprBuilder = new BuilderSyntaxTree<ExprContainer>(exprBuffer, this);
      return exprBuilder;
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IToken tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (GetStatementBuilder(wr, out var builder)) {
        var stmtBuilder = new CallStmtBuilder();
        stmtBuilder.SetName((DAST.CallName)DAST.CallName.create_MapBuilderAdd());
        stmtBuilder.SetTypeArgs(new List<DAST.Type> { });
        stmtBuilder.SetOuts(new List<ISequence<Rune>> { }); ;
        stmtBuilder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(collName)));
        var keyBuilder = CreateExprBuilder();
        stmtBuilder.AddBuildable((ExprBuffer)keyBuilder.Builder);
        stmtBuilder.AddExpr(ConvertExpression(term, builder));
        builder.Builder.AddBuildable(stmtBuilder);
        return keyBuilder;
      } else {
        AddUnsupported("<i>EMitMapBuilder_Add</i>");
        var buffer1 = new ExprBuffer(null);
        return new BuilderSyntaxTree<ExprContainer>(buffer1, this);
      }
    }

    protected override Action<ConcreteSyntaxTree> GetSubtypeCondition(string tmpVarName, Type boundVarType, IToken tok, ConcreteSyntaxTree wPreconditions) {
      Action<ConcreteSyntaxTree> typeTest;

      if (boundVarType.IsRefType) {
        DAST._IExpression baseExpr;
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          baseExpr = DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(true));
        } else {
          // typeTest = $"{tmpVarName} instanceof {TypeName(boundVarType, wPreconditions, tok)}";
          AddUnsupported("<i>TypeName</i>");
          throw new InvalidOperationException();
        }

        if (boundVarType.IsNonNullRefType) {
          typeTest = wr => {
            if (GetExprBuilder(wr, out var builder)) {
              builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_BinOp(
                DAST.BinOp.create_Passthrough(Sequence<Rune>.UnicodeFromString("&&")),
                DAST.Expression.create_BinOp(
                  DAST.BinOp.create_Passthrough(Sequence<Rune>.UnicodeFromString("!=")),
                  DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(tmpVarName)),
                  DAST.Expression.create_Literal(DAST.Literal.create_Null(GenType(boundVarType))),
                  new BinaryOpFormat_NoFormat()),
                baseExpr,
                new BinaryOpFormat_NoFormat()
              ));
            } else {
              throw new InvalidOperationException();
            }
          };
        } else {
          typeTest = wr => {
            if (GetExprBuilder(wr, out var builder)) {
              builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_BinOp(
                DAST.BinOp.create_Passthrough(Sequence<Rune>.UnicodeFromString("||")),
                DAST.Expression.create_BinOp(
                  DAST.BinOp.create_Passthrough(Sequence<Rune>.UnicodeFromString("==")),
                  DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(tmpVarName)),
                  DAST.Expression.create_Literal(DAST.Literal.create_Null(GenType(boundVarType))),
                  new BinaryOpFormat_NoFormat()
                ),
                baseExpr,
                new BinaryOpFormat_NoFormat()
              ));
            } else {
              throw new InvalidOperationException();
            }
          };
        }
      } else {
        typeTest = wr => EmitExpr(Expression.CreateBoolLiteral(tok, true), false, wr, null);
      }

      return typeTest;
    }

    protected override void GetCollectionBuilder_Build(CollectionType ct, IToken tok, string collName,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmt) {
      if (GetExprBuilder(wr, out var builder)) {
        var callExpr = new CallExprBuilder();
        if (ct.IsMapType) {
          callExpr.SetName((DAST.CallName)DAST.CallName.create_MapBuilderBuild());
        } else {
          callExpr.SetName((DAST.CallName)DAST.CallName.create_SetBuilderBuild());
        }

        callExpr.SetTypeArgs(new List<DAST.Type> { });
        callExpr.SetOuts(new List<ISequence<Rune>> { }); ;
        callExpr.AddExpr((DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(collName)));
        builder.Builder.AddBuildable(callExpr);
      } else {
        AddUnsupported("<i>GetCollectionBuilder_Build</i>");
      }
    }

    protected override (Type, Action<ConcreteSyntaxTree>) EmitIntegerRange(Type type, Action<ConcreteSyntaxTree> wLo, Action<ConcreteSyntaxTree> wHi) {
      Type result;
      if (AsNativeType(type) != null) {
        result = type;
      } else {
        result = new IntType();
      }

      return (result, (wr) => {
        var loBuf = new ExprBuffer(null);
        wLo(new BuilderSyntaxTree<ExprContainer>(loBuf, this));
        var hiBuf = new ExprBuffer(null);
        wHi(new BuilderSyntaxTree<ExprContainer>(hiBuf, this));

        if (GetExprBuilder(wr, out var builder)) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_IntRange(
            loBuf.Finish(),
            hiBuf.Finish()
          ));
        } else {
          throw new InvalidOperationException();
        }
      }
      );
    }

    protected override void EmitNull(Type _, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>EmitNull</i>");
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupportedFeature(e.Tok, Feature.ExactBoundedPool);
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      AddUnsupported("<i>EmitHaltRecoveryStmt</i>");
    }

  }
}
