using System;
using System.Collections.Generic;
using Dafny;
using JetBrains.Annotations;
using DAST;
using System.Numerics;
using Microsoft.BaseTypes;
using System.Linq;
using System.Diagnostics.Contracts;
using DAST.Format;
using Microsoft.Boogie;
using Std.Wrappers;

namespace Microsoft.Dafny.Compilers {

  class DafnyCodeGenerator : SinglePassCodeGenerator {

    ProgramBuilder items;
    public object currentBuilder;
    public bool emitUncompilableCode;
    protected override string InternalFieldPrefix => internalFieldPrefix;
    public string internalFieldPrefix;
    public bool preventShadowing;

    // In a language like Rust, trait methods with bodies don't need to be called by
    // the class or datatype extending it with overriding functions or methods that call into the trait.
    // However, if a method is declared in a trait A, and another trait B implements it,
    // then any class or datatype extending that last trait B must also explicitly implement the first trait A
    // by calling the trait implementation in B
    protected override bool InstanceMethodsCanOnlyCallOverridenTraitMethods => true;

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

    public DafnyCodeGenerator(DafnyOptions options, ErrorReporter reporter, string internalFieldPrefix, bool preventShadowing, bool canEmitUncompilableCode) : base(options, reporter) {
      if (Options?.CoverageLegendFile != null) {
        Imports.Add("DafnyProfiling");
      }

      this.internalFieldPrefix = internalFieldPrefix;
      emitUncompilableCode = options.Get(CommonOptionBag.EmitUncompilableCode) && canEmitUncompilableCode;
      this.preventShadowing = preventShadowing;
    }

    protected override string GetCompileNameNotProtected(IVariable v) {
      return preventShadowing ? v.GetOrCreateCompileName(currentIdGenerator) : v.CompileNameShadowable;
    }

    public string TokenToString(IOrigin tok) {
      var absolutePath = tok.Uri;
      var localPath = absolutePath.LocalPath;
      var relativePath = System.IO.Path.GetRelativePath(".", localPath).Replace("\\", "/"); // Normalize paths
      return $"{relativePath}({tok.line},{tok.col})";
    }

    public void AddUnsupported(IOrigin tok, string why) {
      if (emitUncompilableCode && currentBuilder is Container container) {
        container.AddUnsupported($"{TokenToString(tok)}: {why}");
      } else {
        throw new UnsupportedInvalidOperationException(tok, why);
      }
    }

    public void AddUnsupportedFeature(IOrigin tok, Feature feature) {
      if (emitUncompilableCode && currentBuilder is Container container) {
        container.AddUnsupported($"<i>{TokenToString(tok)}DCOMP: {feature}</i>");
      } else {
        throw new RecoverableUnsupportedFeatureException(tok, feature);
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
      Feature.ArraysWithMoreThan16Dims,
      Feature.ForLoops,
      Feature.Traits,
      Feature.RuntimeCoverageReport,
      Feature.NonNativeNewtypes
    };

    private readonly List<string> Imports = [DafnyDefaultModule];

    private const string DafnyRuntimeModule = "_dafny";
    private const string DafnyDefaultModule = "module_";

    protected override string AssignmentSymbol { get => null; }

    protected override void EmitHeader(Program program, ConcreteSyntaxTree wr) {
    }

    public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree wr) {
      AddUnsupported(Token.NoToken, "<i>Call to main</i>");
    }

    protected override ConcreteSyntaxTree CreateStaticMain(IClassWriter cw, string argsParameterName) {
      AddUnsupported(Token.NoToken, "<i>create static main</i>");
      return WrBuffer(out _);
    }

    private bool NeedsExternalImport(MemberDecl memberDecl) {
      return !memberDecl.IsGhost && memberDecl.HasExternAttribute &&
             memberDecl is Function { Body: null } or MethodOrConstructor { Body: null };
    }

    protected override ConcreteSyntaxTree CreateModule(ModuleDefinition module, string moduleName, bool isDefault,
      ModuleDefinition externModule,
      string libraryName, Attributes moduleAttributes, ConcreteSyntaxTree wr) {
      if (currentBuilder is ModuleContainer moduleBuilder) {
        var attributes = (Sequence<DAST.Attribute>)ParseAttributes(moduleAttributes);
        if (externModule != null) {
          attributes = (Sequence<DAST.Attribute>)ParseAttributes(externModule.Attributes);
        }

        var requiresExternImport = enclosingModule.TopLevelDecls.Any((TopLevelDecl decl) =>
          (decl is DefaultClassDecl defaultClassDecl &&
           GetIsExternAndIncluded(defaultClassDecl) is (_, included: false)
           && defaultClassDecl.Members.Exists(NeedsExternalImport)
           ) ||
          (decl is ClassLikeDecl classLikeDecl &&
           GetIsExternAndIncluded(classLikeDecl) is (ClassIsExtern: true, _)) ||
          (decl is AbstractTypeDecl)
        );
        var docString = GetDocString(module.EnclosingLiteralModuleDecl is { } node ? node : module);
        currentBuilder = moduleBuilder.Module(moduleName, docString, attributes, requiresExternImport);
      } else {
        throw new InvalidOperationException();
      }

      return wr;
    }

    private string GetDocString(INode node) {
      return ((node is IHasDocstring iHasDocstring ? iHasDocstring?.GetDocstring(Options) : "") +
              "\n" + (node.StartToken.line != 0 && node is not DatatypeCtor ? TokenToString(node.StartToken) : "")).Trim();
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

    protected override ConcreteSyntaxTree EmitCoercionIfNecessary(Type from, Type to, IOrigin tok, ConcreteSyntaxTree wr, Type toOrig = null) {
      if (currentBuilder is ExprBuffer buf && wr is not BuilderSyntaxTree<ExprContainer>) {
        // the writers are not currently wired properly for DatatypeValue
        wr = new BuilderSyntaxTree<ExprContainer>(buf, this);
      }

      if (from == null || to == null || from.Equals(to, false)) {
        return wr;
      }

      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        return new BuilderSyntaxTree<ExprContainer>(builder.Builder.Convert(GenType(from), GenType(to)), this);
      } else {
        throw new UnsupportedInvalidOperationException(tok, "coercion not in the presence of an ExprContainer");
      }
    }

    protected override IClassWriter CreateClass(string moduleName, bool isExtern, string fullPrintName,
      List<TypeParameter> typeParameters, TopLevelDecl cls, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {
      if (currentBuilder is ClassContainer builder) {
        List<DAST.TypeArgDecl> typeParams = typeParameters.Select(tp => GenTypeArgDecl(tp)).ToList();

        var classWriter = new ClassWriter(this, typeParams.Count > 0, builder.Class(
          IdName(cls), moduleName, typeParams, superClasses.Select(t => GenType(t)).ToList(),
          ParseAttributes(cls.Attributes), GetDocString(cls))
          );

        return classWriter;
      } else {
        throw new InvalidOperationException();
      }
    }

    private TypeParameterInfo GenTypeParameterInfo(TypeParameter tp) {
      return (TypeParameterInfo)TypeParameterInfo.create_TypeParameterInfo(GenTypeVariance(tp),
        tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype);
    }

    private ISequence<TypeParameterInfo> GenTypeParameterInfos(List<TypeParameter> typeParams) {
      return Sequence<TypeParameterInfo>.FromArray(typeParams.Select(GenTypeParameterInfo).ToArray());
    }

    private Variance GenTypeVariance(TypeParameter tp) {
      if (tp.Variance is TypeParameter.TPVariance.Co) {
        return (Variance)Variance.create_Covariant();
      }

      if (tp.Variance is TypeParameter.TPVariance.Contra) {
        AddUnsupported(tp.Origin, "Contravariance");
      }
      return (Variance)Variance.create_Nonvariant();
    }

    private ISequence<_ITypeArgBound> GenTypeBounds(TypeParameter tp) {
      var characteristics = new List<_ITypeArgBound>();
      if (tp.Characteristics.AutoInit is Type.AutoInitInfo.CompilableValue) {
        characteristics.Add(DAST.TypeArgBound.create_SupportsDefault());
      }

      if (tp.Characteristics.EqualitySupport is TypeParameter.EqualitySupportValue.Required or TypeParameter.EqualitySupportValue.InferredRequired) {
        characteristics.Add(DAST.TypeArgBound.create_SupportsEquality());
      }

      foreach (var typebound in tp.TypeBounds) {
        var traitType = GenType(typebound);
        characteristics.Add(DAST.TypeArgBound.create_TraitBound(traitType));
      }

      var bounds = Sequence<_ITypeArgBound>.FromArray(characteristics.ToArray());
      return bounds;
    }

    protected TypeArgDecl GenTypeArgDecl(TypeParameter tp, string name = null) {
      var bounds = GenTypeBounds(tp);

      var variance = GenTypeVariance(tp);

      name ??= tp.GetCompileName(Options);

      var info = TypeParameterInfo.create_TypeParameterInfo(variance,
        tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype);

      return (DAST.TypeArgDecl)DAST.TypeArgDecl.create_TypeArgDecl(
        Sequence<Rune>.UnicodeFromString(name), bounds, info);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<TypeParameter> typeParameters,
      TraitDecl trait, List<Type> superClasses, IOrigin tok, ConcreteSyntaxTree wr) {

      if (currentBuilder is TraitContainer builder) {
        var typeParams = trait.TypeArgs.Select(tp => GenTypeArgDecl(tp)).ToList();
        List<DAST.Type> parents = [];
        if (trait.IsReferenceTypeDecl) {
          parents.Add((DAST.Type)DAST.Type.create_Object());
        }
        foreach (var pt in trait.Traits) {
          var genType = GenType(pt);

          parents.Add(genType);
        }

        var traitType = trait.IsReferenceTypeDecl
          ? DAST.TraitType.create_ObjectTrait()
          : TraitType.create_GeneralTrait();
        var downcastableTraits = trait.DowncastableSubTraitsIfMonomorphized();
        var downcastableTraitTypes = downcastableTraits.Select(GenType).ToList();
        return new ClassWriter(this, typeParameters.Any(), builder.Trait(name, typeParams, parents, ParseAttributes(trait.Attributes), GetDocString(trait), traitType, downcastableTraitTypes));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree CreateIterator(IteratorDecl iter, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(iter.Origin, Feature.Iterators);
      return wr;
    }

    private static bool isTpSupported(TypeParameter tp, [CanBeNull] out string why) {
      if (tp.Variance == TypeParameter.TPVariance.Contra) {
        why = $"<b>Unsupported: <i>Type variance {tp.Variance} not supported</i></b>";
        return false;
      }
      why = null;
      return true;
    }

    protected override IClassWriter DeclareDatatype(DatatypeDecl dt, ConcreteSyntaxTree wr) {
      if (currentBuilder is DatatypeContainer builder) {
        var typeParams = GenTypeParams(dt.TypeArgs);

        IEnumerable<DAST.DatatypeCtor> ctors =
          from ctor in dt.Ctors
          let allDtors =
            from arg in ctor.Formals
            where !arg.IsGhost
            let formalName = Sequence<Rune>.UnicodeFromString(GetDestructorFormalName(arg))
            let formalType = GenType(arg.Type)
            let formalCallName = GetExtractOverrideName(arg.Attributes, null)
            let dtorName =
              formalCallName == null ? Option<Sequence<Rune>>.create_None() :
              Option<Sequence<Rune>>.create_Some((Sequence<Rune>)Sequence<Rune>.UnicodeFromString(formalCallName))
            let formalAttributes = ParseAttributes(arg.Attributes)
            select (DAST.DatatypeDtor)DAST.DatatypeDtor.create_DatatypeDtor((DAST.Formal)DAST.Formal.create_Formal(
              formalName, formalType, formalAttributes), dtorName)
          let args = Sequence<DAST.DatatypeDtor>.FromArray(allDtors.ToArray<DatatypeDtor>())
          select (DAST.DatatypeCtor)DAST.DatatypeCtor.create_DatatypeCtor(
            Sequence<Rune>.UnicodeFromString(ctor.GetCompileName(Options)),
            Sequence<Rune>.UnicodeFromString(GetDocString(ctor)),
            args, ctor.Formals.Count > 0);
        var superClasses = dt.ParentTypeInformation.UniqueParentTraits();
        var superTraitTypes = superClasses.Select(GenType).ToList();

        var superNegativeTraitTypes = GetNegativeTraitTypes(superClasses);

        var equalitySupport = GenEqualitySupport(dt);

        var datatypeBuilder = builder.Datatype(
          dt.GetCompileName(Options),
          dt.EnclosingModuleDefinition.GetCompileName(Options),
          typeParams,
          ctors.ToList(),
          dt is CoDatatypeDecl,
          ParseAttributes(dt.Attributes),
          GetDocString(dt),
          superTraitTypes,
          superNegativeTraitTypes, equalitySupport);

        return new ClassWriter(this, typeParams.Count > 0, datatypeBuilder);
      } else {
        throw new InvalidOperationException("Cannot declare datatype outside of a module: " + currentBuilder);
      }
    }

    private List<TypeArgDecl> GenTypeParams(List<TypeParameter> typePargs) {
      List<DAST.TypeArgDecl> typeParams = [];
      foreach (var tp in typePargs) {
        typeParams.Add(GenTypeArgDecl(tp));
      }

      return typeParams;
    }

    // Given a list of super traits implemented by a datatype,
    // find the list of all instantiated traits that the super traits can be downcasted to,
    // but that are not in the super classes,
    // and return them
    private List<DAST.Type> GetNegativeTraitTypes(List<Type> superClasses) {
      var superNegativeTraitTypes = new List<DAST.Type>();
      var traitDeclsNegative = new HashSet<TraitDecl>();
      var traitDeclsImplemented = superClasses.Select(t => t.AsTraitType)
        .Where(t => t != null).ToHashSet();
      foreach (var superClass in superClasses) {
        if (superClass.AsTraitType is { } traitDecl) {
          var downcastableTraitTypes = traitDecl.DowncastableSubTraitsIfMonomorphized();
          foreach (var downcastableTraitType in downcastableTraitTypes) {
            if (downcastableTraitType is { AsTraitType: { } downcastTraitDecl } &&
                !traitDeclsNegative.Contains(downcastTraitDecl) && !traitDeclsImplemented.Contains(downcastTraitDecl)) {
              traitDeclsNegative.Add(downcastTraitDecl);
              // downcastableTraitType is instantiated with the type parameters of traitDecl
              var typeParametersInstantiation =
                traitDecl.TypeArgs.Zip(superClass.TypeArgs).ToDictionary(kv => kv.Item1, kv => kv.Item2);
              var typeForDatatype = downcastableTraitType.Subst(typeParametersInstantiation);
              superNegativeTraitTypes.Add(GenType(typeForDatatype));
            }
          }
        }
      }

      return superNegativeTraitTypes;
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, ConcreteSyntaxTree wr) {
      if (currentBuilder is NewtypeContainer builder) {
        List<DAST.Statement> witnessStmts = [];
        DAST.Expression witness = null;
        var statementBuf = new StatementBuffer();
        if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
          EmitExpr(
            nt.Witness, false,
            EmitCoercionIfNecessary(nt.Witness.Type, nt.BaseType, nt.Witness.Origin,
              WrBuffer(out var buf)),
            new BuilderSyntaxTree<StatementContainer>(statementBuf, this)
          );
          witness = buf.Finish();
          witnessStmts = statementBuf.PopAll();
        }

        Option<DAST.NewtypeConstraint> constraint;
        if (((RedirectingTypeDecl)nt).ConstraintIsCompilable) {
          // To check if something is compilable for a newtype, we need to convert the variable to the base type
          var type = UserDefinedType.FromTopLevelDecl(nt.Origin, (TopLevelDecl)nt);
          var sourceFormal = new Formal(nt.Origin, "_source", type, true, false, null);
          var statementBuffer = new StatementBuffer();
          var wStmt = new BuilderSyntaxTree<StatementContainer>(statementBuffer, this);
          GenerateIsMethodBody(nt, sourceFormal, wStmt);
          constraint = (Option<DAST.NewtypeConstraint>)Option<DAST.NewtypeConstraint>.create_Some(
            (DAST.NewtypeConstraint)DAST.NewtypeConstraint.create_NewtypeConstraint(
              (DAST.Formal)DAST.Formal.create_Formal(
                Sequence<Rune>.UnicodeFromString(IdProtect(sourceFormal.CompileNameShadowable)), GenType(type), ParseAttributes(null)),
              Sequence<DAST.Statement>.FromArray(statementBuffer.PopAll().ToArray())));
        } else {
          constraint = (Option<DAST.NewtypeConstraint>)Option<DAST.NewtypeConstraint>.create_None();
        }
        var equalitySupport = GenEqualitySupport(nt);
        var typeParams = GenTypeParams(nt.TypeArgs);
        return new ClassWriter(this, false, builder.Newtype(
          nt.GetCompileName(Options), typeParams,
          GenType(nt.BaseType), NativeTypeToNewtypeRange(nt, false),
            constraint, witnessStmts, witness, ParseAttributes(nt.Attributes), GetDocString(nt), equalitySupport));
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
        var overflows = typ is BitvectorType;
        var CreateNewtype = (string baseName, DAST._INewtypeRange newTypeRange) =>
          DAST.Type.create_UserDefined(
            DAST.ResolvedType.create_ResolvedType(
              Sequence<ISequence<Rune>>.FromElements(
                Sequence<Rune>.UnicodeFromString(baseName)
              ),
              Sequence<DAST.Type>.Empty,
              DAST.ResolvedTypeBase.create_Newtype(
                DAST.Type.create_Primitive(DAST.Primitive.create_Int()),
                newTypeRange,
                true
              ),
              Sequence<DAST.Attribute>.Empty,
              Sequence<ISequence<Rune>>.Empty,
              Sequence<DAST.Type>.Empty
            )
          );
        return (DAST.Type)(AsNativeType(xType).Sel switch {
          NativeType.Selection.Byte => CreateNewtype("u8", DAST.NewtypeRange.create_U8(overflows)),
          NativeType.Selection.SByte => CreateNewtype("i8", DAST.NewtypeRange.create_I8(overflows)),
          NativeType.Selection.Short => CreateNewtype("i16", DAST.NewtypeRange.create_I16(overflows)),
          NativeType.Selection.UShort => CreateNewtype("u16", DAST.NewtypeRange.create_U16(overflows)),
          NativeType.Selection.Int => CreateNewtype("i32", DAST.NewtypeRange.create_I32(overflows)),
          NativeType.Selection.UInt => CreateNewtype("u32", DAST.NewtypeRange.create_U32(overflows)),
          NativeType.Selection.Long => CreateNewtype("i64", DAST.NewtypeRange.create_I64(overflows)),
          NativeType.Selection.ULong => CreateNewtype("u64", DAST.NewtypeRange.create_U64(overflows)),
          NativeType.Selection.DoubleLong => CreateNewtype("i128", DAST.NewtypeRange.create_I128(overflows)),
          NativeType.Selection.UDoubleLong => CreateNewtype("u128", DAST.NewtypeRange.create_U128(overflows)),
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
      } else {
        var why = "<i>Type name for " + xType + " (" + typ.GetType() + ")</i>";
        AddUnsupported(typ.Origin, why);
        return (DAST.Type)DAST.Type.create_Passthrough(Sequence<Rune>.UnicodeFromString($"<b>Unsupported: {why}</b>"));
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, ConcreteSyntaxTree wr) {
      if (currentBuilder is not SynonymTypeContainer builder) {
        throw new InvalidOperationException();
      }

      var erasedType = sst.Rhs.NormalizeExpand();

      List<DAST.Statement> witnessStmts = [];
      DAST.Expression witness = null;
      var statementBuf = new StatementBuffer();
      if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
        EmitExpr(
          sst.Witness, false,
          EmitCoercionIfNecessary(sst.Witness.Type, erasedType, sst.Witness.Origin,
            WrBuffer(out var buf)),
          new BuilderSyntaxTree<StatementContainer>(statementBuf, this)
        );
        witness = buf.Finish();
        witnessStmts = statementBuf.PopAll();
      }

      List<DAST.TypeArgDecl> typeParams = [];
      foreach (var tp in sst.TypeArgs) {
        typeParams.Add(GenTypeArgDecl(tp, tp.Name)); // TODO: Test if we can remove the second argument
      }

      builder.SynonymType(sst.GetCompileName(Options), typeParams,
        GenType(erasedType), witnessStmts, witness,
        ParseAttributes(sst.Attributes), GetDocString(sst)).Finish();
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix, out bool needsCastAfterArithmetic) {
      name = null;
      literalSuffix = null;
      needsCastAfterArithmetic = false;
    }


    private Sequence<DAST.Formal> GenFormals(List<Formal> formals) {
      List<DAST.Formal> paramsList = [];
      foreach (var param in formals) {
        if (!param.IsGhost) {
          paramsList.Add((DAST.Formal)DAST.Formal.create_Formal(
            Sequence<Rune>.UnicodeFromString(IdProtect(param.CompileName)), GenType(param.Type), ParseAttributes(param.Attributes)));
        }
      }

      Sequence<DAST.Formal> params_ = (Sequence<DAST.Formal>)Sequence<DAST.Formal>.FromArray(paramsList.ToArray());
      return params_;
    }

    protected override void TrDividedBlockStmt(Constructor m, DividedBlockStmt dividedBlockStmt, ConcreteSyntaxTree writer) {
      TrStmtList(dividedBlockStmt.BodyInit, writer);
      if (writer is BuilderSyntaxTree<StatementContainer> builder) {
        var membersToInitialize = ((TopLevelDeclWithMembers)m.EnclosingClass).Members.Where((md =>
          md is Field and not ConstantField { Rhs: { } }));
        var outFields = membersToInitialize.Select((MemberDecl md) => {
          var formal = DAST.Formal.create_Formal(
            Sequence<Rune>.UnicodeFromString(
              (md is ConstantField ? InternalFieldPrefix : "") +
              md.GetCompileName(Options)),
            GenType(((Field)md).Type.Subst(((TopLevelDeclWithMembers)((Field)md).EnclosingClass)
              .ParentFormalTypeParametersToActuals))
            , ParseAttributes(md.Attributes)
          );
          return DAST.Field.create_Field(formal, md is ConstantField,
            Std.Wrappers.Option<DAST.Expression>.create_None(), md.HasStaticKeyword);
        }
        ).ToList();
        builder.Builder.AddStatement((DAST.Statement)DAST.Statement.create_ConstructorNewSeparator(
          Sequence<_IField>.FromArray(outFields.ToArray())));
      } else {
        throw new InvalidCastException("Divided block statement outside of a statement container");
      }
      // We need to indicate to Dafny that 
      TrStmtList(dividedBlockStmt.BodyProper, writer);
    }

    protected override bool InstanceConstAreStatic() {
      return false;
    }

    [CanBeNull]
    public MemberDecl GetTopMostOverriddenMemberDeclIfDifferent(MemberDecl member) {
      while (member.OverriddenMember is { OverriddenMember: { } } upMember) {
        member = upMember;
      }
      return member.OverriddenMember;
    }

    private class ClassWriter : IClassWriter {
      private readonly DafnyCodeGenerator compiler;
      private readonly ClassLike builder;
      private readonly bool hasTypeArgs;
      private readonly List<MethodBuilder> methods = [];

      public ClassWriter(DafnyCodeGenerator compiler, bool hasTypeArgs, ClassLike builder) {
        this.compiler = compiler;
        this.hasTypeArgs = hasTypeArgs;
        this.builder = builder;
      }

      public ConcreteSyntaxTree CreateMethod(MethodOrConstructor m, List<TypeArgumentInstantiation> typeArgs, bool createBody,
        bool forBodyInheritance, bool lookasideBody) {
        var astTypeArgs = m.TypeArgs.Select(typeArg => compiler.GenTypeArgDecl(typeArg)).ToList();

        var params_ = compiler.GetParameters(m, out var inheritedParams, out var overriddenMethod);

        List<ISequence<Rune>> outVars = [];
        List<DAST.Type> outTypes = [];
        foreach (var outVar in m.Outs) {
          if (!outVar.IsGhost) {
            outVars.Add(Sequence<Rune>.UnicodeFromString(compiler.IdProtect(outVar.GetOrCreateCompileName(m.CodeGenIdGenerator))));
            outTypes.Add(compiler.GenType(outVar.Type));
          }
        }


        var overridingTrait = overriddenMethod?.EnclosingClass;
        if (m is Constructor { EnclosingClass: TopLevelDeclWithMembers cm }) {
          // Constructors need to assign all fields without RHS
          var membersToInitialize = cm.Members.Where((md =>
            md is Field and not ConstantField { Rhs: { } } && !md.IsGhost));
          outVars = membersToInitialize.Select((MemberDecl md) =>
            Sequence<Rune>.UnicodeFromString(
              (md is ConstantField ? compiler.InternalFieldPrefix : "") +
              md.GetCompileName(compiler.Options))
          ).ToList();
          /*outTypes = membersToInitialize.Select((MemberDecl md) =>
            GenType(md.GetType())
          ).ToList();*/
        }

        var attributes = compiler.ParseAttributes(m.Attributes);
        var builder = this.builder.Method(
          m.IsStatic, createBody, m is Constructor, false,
          overridingTrait != null ? compiler.PathFromTopLevel(overridingTrait) : null,
          compiler.GetDocString(m),
          attributes,
          m.GetCompileName(compiler.Options),
          astTypeArgs, params_, inheritedParams,
          outTypes, outVars);
        methods.Add(builder);

        if (createBody) {
          return new BuilderSyntaxTree<StatementContainer>(builder, this.compiler);
        } else {
          // TODO(shadaj): actually create a trait
          return null;
        }
      }

      public ConcreteSyntaxTree SynthesizeMethod(Method m, List<TypeArgumentInstantiation> typeArgs, bool createBody, bool forBodyInheritance, bool lookasideBody) {
        compiler.AddUnsupportedFeature(m.Origin, Feature.MethodSynthesis);
        return new BuilderSyntaxTree<StatementContainer>(new StatementBuffer(), this.compiler);
      }

      public ConcreteSyntaxTree CreateFunction(string name, List<TypeArgumentInstantiation> typeArgs,
          List<Formal> formals, Type resultType, IOrigin tok, bool isStatic, bool createBody, MemberDecl member,
          bool forBodyInheritance, bool lookasideBody) {

        var astTypeArgs = (member is Function fun ? fun.TypeArgs : Enumerable.Empty<TypeParameter>()).Select(typeArg => compiler.GenTypeArgDecl(typeArg)).ToList();

        Sequence<DAST.Formal> params_;
        Sequence<DAST.Formal> inheritedParams;
        MemberDecl overridingFunction;
        if (member is Function fun2) {
          params_ = compiler.GetParameters(fun2, out inheritedParams, out overridingFunction);
        } else {
          params_ = compiler.GenFormals(formals);
          overridingFunction = compiler.GetTopMostOverriddenMemberDeclIfDifferent(member);
          inheritedParams = params_;
        }

        var overridingTrait = overridingFunction?.EnclosingClass;

        var attributes = compiler.ParseAttributes(member.Attributes);
        var builder = this.builder.Method(
          isStatic, createBody, false, true,
          overridingTrait != null ? compiler.PathFromTopLevel(overridingTrait) : null,
          compiler.GetDocString(member),
          attributes,
          name,
          astTypeArgs, params_, inheritedParams,
          [compiler.GenType(resultType)], null);
        methods.Add(builder);

        if (createBody) {
          return new BuilderSyntaxTree<StatementContainer>(builder, this.compiler);
        } else {
          return null;
        }
      }

      public ConcreteSyntaxTree CreateGetter(string name, TopLevelDecl enclosingDecl, Type resultType, IOrigin tok,
          bool isStatic, bool isConst, bool createBody, MemberDecl member, bool forBodyInheritance) {
        var overridingTrait = compiler.GetTopMostOverriddenMemberDeclIfDifferent(member)?.EnclosingClass;

        var attributes = compiler.ParseAttributes(enclosingDecl.Attributes);

        var builder = this.builder.Method(
          isStatic, createBody, false, true,
          overridingTrait != null ? compiler.PathFromTopLevel(overridingTrait) : null,
          compiler.GetDocString(member),
          attributes,
          name,
          [], (Sequence<DAST.Formal>)Sequence<DAST.Formal>.Empty,
          (Sequence<DAST.Formal>)Sequence<DAST.Formal>.Empty,
          [compiler.GenType(resultType)], null);
        methods.Add(builder);

        if (createBody) {
          return new BuilderSyntaxTree<StatementContainer>(builder, this.compiler);
        } else {
          return null;
        }
      }

      public ConcreteSyntaxTree CreateGetterSetter(string name, Type resultType, IOrigin tok,
          bool createBody, MemberDecl member, out ConcreteSyntaxTree setterWriter, bool forBodyInheritance) {
        compiler.AddUnsupported(tok, "<i>Create Getter Setter</i>");
        if (createBody) {
          setterWriter = new BuilderSyntaxTree<StatementContainer>(new StatementBuffer(), this.compiler);
          return new BuilderSyntaxTree<StatementContainer>(new StatementBuffer(), this.compiler);
        } else {
          setterWriter = null;
          return null;
        }
      }

      public void DeclareField(string name, TopLevelDecl enclosingDecl, bool isStatic, bool isConst, Type type,
          IOrigin tok, string rhs, Field field) {
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
          compiler.GenType(type),
          compiler.ParseAttributes(field.Attributes)
        ), isConst || field is ConstantField, rhsExpr, field.IsStatic);
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

    protected override string TypeDescriptor(Type type, ConcreteSyntaxTree wr, IOrigin tok) {
      type = DatatypeWrapperEraser.SimplifyType(Options, type);
      return type.ToString();
    }

    protected override ConcreteSyntaxTree EmitMethodReturns(MethodOrConstructor m, ConcreteSyntaxTree wr) {
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

    public override string TailRecursiveVar(int inParamIndex, IVariable variable) {
      return preventShadowing ? base.TailRecursiveVar(inParamIndex, variable) : Defs.__default.TailRecursionPrefix.ToVerbatimString(false) + inParamIndex;
    }

    protected override void EmitJumpToTailCallStart(ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        stmtContainer.Builder.AddStatement((DAST.Statement)DAST.Statement.create_JumpTailCallStart());
      } else {
        throw new InvalidOperationException();
      }
    }

    internal override string TypeName(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl/*?*/ member = null) {
      return "PLACEBO_TYPE";
    }

    // sometimes, the compiler generates the initial value before the declaration,
    // so we buffer it here
    _IOption<DAST._IExpression> bufferedInitializationValue = null;

    // And its statements here
    _IOption<List<DAST.Statement>> bufferedInitializationStmts = null;

    protected override string TypeInitializationValue(Type type, ConcreteSyntaxTree wr, IOrigin tok,
        bool usePlaceboValue, bool constructTypeParameterDefaultsFromTypeDescriptors) {
      if (bufferedInitializationValue != null) {
        throw new InvalidOperationException();
      } else {
        type = type.NormalizeExpandKeepConstraints();
        if (usePlaceboValue) {
          bufferedInitializationValue = Option<DAST._IExpression>.create_None();
          bufferedInitializationStmts = Option<List<DAST.Statement>>.create_None();
        } else {
          if (type.AsNewtype is { WitnessKind: SubsetTypeDecl.WKind.Compiled } newType) {
            var bufStmt = new StatementBuffer();
            bufferedInitializationValue = Option<DAST._IExpression>.create_Some(
              DAST.Expression.create_Convert(
              ConvertExpression(newType.Witness, new BuilderSyntaxTree<StatementContainer>(bufStmt, this)),
                  GenType(newType.BaseType),
              GenType(UserDefinedType.FromTopLevelDecl(newType.Witness.Origin, newType))
              ));
            bufferedInitializationStmts = Option<List<DAST.Statement>>.create_Some(bufStmt.PopAll());
          } else if (type.AsSubsetType != null && type.AsSubsetType.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
            var bufStmt = new StatementBuffer();
            bufferedInitializationValue = Option<DAST._IExpression>.create_Some(
              ConvertExpression(type.AsSubsetType.Witness, new BuilderSyntaxTree<StatementContainer>(bufStmt, this)));
            bufferedInitializationStmts = Option<List<DAST.Statement>>.create_Some(bufStmt.PopAll());
          } else {
            bufferedInitializationValue = Option<DAST._IExpression>.create_Some(
              DAST.Expression.create_InitializationValue(GenType(type))
            );
            bufferedInitializationStmts = Option<List<DAST.Statement>>.create_None();
          }
        }
        return "BUFFERED"; // used by DeclareLocal(Out)Var
      }
    }

    protected override string TypeName_UDT(string fullCompileName, List<TypeParameter.TPVariance> variance,
        List<Type> typeArgs, ConcreteSyntaxTree wr, IOrigin tok, bool omitTypeArguments) {
      return fullCompileName;
    }

    internal override string TypeName_Companion(Type type, ConcreteSyntaxTree wr, IOrigin tok, MemberDecl member) {
      ExprContainer actualBuilder;
      if (wr is BuilderSyntaxTree<ExprContainer> st) {
        actualBuilder = st.Builder;
      } else {
        throw new InvalidOperationException();
      }

      EmitTypeName_Companion(type, new BuilderSyntaxTree<ExprContainer>(actualBuilder, this), wr, tok, member);
      return "";
    }

    protected override void EmitTypeName_Companion(Type type, ConcreteSyntaxTree wr, ConcreteSyntaxTree surrounding, IOrigin tok, MemberDecl member) {
      if (wr is BuilderSyntaxTree<ExprContainer> container) {
        type = UserDefinedType.UpcastToMemberEnclosingType(type, member);
        var typeArgs = Sequence<DAST.Type>.FromArray(type.TypeArgs.Select(GenType).ToArray());

        if (type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
            DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) {
          container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(udt.ResolvedClass), typeArgs));
        } else {
          if (type.AsTopLevelTypeWithMembers == null) { // git-issues/git-issue-697g.dfy while iterating over "nat"
            AddUnsupportedFeature(tok, Feature.SubtypeConstraintsInQuantifiers);
          } else {
            container.Builder.AddExpr(
              (DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(type.AsTopLevelTypeWithMembers), typeArgs));
          }
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitNameAndActualTypeArgs(string protectedName, List<Type> typeArgs, IOrigin tok,
     Expression replacementReceiver, bool receiverAsArgument, ConcreteSyntaxTree wr) {
      Option<_IFormal> receiverArg;
      var receiverBeforeName = replacementReceiver != null && replacementReceiver is not StaticReceiverExpr;
      Option<DAST.Type> receiverType = receiverBeforeName && !receiverAsArgument
        ? (Option<DAST.Type>)Option<DAST.Type>.create_Some(GenType(replacementReceiver.Type))
        : (Option<DAST.Type>)Option<DAST.Type>.create_None();
      if (receiverBeforeName) {
        var name = replacementReceiver is IdentifierExpr { Var: { } variable } && variable.GetOrCreateCompileName(enclosingDeclaration.CodeGenIdGenerator) is var compileName
          ? compileName
          : "receiver";
        receiverArg = (Option<_IFormal>)Option<DAST._IFormal>.create_Some(
          DAST.Formal.create_Formal(Sequence<Rune>.UnicodeFromString(name),
          GenType(replacementReceiver.Type), ParseAttributes(null)));
      } else {
        receiverArg = (Option<_IFormal>)Option<_IFormal>.create_None();
      }

      if (GetExprBuilder(wr, out var st) && st.Builder is CallExprBuilder callExpr) {
        var signature = callExpr.Signature;
        callExpr.SetName((DAST.CallName)DAST.CallName.create_CallName(Sequence<Rune>.UnicodeFromString(protectedName), receiverType, receiverArg, receiverAsArgument, signature));
      } else if (GetExprBuilder(wr, out var st2) && st2.Builder is CallStmtBuilder callStmt) {
        var signature = callStmt.Signature;
        callStmt.SetName((DAST.CallName)DAST.CallName.create_CallName(Sequence<Rune>.UnicodeFromString(protectedName), receiverType, receiverArg, receiverAsArgument, signature));
      } else {
        AddUnsupported(tok, "Builder issue: wr is as " + wr.GetType() +
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

    protected override bool DeclareFormal(string prefix, string name, Type type, IOrigin tok, bool isInParam, ConcreteSyntaxTree wr) {
      AddUnsupported(tok, "<i>Declare formal</i>");
      return true;
    }

    DeclareBuilder tmpDeclareBuilder;

    protected override ConcreteSyntaxTree EmitAssignmentRhs(ConcreteSyntaxTree wr) {
      if (tmpDeclareBuilder == null) {
        return base.EmitAssignmentRhs(wr);
      }
      var t = tmpDeclareBuilder;
      tmpDeclareBuilder = null;
      return new BuilderSyntaxTree<ExprContainer>(t, this);
    }

    protected override void DeclareLocalVar(string name, Type type, IOrigin tok, bool leaveRoomForRhs, string rhs,
        ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var typ = GenType(type);

        if (rhs == null) {
          // we expect an initializer to come *after* this declaration
          var variable = stmtContainer.Builder.DeclareAndAssign(typ, name);

          if (leaveRoomForRhs) {
            tmpDeclareBuilder = variable;
          }
        } else if (rhs == "BUFFERED") {
          if (bufferedInitializationValue == null) {
            throw new InvalidOperationException(
              "Expected a buffered value to have been populated because rhs != null");
          }

          var rhsValue = bufferedInitializationValue;
          bufferedInitializationValue = null;

          if (bufferedInitializationStmts is { is_Some: true }) {
            foreach (var stmt in bufferedInitializationStmts.dtor_value) {
              stmtContainer.Builder.AddStatement(stmt);
            }

            bufferedInitializationStmts = null;
          }

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

    protected override ConcreteSyntaxTree DeclareLocalVar(string name, Type type, IOrigin tok, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var variable = stmtContainer.Builder.DeclareAndAssign(GenType(type), name);
        return new BuilderSyntaxTree<ExprContainer>(variable, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override bool UseReturnStyleOuts(MethodOrConstructor m, int nonGhostOutCount) => true;
    protected override bool SupportsMultipleReturns => true;

    protected override void DeclareLocalOutVar(string name, Type type, IOrigin tok, string rhs, bool useReturnStyleOuts,
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
          var signature = GetCallSignature(s.Method); ;
          var callBuilder = stmtContainer.Builder.Call(signature);
          base.TrCallStmt(s, receiverReplacement, new BuilderSyntaxTree<ExprContainer>(callBuilder, this), wrStmts, wrStmtsAfterCall);
        }
      } else {
        throw new InvalidOperationException("Cannot call statement in this context: " + currentBuilder);
      }
    }

    public override bool NeedsCustomReceiverNotTrait(MemberDecl member) {
      return member is Constructor || base.NeedsCustomReceiverNotTrait(member);
    }

    protected override void EmitStaticExternMethodQualifier(string qual, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_ExternCompanion(
          Sequence<ISequence<Rune>>.FromArray([
            Defs.__default.DAFNY__EXTERN__MODULE,
            Sequence<Rune>.UnicodeFromString(qual)
          ])
          ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitCallToInheritedMethod(MethodOrConstructor method, [CanBeNull] TopLevelDeclWithMembers heir, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, ConcreteSyntaxTree wStmtsAfterCall) {
      if (wr is BuilderSyntaxTree<StatementContainer> stmtContainer) {
        var signature = GetCallSignature(method);
        var callBuilder = stmtContainer.Builder.Call(signature);
        base.EmitCallToInheritedMethod(method, heir, new BuilderSyntaxTree<ExprContainer>(callBuilder, this), wStmts, wStmtsAfterCall);
      } else {
        throw new InvalidOperationException("Cannot call inherited method in this context: " + currentBuilder);
      }
    }

    private _ICallSignature GetCallSignature(MethodOrFunction method) {
      var parameters = GetParameters(method, out var inheritedParameters, out _);
      var signature = DAST.CallSignature.create_CallSignature(parameters, inheritedParameters);
      return signature;
    }

    private Sequence<DAST.Formal> GetParameters(MethodOrFunction method, out Sequence<DAST.Formal> inheritedParameters, out MemberDecl inheritedMethod) {
      var parameters = GenFormals(method.Ins);
      inheritedMethod = GetTopMostOverriddenMemberDeclIfDifferent(method);
      var oldThisContext = thisContext;
      thisContext = null;
      inheritedParameters = inheritedMethod is MethodOrFunction m ? GenFormals(m.Ins) : parameters;
      thisContext = oldThisContext;
      return parameters;
    }

    protected override ConcreteSyntaxTree StartCall(Function f, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<ExprContainer> exprContainer) {
        var signature = GetCallSignature(f);
        var callBuilder = exprContainer.Builder.Call(signature);
        return new BuilderSyntaxTree<ExprContainer>(callBuilder, this);
      } else {
        throw new InvalidOperationException("Cannot call inherited function in this context: " + currentBuilder);
      }
    }

    protected override void EmitMultiReturnTuple(List<Formal> outs, List<Type> outTypes, List<string> outTmps, IOrigin methodToken, ConcreteSyntaxTree wr) {
      // nothing to do, we auto-emit a return for the method
    }

    protected override void CompileFunctionCallExpr(FunctionCallExpr e, ConcreteSyntaxTree wr, bool inLetExprBody,
        ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr, bool alreadyCoerced) {
      var toType = e.Type.Subst(e.GetTypeArgumentSubstitutions());
      var fromType = e.Function.Original.ResultType.Subst(e.GetTypeArgumentSubstitutions());
      if (thisContext != null) {
        toType = toType.Subst(thisContext.ParentFormalTypeParametersToActuals);
        fromType = fromType.Subst(thisContext.ParentFormalTypeParametersToActuals);
      }
      wr = EmitCoercionIfNecessary(fromType, toType, e.Origin, wr);

      if (wr is BuilderSyntaxTree<ExprContainer> builder) {
        var signature = GetCallSignature(e.Function);
        var callBuilder = builder.Builder.Call(signature);
        base.CompileFunctionCallExpr(e, new BuilderSyntaxTree<ExprContainer>(callBuilder, this), inLetExprBody, wStmts, tr, true);
      } else {
        throw new InvalidOperationException("Cannot call function in this context: " + currentBuilder);
      }
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, IOrigin tok, ConcreteSyntaxTree wr) {
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
          compiler.AddUnsupported(Token.NoToken, "<i>EmitRead</i> without ExprContainer builder");
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
      EmitExpr(
        ll.Seq, false,
        EmitCoercionIfNecessary(
          ll.Seq.Type,
          ll.Seq.Type.IsNonNullRefType || !ll.Seq.Type.IsRefType ? null : UserDefinedType.CreateNonNullType((UserDefinedType)ll.Seq.Type.NormalizeExpand()),
          ll.Origin, WrBuffer(out var sourceBuf)
        ),
        wStmts
      );

      EmitExpr(ll.E0, false, WrBuffer(out var indexBuf), wStmts);

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
      if (ll.Indices.Count > 16) {
        throw new UnsupportedFeatureException(ll.Origin, Feature.ArraysWithMoreThan16Dims);
      }

      if (!ll.Array.Type.IsArrayType) {
        throw new InvalidOperationException();
      }

      var targetType = ll.Array.Type.IsNonNullRefType || !ll.Array.Type.IsRefType
        ? null
        : UserDefinedType.CreateNonNullType((UserDefinedType)ll.Array.Type.NormalizeExpand());

      var coercion = EmitCoercionIfNecessary(
        ll.Array.Type,
        targetType,
        ll.Origin,
        WrBuffer(out var arrayBuf)
      );

      EmitExpr(ll.Array, false, coercion, wStmts);

      var array = arrayBuf.Finish();

      var indices = ll.Indices.Select(idx => {
        EmitExpr(idx, false, WrBuffer(out var indexBuf), wStmts);
        return indexBuf.Finish();
      }).ToArray();

      return new ExprLvalue(
        (DAST.Expression)DAST.Expression.create_Index(array, DAST.CollKind.create_Array(), Sequence<DAST.Expression>.FromElements(indices)),
        (DAST.AssignLhs)DAST.AssignLhs.create_Index(array, Sequence<DAST.Expression>.FromElements(indices)),
        this
      );
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

    protected override void EmitHalt(IOrigin tok, Expression messageExpr, ConcreteSyntaxTree wr) {
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

    // Return a writer to write the start expression, which is lo if going up, and hi if going down
    protected override ConcreteSyntaxTree EmitForStmt(IOrigin tok, IVariable loopIndex, bool goingUp, string endVarName,
      List<Statement> body, List<Label> labels, ConcreteSyntaxTree wr) {
      if (GetStatementBuilder(wr, out var statementContainer)) {
        var indexName = loopIndex.CompileNameShadowable;
        ForeachBuilder foreachBuilder = statementContainer.Builder.Foreach(
          indexName, GenType(loopIndex.Type));
        if (endVarName == null) {
          var startBuilder = ((ExprContainer)foreachBuilder).Wrapper(start =>
            (DAST.Expression)DAST.Expression.create_UnboundedIntRange(
              start,
              goingUp
            ));
          ConcreteSyntaxTree bodyWr = new BuilderSyntaxTree<StatementContainer>(foreachBuilder, this);
          bodyWr = EmitContinueLabel(labels, bodyWr);
          TrStmtList(body, bodyWr);
          return new BuilderSyntaxTree<ExprContainer>(startBuilder, this);
        } else {
          var loHiBuilder = ((ExprContainer)foreachBuilder).BinOp("int_range", (DAST.Expression lo, DAST.Expression hi) =>
             (DAST.Expression)DAST.Expression.create_IntRange(
               GenType(loopIndex.Type),
               lo,
               hi,
               goingUp
             ));
          ConcreteSyntaxTree bodyWr = new BuilderSyntaxTree<StatementContainer>(foreachBuilder, this);
          bodyWr = EmitContinueLabel(labels, bodyWr);
          TrStmtList(body, bodyWr);
          BuilderSyntaxTree<ExprContainer> toReturn;
          if (goingUp) {
            toReturn = WrBuffer(out var loBuf);
            loHiBuilder.AddBuildable(loBuf);
          } else {
            toReturn = new BuilderSyntaxTree<ExprContainer>(loHiBuilder, this);
          }
          loHiBuilder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(endVarName)));
          return toReturn;
        }
      }
      throw new InvalidOperationException();
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

    protected override void EmitArrayLength(Action<ConcreteSyntaxTree> arr, AllocateArray typeRhs, int d, bool native,
      ConcreteSyntaxTree w) {
      var arrayLengthBuilder = new ArrayLengthBuilder(GenType(typeRhs.Type), d, native);
      arr(new BuilderSyntaxTree<ExprContainer>(arrayLengthBuilder, this));
      if (w is BuilderSyntaxTree<ExprContainer> expressionContainer) {
        expressionContainer.Builder.AddBuildable(arrayLengthBuilder);
      } else {
        throw new InvalidOperationException("ArrayLength within a non-expression context");
      }
    }

    protected override ConcreteSyntaxTree CreateForLoop(string indexVar,
      Action<ConcreteSyntaxTree> boundWriter, ConcreteSyntaxTree wr,
      string start = null) {
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var foreachBuilder = statementContainer.Builder.Foreach(indexVar, GenType(Dafny.Type.Int));
        var nativeRangeBuilder = new NativeRangeBuilder(start);
        foreachBuilder.AddBuildable(nativeRangeBuilder);
        boundWriter(new BuilderSyntaxTree<ExprContainer>(nativeRangeBuilder, this));
        return new BuilderSyntaxTree<StatementContainer>(foreachBuilder, this);
      }
      throw new InvalidOperationException("Not in a statement container");
    }

    protected override ConcreteSyntaxTree CreateDoublingForLoop(string indexVar, int start, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(Token.NoToken, Feature.ForLoops);
      return wr;
    }

    protected override void EmitIncrementVar(string varName, ConcreteSyntaxTree wr) {
      AddUnsupported(Token.NoToken, "<i>EmitIncrementVar</i>");
    }

    protected override void EmitDecrementVar(string varName, ConcreteSyntaxTree wr) {
      AddUnsupported(Token.NoToken, "<i>EmitDecrementVar</i>");
    }

    protected override ConcreteSyntaxTree EmitQuantifierExpr(Action<ConcreteSyntaxTree> collection, bool isForall, Type collectionElementType, BoundVar bv, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        var tp = GenType(collectionElementType);
        var argBuilder = builder.Builder.BinOp("quantifier",
          (DAST.Expression collectionExpr, DAST.Expression lambda) =>
            (DAST.Expression)DAST.Expression.create_Quantifier(tp, collectionExpr, isForall, lambda)
        );
        var wBody = new BuilderSyntaxTree<ExprContainer>(argBuilder, this);
        collection(wBody);
        return wBody;
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override string GetQuantifierName(string bvType) {
      throw new InvalidOperationException();
    }

    protected override ConcreteSyntaxTree CreateForeachLoop(string tmpVarName, Type collectionElementType, IOrigin tok,
      out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      if (wr is BuilderSyntaxTree<StatementContainer> statementContainer) {
        var foreachBuilder = statementContainer.Builder.Foreach(tmpVarName, GenType(collectionElementType));
        collectionWriter = new BuilderSyntaxTree<ExprContainer>(foreachBuilder, this);
        return new BuilderSyntaxTree<StatementContainer>(foreachBuilder, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override ConcreteSyntaxTree EmitDowncast(Type from, Type to, IOrigin tok, ConcreteSyntaxTree wr) {
      return wr;
    }

    protected override void EmitDowncastVariableAssignment(string boundVarName, Type boundVarType, string tmpVarName,
      Type sourceType, bool introduceBoundVar, IOrigin tok, ConcreteSyntaxTree wr) {
      var w = introduceBoundVar ? DeclareLocalVar(boundVarName, boundVarType, tok, wr) : IdentLvalue(boundVarName).EmitWrite(wr);
      EmitIdentifier(tmpVarName, EmitCoercionIfNecessary(sourceType, boundVarType, tok, w));
    }

    protected override ConcreteSyntaxTree CreateForeachIngredientLoop(string boundVarName, int L, string tupleTypeArgs,
        out ConcreteSyntaxTree collectionWriter, ConcreteSyntaxTree wr) {
      AddUnsupported(Token.NoToken, "<i>CreateForeachIngredientLoop</i>");
      collectionWriter = new BuilderSyntaxTree<ExprContainer>(new ExprBuffer(null), this);
      return new BuilderSyntaxTree<StatementContainer>(new StatementBuffer(), this);
    }

    protected override void EmitNew(Type type, IOrigin tok, CallStmt initCall, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var ctor = (Constructor)initCall?.Method;
        var arguments = Enumerable.Empty<DAST.Expression>();
        if (ctor != null && ctor.IsExtern(Options, out _, out _)) {
          // the arguments of any external constructor are placed here
          arguments = ctor.Ins.Select((f, i) => (f, i))
            .Where(tp => !tp.f.IsGhost)
            .Select(tp => {
              var localWriter = WrBuffer(out var buf);
              EmitExpr(initCall.Args[tp.i], false, localWriter, wStmts);
              return buf.Finish();
            });
        }

        if (ctor == null) {
          AddUnsupported(tok, "Creation of object of type " + type.ToString() + " requires a constructor");
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

    protected override void EmitNewArray(Type elementType, IOrigin tok, List<string> dimensions,
      bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      throw new InvalidOperationException();
    }

    protected override void EmitNewArray(Type elementType, IOrigin tok, List<Expression> dimensions, bool mustInitialize, [CanBeNull] string exampleElement, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var dimensionsAST = dimensions.Select(convert).ToArray();

        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_NewUninitArray(
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
        AddUnsupported(Token.NoToken, "Expected ExprContainer, got " + wr.GetType());
      }
    }

    // Overriden from SinglePassCodeGenerator to return a BuilderSyntaxTree
    // To avoid UnsupportedInvalidOperationException in EmitIdentifier by way of set comprehension (github issue 5644)
    protected override ConcreteSyntaxTree MaybeEmitCallToIsMethod(RedirectingTypeDecl declWithConstraints, List<Type> typeArguments, ConcreteSyntaxTree wr) {
      Contract.Requires(declWithConstraints is SubsetTypeDecl or NewtypeDecl);
      Contract.Requires(declWithConstraints.TypeArgs.Count == typeArguments.Count);
      Contract.Requires(declWithConstraints.ConstraintIsCompilable);
      switch (declWithConstraints) {
        case NonNullTypeDecl:
          // Non-null types don't have a special target class, so we just do the non-null constraint check here.
          return EmitNullTest(false, wr);
        case NewtypeDecl { TargetTypeCoversAllBitPatterns: true }: {
            EmitLiteralExpr(wr, Expression.CreateBoolLiteral(declWithConstraints.Tok, true));
            return new BuilderSyntaxTree<ExprContainer>(new ExprBuffer(null), this);
          }
        default: {
            // in mind that type parameters are not accessible in static methods in some target languages).
            var type = UserDefinedType.FromTopLevelDecl(declWithConstraints.Tok, (TopLevelDecl)declWithConstraints, typeArguments);
            return EmitCallToIsMethod(declWithConstraints, type, wr);
          }
      }
    }

    protected override void EmitLiteralExpr(ConcreteSyntaxTree wr, LiteralExpr e) {
      if (GetExprBuilder(wr, out var builder)) {
        DAST.Expression baseExpr;

        switch (e) {
          case CharLiteralExpr c:
            var codePoint = Util.UnescapedCharacters(Options, (string)c.Value, false).Single();
            if (Rune.IsRune(new BigInteger(codePoint))) { // More readable version in the generated code.
              baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_CharLiteral(
                new Rune(codePoint)
              ));
            } else {
              baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_CharLiteralUTF16(
                codePoint
              ));
            }

            break;
          case StringLiteralExpr str:
            if (!UnicodeCharEnabled && Util.TokensWithEscapes(str.AsStringLiteral(), false) is var tokens && tokens.Any((string token) => Util.Utf16Escape.IsMatch(token))) {
              var s = Util.UnescapedCharacters(UnicodeCharEnabled, str.AsStringLiteral(), true);
              var chars = tokens.Select((string singleChar) =>
                ConvertExpressionNoStatement(new CharLiteralExpr(Token.NoToken, singleChar) { Type = Type.Char })).ToArray();
              baseExpr = (DAST.Expression)DAST.Expression.create_SeqValue(Sequence<DAST.Expression>.FromArray(chars), GenType(new CharType()));
              // We need to emit a sequence of chars literal. We first 
            } else {
              baseExpr = (DAST.Expression)DAST.Expression.create_Literal(DAST.Literal.create_StringLiteral(
                Sequence<Rune>.UnicodeFromString(str.AsStringLiteral()), str.IsVerbatim
              ));
            }
            break;
          case StaticReceiverExpr:
            var typeArgs = Sequence<DAST.Type>.FromArray(e.Type.TypeArgs.Select(GenType).ToArray());

            if (e.Type.NormalizeExpandKeepConstraints() is UserDefinedType udt && udt.ResolvedClass is DatatypeDecl dt &&
                DatatypeWrapperEraser.IsErasableDatatypeWrapper(Options, dt, out _)) {
              baseExpr = (DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(udt.ResolvedClass), typeArgs);
            } else {
              baseExpr = (DAST.Expression)DAST.Expression.create_Companion(PathFromTopLevel(e.Type.AsTopLevelTypeWithMembers), typeArgs);
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

        if (e is not StaticReceiverExpr) {
          if (e.Type.AsNewtype != null) {
            baseExpr = (DAST.Expression)DAST.Expression.create_Convert(baseExpr, GenType(EraseNewtypeLayers(e.Type.AsNewtype)),
              GenType(e.Type));
          } else if (e.Type.AsSubsetType != null) {
            baseExpr = (DAST.Expression)DAST.Expression.create_Convert(baseExpr, GenType(e.Type),
              GenType(e.Type));
          }
        }

        builder.Builder.AddExpr(baseExpr);
      } else if (emitUncompilableCode && GetStatementBuilder(wr, out var builder2)) {
        builder2.Builder.AddStatement(StatementContainer.UnsupportedToStatement($"Cannot emit literal expression {e} outside of expression context: " + wr.GetType()));
      } else {
        throw new InvalidOperationException("Cannot emit literal expression outside of expression context: " + wr.GetType());
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, ConcreteSyntaxTree wr) {
      AddUnsupported(Token.NoToken, "<i>EmitStringLiteral</i>");
    }

    protected override ConcreteSyntaxTree EmitBitvectorTruncation(BitvectorType bvType, [CanBeNull] NativeType nativeType,
      bool surroundByUnchecked, ConcreteSyntaxTree wr) {
      if (nativeType != null && bvType.NativeType.Name == nativeType.Name && bvType.NativeType.Bitwidth == nativeType.Bitwidth) {
        return wr;
      }

      AddUnsupported(bvType.Origin, $"<i>EmitBitvectorTruncation from {bvType} to {nativeType}</i>");
      return wr;
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, ConcreteSyntaxTree wr,
        bool inLetExprBody, ConcreteSyntaxTree wStmts, FCE_Arg_Translator tr) {
      AddUnsupportedFeature(e0.Origin, Feature.BitvectorRotateFunctions);
    }

    protected override void EmitEmptyTupleList(string tupleTypeArgs, ConcreteSyntaxTree wr) {
      AddUnsupportedFeature(Token.NoToken, Feature.NonSequentializableForallStatements);
    }

    protected override ConcreteSyntaxTree EmitIngredients(ConcreteSyntaxTree wr, string ingredients, int L,
      string tupleTypeArgs, ForallStmt s, SingleAssignStmt s0, Expression rhs) {
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
      AddUnsupported(udt.Origin, "<i>FullTypeName</i>");
      return "FullTypeName";
    }

    private DAST.Type FullTypeNameAST(UserDefinedType udt, MemberDecl member = null) {
      if (udt.IsArrowType) {
        var arrow = udt.AsArrowType;
        return (DAST.Type)DAST.Type.create_Arrow(
          Sequence<DAST.Type>.FromArray(arrow.Args.Select(m => GenType(m)).ToArray()),
          GenType(arrow.Result)
        );
      } else if (udt.AsArrayType is var array && array != null) {
        return (DAST.Type)DAST.Type.create_Array(GenType(udt.TypeArgs[0]), array.Dims);
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

    private readonly Dictionary<TopLevelDecl, ISequence<ISequence<Rune>>> topLevelDeclPath = new();

    private ISequence<ISequence<Rune>> PathFromTopLevel(TopLevelDecl topLevel) {
      if (topLevel is NonNullTypeDecl { Class: var classLikeDecl } nonNullTypeDecl) {
        topLevel = classLikeDecl;
      }
      if (topLevelDeclPath.TryGetValue(topLevel, out var path)) {
        return path;
      }
      var enclosingName = topLevel.GetQualificationName(Options);
      var compileName = topLevel.GetCompileName(Options);
      List<ISequence<Rune>> pathList = [
        Sequence<Rune>.UnicodeFromString(enclosingName),
        Sequence<Rune>.UnicodeFromString(compileName)
      ];
      var p = Sequence<ISequence<Rune>>.FromArray(pathList.ToArray());
      topLevelDeclPath[topLevel] = p;
      return p;
    }

    private DAST.NewtypeRange NativeTypeToNewtypeRange(NewtypeDecl newtypeDecl, bool overflows) {
      var nativeType = newtypeDecl.NativeType;
      return (DAST.NewtypeRange)(nativeType?.Sel switch {
        NativeType.Selection.Byte => NewtypeRange.create_U8(overflows),
        NativeType.Selection.SByte => NewtypeRange.create_I8(overflows),
        NativeType.Selection.UShort => NewtypeRange.create_U16(overflows),
        NativeType.Selection.Short => NewtypeRange.create_I16(overflows),
        NativeType.Selection.UInt => NewtypeRange.create_U32(overflows),
        NativeType.Selection.Int => NewtypeRange.create_I32(overflows),
        NativeType.Selection.ULong => NewtypeRange.create_U64(overflows),
        NativeType.Selection.Long => NewtypeRange.create_I64(overflows),
        NativeType.Selection.UDoubleLong => NewtypeRange.create_U128(overflows),
        NativeType.Selection.DoubleLong => NewtypeRange.create_I128(overflows),
        _ =>
          EraseNewtypeLayers(newtypeDecl) is { } resType ?
            resType is BoolType ? NewtypeRange.create_Bool() :
              resType is MapType ? NewtypeRange.create_Map() :
                resType is SeqType ? NewtypeRange.create_Sequence()
              : NewtypeRange.create_NoRange() : NewtypeRange.create_NoRange()
      });
    }

    private ISequence<DAST.Attribute> ParseAttributes(Attributes attributes) {
      var a = attributes;
      var result = new List<DAST.Attribute>() { };
      while (a != null) {
        var name = Sequence<Rune>.UnicodeFromString(a.Name);
        var args = new List<Sequence<Rune>>();
        foreach (var arg in a.Args) {
          if (arg is Dafny.LiteralExpr { Value: var value }) {
            var argToAdd = "";
            if (value is string s) {
              argToAdd = s;
            } else if (value is bool b) {
              argToAdd = b ? "true" : "false";
            } else if (value is BigInteger big) {
              argToAdd = big.ToString();
            } else {
              argToAdd = "unknown " + value.GetType();
            }
            args.Add((Sequence<Rune>)Sequence<Rune>.UnicodeFromString(argToAdd));
          }
        }
        result.Add((DAST.Attribute)DAST.Attribute.create_Attribute(name,
          Sequence<Sequence<Rune>>.FromArray(args.ToArray())));
        a = a.Prev;
      }

      return Sequence<DAST.Attribute>.FromArray(result.ToArray());
    }

    protected override bool IsNewtypeErased(NewtypeDecl newtypeDecl) {
      var erasedIfNewtype = true;
      if (!Attributes.ContainsBool(newtypeDecl.Attributes, "rust_erased", ref erasedIfNewtype)) {
        var hasNoMember = !newtypeDecl.Members.Any();
        erasedIfNewtype = hasNoMember;
      }

      return erasedIfNewtype;
    }

    private DAST.Type TypeNameASTFromTopLevel(TopLevelDecl topLevel, List<Type> typeArgs) {
      var path = PathFromTopLevel(topLevel);

      if (topLevel is NonNullTypeDecl non) {
        topLevel = non.Rhs.AsTopLevelTypeWithMembers;
      }

      var properMethods = new List<Sequence<Rune>>();
      var extendedTraits = new List<DAST.Type>();

      if (topLevel is TopLevelDeclWithMembers memberContainer) {
        foreach (var member in memberContainer.Members) {
          if (member.OverriddenMember == null) {
            properMethods.Add((Sequence<Rune>)Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)));
          }
        }
      }

      var erasedIfNewtype = true;
      if (topLevel is NewtypeDecl newtypeDecl) {
        erasedIfNewtype = IsNewtypeErased(newtypeDecl);
      }

      foreach (var parentType in topLevel.ParentTypes(typeArgs, true)) {
        extendedTraits.Add(GenType(parentType));
      }

      var seqProperMethods = Sequence<Sequence<Rune>>.FromArray(properMethods.ToArray());
      var seqExtendTraits = Sequence<DAST.Type>.FromArray(extendedTraits.ToArray());
      var seqTypeArgs = Sequence<DAST.Type>.FromArray(typeArgs.Select(m => GenType(m)).ToArray());

      DAST.ResolvedTypeBase resolvedTypeBase;
      var attributes = topLevel.Attributes;

      if (topLevel is NewtypeDecl newType) {
        var range = NativeTypeToNewtypeRange(newType, false);
        var newtypeBase = newType.RhsWithArgument(typeArgs);
        resolvedTypeBase = (DAST.ResolvedTypeBase)DAST.ResolvedTypeBase.create_Newtype(
          GenType(newtypeBase), range, erasedIfNewtype);
      } else if (topLevel is TypeSynonymDecl typeSynonym) { // Also SubsetTypeDecl
        resolvedTypeBase = (DAST.ResolvedTypeBase)DAST.ResolvedTypeBase.create_SynonymType(
          GenType(typeSynonym.RhsWithArgument(typeArgs)));
      } else if (topLevel is TraitDecl traitDecl) {
        var traitType = traitDecl.IsReferenceTypeDecl
          ? TraitType.create_ObjectTrait()
          : TraitType.create_GeneralTrait();
        resolvedTypeBase = (DAST.ResolvedTypeBase)DAST.ResolvedTypeBase.create_Trait(traitType);
      } else if (topLevel is DatatypeDecl dd) {
        var infos = GenTypeParameterInfos(dd.TypeArgs);
        var equalitySupport = GenEqualitySupport(dd);
        resolvedTypeBase = (DAST.ResolvedTypeBase)DAST.ResolvedTypeBase.create_Datatype(
          equalitySupport, infos);
      } else if (topLevel is ClassDecl) {
        resolvedTypeBase = (DAST.ResolvedTypeBase)DAST.ResolvedTypeBase.create_Class();
      } else if (topLevel is AbstractTypeDecl atd) {
        resolvedTypeBase = (DAST.ResolvedTypeBase)DAST.ResolvedTypeBase.create_Datatype(GenEqualitySupport(topLevel), GenTypeParameterInfos(topLevel.TypeArgs));
        attributes = new Attributes("rust_rc", [Expression.CreateBoolLiteral(Token.NoToken, false)], attributes);
      } else {
        // SubsetTypeDecl are covered by TypeSynonymDecl
        throw new InvalidOperationException(topLevel.GetType().ToString());
      }
      var resolvedType = (DAST.ResolvedType)DAST.ResolvedType.create_ResolvedType(
        path, seqTypeArgs, resolvedTypeBase, ParseAttributes(attributes), seqProperMethods, seqExtendTraits);

      DAST.Type baseType = (DAST.Type)DAST.Type.create_UserDefined(resolvedType);

      return baseType;
    }

    private static _IEqualitySupport GenEqualitySupport(Declaration decl) {
      Contract.Requires(decl is IndDatatypeDecl or NewtypeDecl);
      IndDatatypeDecl.ES equalitySupport =
        decl is IndDatatypeDecl indDecl ? indDecl.EqualitySupport :
        decl is NewtypeDecl nt ? nt.EqualitySupport :
        decl is AbstractTypeDecl atd ?
          atd.Characteristics.EqualitySupport switch {
            TypeParameter.EqualitySupportValue.Required => IndDatatypeDecl.ES.ConsultTypeArguments,
            TypeParameter.EqualitySupportValue.InferredRequired => IndDatatypeDecl.ES.ConsultTypeArguments,
            TypeParameter.EqualitySupportValue.Unspecified => IndDatatypeDecl.ES.Never,
            _ => throw new ArgumentOutOfRangeException()
          }
        :
        IndDatatypeDecl.ES.Never;

      return equalitySupport switch {
        IndDatatypeDecl.ES.Never => EqualitySupport.create_Never(),
        IndDatatypeDecl.ES.ConsultTypeArguments => EqualitySupport.create_ConsultTypeArguments(),
        _ => throw new InvalidOperationException()
      };
    }

    private static Type EraseNewtypeLayers(TopLevelDecl topLevel) {
      var topLevelType = UserDefinedType.FromTopLevelDecl(topLevel.Origin, topLevel);
      return topLevelType.NormalizeToAncestorType();
    }

    // Contrary to other backends, we don't necessarily erase newtypes
    public override Type GetRuntimeType(Type tpe) {
      if (tpe.AsNewtype is { } newtypeDecl && !IsNewtypeErased(newtypeDecl)) {
        return tpe;
      }
      return base.GetRuntimeType(tpe);
    }

    public override ConcreteSyntaxTree Expr(Expression expr, bool inLetExprBody, ConcreteSyntaxTree wStmts) {
      if (currentBuilder is ExprContainer container) {
        EmitExpr(expr, inLetExprBody, new BuilderSyntaxTree<ExprContainer>(container, this), wStmts);
        return new BuilderSyntaxTree<ExprContainer>(new ExprBuffer(null), this);
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
      if (
        actualWr is BuilderSyntaxTree<ExprContainer> { Builder: IfElseBuilder { Condition: null } or WhileBuilder { Condition: null } } builder &&
        expr.Type is not BoolType) {
        actualWr = EmitConversion(builder, expr.Type, new BoolType());
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
        List<_System._ITuple2<ISequence<Rune>, DAST.Expression>> namedContents = [];

        int argI = 0;
        for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
          var destructor = dtv.Ctor.Destructors[i];
          if (destructor.IsGhost) {
            continue;
          }

          var actual = contents[argI];
          var formal = dtv.Ctor.Formals[i];
          var destructorName = GetDestructorFormalName(formal);
          namedContents.Add(_System.Tuple2<ISequence<Rune>, DAST.Expression>.create(
            Sequence<Rune>.UnicodeFromString(destructorName),
            actual
          ));

          argI++;
        }

        if (argI != contents.Count) {
          var error = "Datatype constructor "
                + dtv.Ctor.Name + " expects " + dtv.Ctor.Formals.Count + " arguments, but "
                + contents.Count + " were provided";
          if (emitUncompilableCode) {
            contents.Insert(0,
              ExprContainer.UnsupportedToExpr(
                error));
            builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Tuple(
              Sequence<DAST.Expression>.FromArray(contents.ToArray())
              ));
            return;
          }
          throw new InvalidOperationException(error);
        }

        if (dtv.Ctor.EnclosingDatatype is TupleTypeDecl tupleDecl) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Tuple(
            Sequence<DAST.Expression>.FromArray(namedContents.Select(x => x.dtor__1).ToArray())
          ));
        } else {
          var dtPath = PathFromTopLevel(dtv.Ctor.EnclosingDatatype);
          var dtTypeArgs = Sequence<DAST.Type>.FromArray(dtv.InferredTypeArgs.Select(m => GenType(m)).ToArray());
          var dType = GenType(dtv.Type);
          if (!dType.is_UserDefined) {
            throw new InvalidOperationException("Did not expected a non-user defined type for database values");
          }

          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_DatatypeValue(
            dType.dtor_resolved,
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

    private static string GetDestructorFormalName(Formal formal) {
      var defaultName = formal.CompileName;
      object externVal = null;
      bool hasExternVal = Attributes.ContainsMatchingValue(formal.Attributes, "extern",
        ref externVal, new HashSet<Attributes.MatchingValueOption> {
          Attributes.MatchingValueOption.String
        }, s => throw new UnsupportedInvalidOperationException(formal.Origin, "Non-string externs for destructors"));
      var destructorName = externVal as string ?? defaultName;
      return destructorName;
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
        case SpecialField.ID.ArrayLengthInt:
          break;
        case SpecialField.ID.Keys:
          break;
        case SpecialField.ID.Values:
          break;
        case SpecialField.ID.Items:
          break;
        default:
          AddUnsupported(receiverType.Origin, "<i>Special field: " + id + "</i>");
          break;
      }
    }

    _ISelectContext GetSelectContext(TopLevelDecl decl) {
      return decl is DatatypeDecl or NewtypeDecl ? SelectContext.create_SelectContextDatatype() :
        decl is TraitDecl { IsReferenceTypeDecl: false } ?
      SelectContext.create_SelectContextGeneralTrait() :
      SelectContext.create_SelectContextClassOrObjectTrait();
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
            int.Parse(dtor.CorrespondingFormals[0].NameForCompilation), GenType(expectedType)
          ), null, this);
        } else {
          var attributes = member.Attributes ??
                           (dtor.CorrespondingFormals.Count == 1 ? dtor.CorrespondingFormals[0].Attributes : null);
          var compileName = GetExtractOverrideName(attributes, member.GetCompileName(Options));
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(compileName),
            FieldMutabilityOf(member),
            GetSelectContext(member.EnclosingClass), GenType(expectedType)
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member is ConstantField
          ), this);
        }
      } else if (member is SpecialField { SpecialId: SpecialField.ID.ArrayLength } arraySpecial) {
        obj(EmitCoercionIfNecessary(
            objType,
            objType.IsNonNullRefType || !objType.IsRefType ? null : UserDefinedType.CreateNonNullType((UserDefinedType)objType.NormalizeExpand()),
          null, new BuilderSyntaxTree<ExprContainer>(objReceiver, this)
        ));
        var objExpr = objReceiver.Finish();

        return new ExprLvalue((DAST.Expression)DAST.Expression.create_ArrayLen(
          objExpr,
          GenType(objType),
          arraySpecial.IdParam != null ? ((int)arraySpecial.IdParam) : 0,
          false
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
      } else if (member is SpecialField { SpecialId: SpecialField.ID.Items }) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_MapItems(
          objExpr), null, this);
      } else if (member is SpecialField sf && sf.SpecialId != SpecialField.ID.UseIdParam) {
        obj(new BuilderSyntaxTree<ExprContainer>(objReceiver, this));
        var objExpr = objReceiver.Finish();

        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, objType, out var compiledName, out _, out _);
        return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(compiledName),
          FieldMutabilityOf(member),
          GetSelectContext(member.EnclosingClass), GenType(expectedType)
        ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
          objExpr,
          Sequence<Rune>.UnicodeFromString(compiledName),
          member is ConstantField
        ), this);
      } else if (member is DatatypeDiscriminator discriminator && discriminator.IdParam is string fieldName && fieldName.StartsWith("is_")) {
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
            member.IsInstanceIndependentConstant,
            Sequence<DAST.Type>.FromElements(expectedType.AsArrowType.Args.Select(GenType).ToArray())
          ), null, this);
        } else if (internalAccess && (member is ConstantField || member.EnclosingClass is TraitDecl)) {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(InternalFieldPrefix + member.GetCompileName(Options)),
            FieldMutabilityOf(member, isInternal: true),
            GetSelectContext(member.EnclosingClass), GenType(expectedType)
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(InternalFieldPrefix + member.GetCompileName(Options)),
            member is ConstantField
          ), this);
        } else {
          return new ExprLvalue((DAST.Expression)DAST.Expression.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            FieldMutabilityOf(member),
            GetSelectContext(member.EnclosingClass), GenType(expectedType)
          ), (DAST.AssignLhs)DAST.AssignLhs.create_Select(
            objExpr,
            Sequence<Rune>.UnicodeFromString(member.GetCompileName(Options)),
            member is ConstantField
          ), this);
        }
      }
    }

    private static _IFieldMutability FieldMutabilityOf(MemberDecl member, bool isInternal = false) {
      return member is ConstantField or DatatypeDestructor
          ? isInternal || member is DatatypeDestructor
            ? new FieldMutability_InternalClassConstantFieldOrDatatypeDestructor()
            : new FieldMutability_ConstantField()
          : new FieldMutability_ClassMutableField();
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

      DAST._ICollKind collKind;
      Type indexType;
      if (source.Type.IsArrayType) {
        collKind = DAST.CollKind.create_Array();
        indexType = Type.Int;
      } else if (source.Type.NormalizeToAncestorType() is { IsMapType: true } normalized) {
        collKind = DAST.CollKind.create_Map();
        indexType = normalized.AsMapType.Domain;
      } else if (source.Type.NormalizeToAncestorType() is { AsMultiSetType: { } msType }) {
        collKind = DAST.CollKind.create_Map();
        indexType = msType.Arg;
      } else {
        collKind = DAST.CollKind.create_Seq();
        indexType = Type.Int;
      }

      var indexBuf = new ExprBuffer(null);
      var indexWr = EmitCoercionIfNecessary(index.Type.NormalizeExpand(), indexType, source.Origin, new BuilderSyntaxTree<ExprContainer>(indexBuf, this));
      EmitExpr(index, inLetExprBody, indexWr, wStmts);

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
        builder = b;
        if (wStmts is BuilderSyntaxTree<StatementContainer> s) {
          converter = (Expression expr) => ConvertExpression(expr, s);
        } else {
          var statementBuf = new NoStatementBuffer();
          var sNoStmt = new BuilderSyntaxTree<StatementContainer>(statementBuf, this);
          converter = (Expression expr) => ConvertExpression(expr, sNoStmt);
        }

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
            convert(source), convert(index), convert(value), GenType(resultCollectionType), GenType(source.Type)
          ));
        } else if (resultCollectionType.AsMapType is { }) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_MapUpdate(
            convert(source), convert(index), convert(value), GenType(resultCollectionType), GenType(source.Type)
          ));
        } else {
          AddUnsupported(source.Origin, "<i>EmitIndexCollectionUpdate for " + resultCollectionType.ToString() + "</i>");
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
        var loWr = EmitCoercionIfNecessary(lo.Type.NormalizeExpand(), Type.Int, source.Origin, new BuilderSyntaxTree<ExprContainer>(loBuf, this));
        EmitExpr(lo, inLetExprBody, loWr, wStmts);
        loExpr = loBuf.Finish();
      }

      DAST.Expression hiExpr = null;
      if (hi != null) {
        var hiBuf = new ExprBuffer(null);
        var loWr = EmitCoercionIfNecessary(hi.Type.NormalizeExpand(), Type.Int, source.Origin, new BuilderSyntaxTree<ExprContainer>(hiBuf, this));
        EmitExpr(hi, inLetExprBody, loWr, wStmts);
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
          size = new ConversionExpr(expr.N.Origin, size, new IntType());
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
        AddUnsupportedFeature(expr.Origin, Feature.Multisets);
      }
    }

    protected override void EmitApplyExpr(Type functionType, IOrigin tok, Expression function,
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
      List<Type> boundTypes, Type resultType, IOrigin resultTok, bool inLetExprBody, ConcreteSyntaxTree wr,
      ref ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var argsAST = arguments.Select((t, i) =>
          (_System.Tuple2<DAST.Formal, DAST.Expression>)
          _System.Tuple2<DAST.Formal, DAST.Expression>.create(
            (DAST.Formal)DAST.Formal.create_Formal(Sequence<Rune>.UnicodeFromString(boundVars[i]),
              GenType(boundTypes[i]), ParseAttributes(null)), convert(t))).ToList();

        var retType = GenType(resultType);

        return new BuilderSyntaxTree<ExprContainer>(builder.Builder.BetaRedex(
          argsAST, retType
        ), this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitDestructor(Action<ConcreteSyntaxTree> source, Formal dtor, int formalNonGhostIndex,
      DatatypeCtor ctor,
      Func<List<Type>> getTypeArgs, Type bvType, ConcreteSyntaxTree wr) {
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
              int.Parse(dtor.NameForCompilation), GenType(dtor.Type)
            ));
          } else {
            var compileName = GetExtractOverrideName(dtor.Attributes, dtor.GetOrCreateCompileName(currentIdGenerator));
            builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Select(
              sourceAST,
              Sequence<Rune>.UnicodeFromString(compileName),
              new FieldMutability_InternalClassConstantFieldOrDatatypeDestructor(),
              GetSelectContext(ctor.EnclosingDatatype), GenType(dtor.Type)
            ));
          }
        }
      }
    }

    private static string GetExtractOverrideName(Attributes attributes, string defaultValue) {
      return ((Attributes.Find(attributes, "extern_extract") is { } extern_extract
               && extern_extract.Args.Count() == 1 && extern_extract.Args[0] is LiteralExpr { Value: string overrideName }
        ? overrideName : defaultValue));
    }

    protected override ConcreteSyntaxTree CreateLambda(List<Type> inTypes, IOrigin tok, List<string> inNames,
        Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts, bool untyped = false) {
      if (GetExprBuilder(wr, out var builder)) {
        var formals = new List<DAST.Formal>();
        for (int i = 0; i < inTypes.Count; ++i) {
          formals.Add((DAST.Formal)DAST.Formal.create_Formal(
            Sequence<Rune>.UnicodeFromString(inNames[i]),
            GenType(inTypes[i]), ParseAttributes(null)
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

    protected override ConcreteSyntaxTree EmitCallToIsMethod(RedirectingTypeDecl declWithConstraints, Type type, ConcreteSyntaxTree wr) {
      if (!GetExprBuilder(wr, out var builder)) {
        throw new InvalidOperationException();
      }

      if (declWithConstraints is SubsetTypeDecl subsetTypeDecl) {
        // Since this type becomes a type synonym at run-time, we simply inline the condition
        // We put it as a IIFE
        var constraint = subsetTypeDecl.Constraint;

        var statementBuf = new NoStatementBuffer();
        ConcreteSyntaxTree sNoStmt = new BuilderSyntaxTree<StatementContainer>(statementBuf, this);
        CreateIIFE(GetCompileNameNotProtected(subsetTypeDecl.Var), subsetTypeDecl.Var.Type, subsetTypeDecl.Var.Origin,
        Type.Bool, constraint.Origin, wr, ref sNoStmt, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody);
        if (!GetExprBuilder(wrBody, out var wrBodyBuilder)) {
          throw new InvalidOperationException();
        }
        wrBodyBuilder.Builder.AddExpr(ConvertExpression(constraint, sNoStmt));
        return wrRhs;
      }

      var parameters = Sequence<_IFormal>.FromArray([
        new DAST.Formal(Sequence<Rune>.UnicodeFromString("_dummy_"), GenType(type), Sequence<DAST.Attribute>.Empty)
      ]);
      var signature = CreateSignature(parameters);
      var c = builder.Builder.Call(signature);
      c.SetName((DAST.CallName)DAST.CallName.create_CallName(Sequence<Rune>.UnicodeFromString("is"),
        Option<_IType>.create_None(), Option<_IFormal>.create_None(), false, signature));
      var wrc = new BuilderSyntaxTree<ExprContainer>(c, this);
      EmitTypeName_Companion(type, wrc,
        wr, declWithConstraints.Tok, null);
      return wrc;
    }

    protected override ConcreteSyntaxTree EmitAnd(Action<ConcreteSyntaxTree> lhs, ConcreteSyntaxTree wr) {
      if (GetExprBuilder(wr, out var builder)) {
        var boolType = (DAST.Type)DAST.Type.create_Primitive(Primitive.create_Bool());
        var binOp = builder.Builder.BinOp((DAST.BinOp)DAST.BinOp.create_And(), boolType, boolType, boolType);
        lhs(new BuilderSyntaxTree<ExprContainer>(binOp, this));

        return new BuilderSyntaxTree<ExprContainer>(binOp, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitArrayIndexToInt(ConcreteSyntaxTree wr, out ConcreteSyntaxTree wIndex) {
      if (GetExprBuilder(wr, out var builder)) {
        var binOp = builder.Builder.Wrapper((DAST.Expression nativeArrayIndex) =>
          (DAST.Expression)DAST.Expression.create_ArrayIndexToInt(nativeArrayIndex));
        wIndex = new BuilderSyntaxTree<ExprContainer>(binOp, this);
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitArrayFinalize(ConcreteSyntaxTree wr, out ConcreteSyntaxTree wrArray, Type type) {
      if (GetExprBuilder(wr, out var builder)) {
        var binOp = builder.Builder.Wrapper((DAST.Expression arrayPointer) =>
          (DAST.Expression)DAST.Expression.create_FinalizeNewArray(arrayPointer, GenType(type)));
        wrArray = new BuilderSyntaxTree<ExprContainer>(binOp, this);
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
      AddUnsupported(Token.NoToken, "<i>EmitCharBoundedPool</i>");
    }

    protected override void EmitWiggleWaggleBoundedPool(bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported(Token.NoToken, "<i>EmitWiggleWaggleBoundedPool</i>");
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
      if (GetExprConverter(wr, wStmts, out var exprBuilder, out var convert)) {
        exprBuilder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_MultisetBoundedPool(
          convert(of), includeDuplicates
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitSubSetBoundedPool(Expression of, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupported(of.Origin, "<i>EmitSubSetBoundedPool</i>");
    }

    protected override void EmitMapBoundedPool(Expression map, string propertySuffix, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var exprBuilder, out var convert)) {
        exprBuilder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_MapBoundedPool(
          convert(map)
        ));
      } else {
        throw new InvalidOperationException();
      }
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
      if (GetExprConverter(wr, wStmts, out var exprBuilder, out var convert)) {
        if (bv.Type.IsDatatype && bv.Type.AsDatatype is { } datatypeDecl) {

          var parameters = Sequence<_IFormal>.FromArray([]);
          var signature = CreateSignature(parameters);
          var c = exprBuilder.Builder.Call(signature);
          c.SetName((DAST.CallName)DAST.CallName.create_CallName(Sequence<Rune>.UnicodeFromString("_AllSingletonConstructors"),
            Option<_IType>.create_None(), Option<_IFormal>.create_None(), false, signature));
          var wrc = new BuilderSyntaxTree<ExprContainer>(c, this);
          EmitTypeName_Companion(bv.Type, wrc, wr, bv.Origin, null);
        } else {
          throw new InvalidOperationException("Datatype Bounded pool on non-datatype value");
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void CreateIIFE(string bvName, Type bvType, IOrigin bvTok, Type bodyType, IOrigin bodyTok,
      ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts, out ConcreteSyntaxTree wrRhs, out ConcreteSyntaxTree wrBody) {
      if (GetExprBuilder(wr, out var builder)) {
        var iife = builder.Builder.IIFE(bvName, GenType(bvType));
        wrRhs = new BuilderSyntaxTree<ExprContainer>(iife.RhsBuilder(), this);
        wrBody = new BuilderSyntaxTree<ExprContainer>(iife, this);
      } else {
        throw new InvalidOperationException("Invalid context for IIFE: " + wr.GetType());
      }
    }

    protected override ConcreteSyntaxTree CreateIIFE0(Type resultType, IOrigin resultTok, ConcreteSyntaxTree wr,
        ConcreteSyntaxTree wStmts) {
      EmitLambdaApply(wr, out var wLambda, out var wArg);
      return CreateLambda([], null, [], resultType, wLambda, wStmts);
    }

    protected override ConcreteSyntaxTree CreateIIFE1(int source, Type resultType, IOrigin resultTok, string bvName,
        ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      EmitLambdaApply(wr, out var wLambda, out var wArg);
      var ret = CreateLambda([Type.Int], null, [bvName], resultType, wLambda, wStmts);
      EmitLiteralExpr(wArg, new LiteralExpr(null, source) {
        Type = Type.Int
      });
      return ret;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var container, out var convert)) {
        var dastExpr = convert(expr);
        switch (op) {
          case ResolvedUnaryOp.BoolNot: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_Not(),
                dastExpr,
                new UnaryOpFormat_NoFormat()
              ));
              break;
            }
          case ResolvedUnaryOp.BitwiseNot: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_BitwiseNot(),
                dastExpr,
                new UnaryOpFormat_NoFormat()
              ));
              break;
            }
          case ResolvedUnaryOp.Cardinality: {
              container.Builder.AddExpr((DAST.Expression)DAST.Expression.create_UnOp(
                UnaryOp.create_Cardinality(),
                dastExpr,
                new UnaryOpFormat_NoFormat()
              ));
              break;
            }
        }
      } else {
        AddUnsupported(expr.Origin, "<i>UnaryExpr " + op + " without expr container</i>");
      }
    }

    // A few helpers to reduce the size of expressions
    private static DAST.Expression Not(_IExpression expr, bool mergeInner = true) {
      return (DAST.Expression)DAST.Expression.create_UnOp(
        new UnaryOp_Not(),
        (DAST.Expression)expr,
        mergeInner ? new UnaryOpFormat_CombineFormat() : new UnaryOpFormat_NoFormat());
    }

    private static DAST.Expression BinaryOp(_ITypedBinOp typedOp, _IExpression left, _IExpression right, _IBinaryOpFormat format = null) {
      format ??= new BinaryOpFormat_NoFormat();

      return (DAST.Expression)DAST.Expression.create_BinOp(typedOp, left, right, format
      );
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op,
      Type e0Type, Type e1Type, IOrigin tok, Type resultType,
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
        var overflows = e0Type is BitvectorType;

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
          BinaryExpr.ResolvedOpcode.NeqCommon => "!=",
          _ => null
        };

        var typeLeft = GenType(e0Type);
        var typeRight = GenType(e1Type);
        var typeResult = GenType(resultType);

        object B(_IBinOp binOp) {
          return builder.Builder.BinOp((DAST.BinOp)binOp, typeLeft, typeRight, typeResult);
        }

        var opStringClosure = opString;
        object C(System.Func<DAST.Expression, DAST.Expression, DAST.Expression> callback) {
          return builder.Builder.BinOp(opStringClosure, callback);
        }

        TypedBinOp TypeOp(_IBinOp binOp) {
          return (TypedBinOp)TypedBinOp.create_TypedBinOp(binOp, typeLeft, typeRight, typeResult);
        }

        TypedBinOp TypeOpRev(_IBinOp binOp) {
          return (TypedBinOp)TypedBinOp.create_TypedBinOp(binOp, typeRight, typeLeft, typeResult);
        }

        var newBuilder = op switch {
          BinaryExpr.ResolvedOpcode.EqCommon => B((BinOp)BinOp.create_Eq(
            e0Type.IsRefType
          )),
          BinaryExpr.ResolvedOpcode.SetEq => B((BinOp)BinOp.create_Eq(false)),
          BinaryExpr.ResolvedOpcode.MapEq => B((BinOp)BinOp.create_Eq(false)),
          BinaryExpr.ResolvedOpcode.SeqEq => B((BinOp)BinOp.create_Eq(false)),
          BinaryExpr.ResolvedOpcode.MultiSetEq => B((BinOp)BinOp.create_Eq(false)),
          BinaryExpr.ResolvedOpcode.NeqCommon => C((left, right) =>
            Not(BinaryOp(
              TypeOp(BinOp.create_Eq(
                e0Type.IsRefType
              )), left, right))),
          BinaryExpr.ResolvedOpcode.SetNeq => C((left, right) =>
            Not(BinaryOp(TypeOp(BinOp.create_Eq(false)), left, right))),
          BinaryExpr.ResolvedOpcode.SeqNeq => C((left, right) =>
            Not(BinaryOp(TypeOp(BinOp.create_Eq(false)), left, right))),
          BinaryExpr.ResolvedOpcode.MapNeq => C((left, right) =>
            Not(BinaryOp(TypeOp(BinOp.create_Eq(false)), left, right))),
          BinaryExpr.ResolvedOpcode.MultiSetNeq => C((left, right) =>
            Not(BinaryOp(TypeOp(BinOp.create_Eq(false)), left, right))),

          BinaryExpr.ResolvedOpcode.Div =>
            B(NeedsEuclideanDivision(resultType) ? BinOp.create_EuclidianDiv() : BinOp.create_Div(overflows)),
          BinaryExpr.ResolvedOpcode.Mod =>
            B(NeedsEuclideanDivision(resultType) ? BinOp.create_EuclidianMod() : BinOp.create_Mod()),
          BinaryExpr.ResolvedOpcode.Imp =>
            C((left, right) =>
              BinaryOp(
                TypeOp(DAST.BinOp.create_Or()),
                Not(left, false), right, new BinaryOpFormat_ImpliesFormat()
              )),
          BinaryExpr.ResolvedOpcode.Iff =>
            C((left, right) =>
              BinaryOp(
                TypeOp(BinOp.create_Eq(false)),
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
              BinaryOp(TypeOpRev(new BinOp_Subset()), right, left,
                new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.ProperSuperset =>
            C((left, right) =>
              BinaryOp(TypeOpRev(new BinOp_ProperSubset()), right, left,
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
              BinaryOp(TypeOpRev(new BinOp_Submultiset()), right, left,
                new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.ProperMultiSuperset =>
            C((left, right) =>
              BinaryOp(TypeOpRev(new BinOp_ProperSubmultiset()), right, left,
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
              Not(BinaryOp(TypeOp(new BinOp_In()), left, right))),
          BinaryExpr.ResolvedOpcode.NotInSet =>
            C((left, right) =>
              Not(BinaryOp(TypeOp(new BinOp_In()), left, right))),
          BinaryExpr.ResolvedOpcode.NotInSeq =>
            C((left, right) =>
              Not(BinaryOp(TypeOp(new BinOp_In()), left, right))),
          BinaryExpr.ResolvedOpcode.NotInMultiSet =>
            C((left, right) =>
              Not(BinaryOp(TypeOp(new BinOp_In()), left, right))),
          BinaryExpr.ResolvedOpcode.Concat => B(BinOp.create_Concat()),
          BinaryExpr.ResolvedOpcode.And => B(BinOp.create_And()),
          BinaryExpr.ResolvedOpcode.Or => B(BinOp.create_Or()),
          BinaryExpr.ResolvedOpcode.Add => B(BinOp.create_Plus(overflows)),
          BinaryExpr.ResolvedOpcode.Sub => B(BinOp.create_Minus(overflows)),
          BinaryExpr.ResolvedOpcode.Mul => B(BinOp.create_Times(overflows)),
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
              Not(BinaryOp(TypeOpRev(new BinOp_Lt()), right, left,
                new BinaryOpFormat_ReverseFormat()))),
          BinaryExpr.ResolvedOpcode.LeChar =>
            C((left, right) =>
              Not(BinaryOp(TypeOpRev(new BinOp_LtChar()), right, left,
                new BinaryOpFormat_ReverseFormat()))),
          BinaryExpr.ResolvedOpcode.Gt =>
            C((left, right) =>
              BinaryOp(TypeOpRev(new BinOp_Lt()), right, left, new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.GtChar =>
            C((left, right) =>
              BinaryOp(TypeOpRev(new BinOp_LtChar()), right, left, new BinaryOpFormat_ReverseFormat())),
          BinaryExpr.ResolvedOpcode.Ge =>
            C((left, right) =>
              Not(BinaryOp(TypeOp(new BinOp_Lt()), left, right))),
          BinaryExpr.ResolvedOpcode.GeChar =>
            C((left, right) =>
              Not(BinaryOp(TypeOp(new BinOp_LtChar()), left, right))),

          _ => B(DAST.BinOp.create_Passthrough(Sequence<Rune>.UnicodeFromString($"<b>Unsupported: <i>Operator {op}</i></b>"))),
        };

        opString = "";

        currentBuilder = newBuilder;
        // cleaned up by EmitExpr
      } else {
        throw new InvalidOperationException();
      }
    }

    public BuilderSyntaxTree<ExprContainer> WrBuffer(out ExprBuffer buf) {
      buf = new ExprBuffer(null);
      var wGuard = new BuilderSyntaxTree<ExprContainer>(buf, this);
      return wGuard;
    }
    protected override void EmitITE(Expression guard, Expression thn, Expression els, Type resultType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        DAST.Expression convertedGuard;
        if (guard.Type is BoolType) {
          if (guard is UnaryOpExpr { ResolvedOp: UnaryOpExpr.ResolvedOpcode.BoolNot, E: var innerGuard } unaryOpExpr && innerGuard.Type is not BoolType) {
            guard = unaryOpExpr.E;
          }
          convertedGuard = convert(guard);
        } else {
          EmitConversionExpr(guard, guard.Type, new BoolType(), inLetExprBody, WrBuffer(out var buf), wStmts);
          convertedGuard = buf.Finish();
        }
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Ite(
          convertedGuard,
          convert(thn),
          convert(els)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitIsZero(string varName, ConcreteSyntaxTree wr) {
      AddUnsupported(Token.NoToken, "<i>EmitIsZero</i>");
    }

    protected override void EmitConversionExpr(Expression fromExpr, Type fromType, Type toType, bool inLetExprBody, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprBuilder(wr, out var builder)) {
        if (toType.Equals(fromType)) {
          EmitExpr(fromExpr, inLetExprBody, builder, wStmts);
        } else {
          EmitExpr(fromExpr, inLetExprBody, EmitConversion(builder, fromType, toType), wStmts);
        }
      } else {
        throw new InvalidOperationException();
      }
    }

    private BuilderSyntaxTree<ExprContainer> EmitConversion(BuilderSyntaxTree<ExprContainer> builder, Type fromType, Type toType) {
      return new BuilderSyntaxTree<ExprContainer>(builder.Builder.Convert(
        GenType(fromType),
        GenType(toType)
      ), this);
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

    protected override void EmitTypeTest(string localName, Type fromType, Type toType, IOrigin tok, ConcreteSyntaxTree wr) {
      // This method needs to be implemented, but because we override EmitTypeTestExpr, it's never going to be called Still, we leave the body for completeness and maintenance. 
      if (GetExprBuilder(wr, out var builder)) {
        EmitTypeTestDAST(fromType, toType, builder,
          (DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(localName)));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitTypeTestExpr(Expression expr, Type fromType, Type toType, IOrigin tok,
      bool inLetExprBody, ConcreteSyntaxTree wr, ref ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var exprDAST = convert(expr);
        EmitTypeTestDAST(fromType, toType, builder, exprDAST);
      } else {
        throw new InvalidOperationException();//TODO
      }
    }

    private void EmitTypeTestDAST(Type fromType, Type toType, BuilderSyntaxTree<ExprContainer> builder, DAST.Expression exprDAST) {
      builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_Is(
        exprDAST,
        GenType(fromType),
        GenType(toType)
      ));
    }

    protected override void EmitIsIntegerTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupportedFeature(source.Origin, Feature.TypeTests);
    }

    protected override void EmitIsUnicodeScalarValueTest(Expression source, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupportedFeature(source.Origin, Feature.TypeTests);
    }

    protected override void EmitIsInIntegerRange(Expression source, BigInteger lo, BigInteger hi, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      AddUnsupportedFeature(source.Origin, Feature.TypeTests);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, IOrigin tok, List<Expression> elements,
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

    protected override void EmitMapDisplay(MapType mt, IOrigin tok, List<MapDisplayEntry> elements, bool inLetExprBody,
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
          Sequence<_System.Tuple2<DAST.Expression, DAST.Expression>>.FromArray(elementsAST.ToArray()),
          GenType(mt.Domain), GenType(mt.Range)
        ));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void EmitSetBuilder_New(ConcreteSyntaxTree wr, SetComprehension e, string collectionName) {
      if (GetStatementBuilder(wr, out var builder)) {
        var eType = e.Type.AsSetType;
        if (eType == null) {// dafny0/GeneralNewtypeCollections
          AddUnsupportedFeature(e.Origin, Feature.NonNativeNewtypes);
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
        throw new InvalidOperationException();
      }
    }

    protected override void EmitMapBuilder_New(ConcreteSyntaxTree wr, MapComprehension e, string collectionName) {
      if (GetStatementBuilder(wr, out var builder)) {
        var eType = e.Type.AsMapType;
        var keyType = GenType(eType.Domain);
        var valueType = GenType(eType.Range);
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
        AddUnsupported(e.Origin, "<i>EmitMapBuilder_New (non-statement)</i>");
      }
      //throw new InvalidOperationException();
    }

    protected override void EmitSetBuilder_Add(CollectionType ct, string collName, Expression elmt, bool inLetExprBody,
        ConcreteSyntaxTree wr) {
      if (GetStatementBuilder(wr, out var builder)) {
        var stmtBuilder = new CallStmtBuilder(CreateSignature(Sequence<_IFormal>.Empty));
        stmtBuilder.SetName((DAST.CallName)DAST.CallName.create_SetBuilderAdd());
        stmtBuilder.SetTypeArgs([]);
        stmtBuilder.SetOuts([]); ;
        stmtBuilder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(collName)));
        stmtBuilder.AddExpr(ConvertExpression(elmt, builder));
        builder.Builder.AddBuildable(stmtBuilder);
      } else {
        AddUnsupported(elmt.Origin, "<i>EmitSetBuilder_Add</i>");
      }
      //throw new InvalidOperationException();
    }

    private static _ICallSignature CreateSignature(ISequence<_IFormal> params_) {
      return CallSignature.create_CallSignature(params_, params_);
    }

    // Normally wStmt is a BuilderSyntaxTree<StatementContainer> but it might not while the compiler is being developed
    private DAST.Expression ConvertExpression(Expression term, ConcreteSyntaxTree wStmt) {
      EmitExpr(term, false, WrBuffer(out var buffer0), wStmt);
      return buffer0.Finish();
    }

    private DAST.Expression ConvertExpressionNoStatement(Expression term) {
      var statementBuf = new NoStatementBuffer();
      var sNoStmt = new BuilderSyntaxTree<StatementContainer>(statementBuf, this);
      return ConvertExpression(term, sNoStmt);
    }

    private BuilderSyntaxTree<ExprContainer> CreateExprBuilder() {
      return WrBuffer(out _);
    }

    protected override ConcreteSyntaxTree EmitMapBuilder_Add(MapType mt, IOrigin tok, string collName, Expression term,
        bool inLetExprBody, ConcreteSyntaxTree wr) {
      if (GetStatementBuilder(wr, out var builder)) {
        var stmtBuilder = new CallStmtBuilder(CreateSignature(Sequence<_IFormal>.Empty));
        stmtBuilder.SetName((DAST.CallName)DAST.CallName.create_MapBuilderAdd());
        stmtBuilder.SetTypeArgs([]);
        stmtBuilder.SetOuts([]); ;
        stmtBuilder.AddExpr((DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(collName)));
        var keyBuilder = CreateExprBuilder();
        stmtBuilder.AddBuildable((ExprBuffer)keyBuilder.Builder);
        stmtBuilder.AddExpr(ConvertExpression(term, builder));
        builder.Builder.AddBuildable(stmtBuilder);
        return keyBuilder;
      } else {
        AddUnsupported(tok, "<i>EMitMapBuilder_Add</i>");
        return WrBuffer(out _);
      }
    }

    protected override Action<ConcreteSyntaxTree> GetSubtypeCondition(string tmpVarName, Type boundVarType, IOrigin tok, ConcreteSyntaxTree wPreconditions) {
      Action<ConcreteSyntaxTree> typeTest;

      if (boundVarType.IsRefType) {
        DAST._IExpression baseExpr;
        if (boundVarType.IsObject || boundVarType.IsObjectQ) {
          baseExpr = DAST.Expression.create_Literal(DAST.Literal.create_BoolLiteral(true));
        } else {
          // typeTest = $"{tmpVarName} instanceof {TypeName(boundVarType, wPreconditions, tok)}";
          AddUnsupported(tok, "<i>TypeName</i>");
          return (ConcreteSyntaxTree w) => { };
        }

        if (boundVarType.IsNonNullRefType) {
          typeTest = wr => {
            if (GetExprBuilder(wr, out var builder)) {
              var boolType = DAST.Type.create_Primitive(Primitive.create_Bool());
              var tmpVarType = GenType(boundVarType);
              var tmpVarNotNull = DAST.Expression.create_UnOp(
                DAST.UnaryOp.create_Not(),
                DAST.Expression.create_BinOp(
                  TypedBinOp.create_TypedBinOp(DAST.BinOp.create_Eq(true), tmpVarType, tmpVarType, boolType),
                  DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(tmpVarName)),
                  DAST.Expression.create_Literal(DAST.Literal.create_Null(GenType(boundVarType))),
                  new BinaryOpFormat_NoFormat()), new UnaryOpFormat_CombineFormat());
              builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_BinOp(
                TypedBinOp.create_TypedBinOp(BinOp.create_And(), boolType, boolType, boolType),
                  tmpVarNotNull,
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
              var boolType = DAST.Type.create_Primitive(Primitive.create_Bool());
              var tmpVarType = GenType(boundVarType);
              builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_BinOp(
                TypedBinOp.create_TypedBinOp(BinOp.create_Or(), boolType, boolType, boolType),
                DAST.Expression.create_BinOp(
                  TypedBinOp.create_TypedBinOp(DAST.BinOp.create_Eq(true), tmpVarType, tmpVarType, boolType),
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

    protected override void GetCollectionBuilder_Build(CollectionType ct, IOrigin tok, string collName,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmt) {
      if (GetExprBuilder(wr, out var builder)) {
        var callExpr = new CallExprBuilder(CreateSignature(Sequence<_IFormal>.Empty));
        if (ct.IsMapType) {
          callExpr.SetName((DAST.CallName)DAST.CallName.create_MapBuilderBuild());
        } else {
          callExpr.SetName((DAST.CallName)DAST.CallName.create_SetBuilderBuild());
        }

        callExpr.SetTypeArgs([]);
        callExpr.SetOuts([]); ;
        callExpr.AddExpr((DAST.Expression)DAST.Expression.create_Ident(Sequence<Rune>.UnicodeFromString(collName)));
        builder.Builder.AddBuildable(callExpr);
      } else {
        AddUnsupported(tok, "<i>GetCollectionBuilder_Build</i>");
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
        wLo(WrBuffer(out var loBuf));
        wHi(WrBuffer(out var hiBuf));

        if (GetExprBuilder(wr, out var builder)) {
          builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_IntRange(
            GenType(result),
            loBuf.Finish(),
            hiBuf.Finish(),
            true
          ));
        } else {
          throw new InvalidOperationException();
        }
      }
      );
    }

    protected override void EmitNull(Type _, ConcreteSyntaxTree wr) {
      AddUnsupported(Token.NoToken, "<i>EmitNull</i>");
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type,
      ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts) {
      if (GetExprConverter(wr, wStmts, out var builder, out var convert)) {
        var eBuild = convert(e);
        builder.Builder.AddExpr((DAST.Expression)DAST.Expression.create_ExactBoundedPool(eBuild));
      } else {
        throw new InvalidOperationException();
      }
    }

    protected override void OrganizeModules(Program program, out List<ModuleDefinition> modules) {
      modules = program.CompileModules.ToList();
      modules.Sort((a, b) =>
        String.Compare(a.FullDafnyName, b.FullDafnyName, StringComparison.Ordinal));
    }

    protected override void EmitHaltRecoveryStmt(Statement body, string haltMessageVarName, Statement recoveryBody, ConcreteSyntaxTree wr) {
      TrStmt(body, wr);
    }

    protected override ConcreteSyntaxTree GetNullClassConcreteSyntaxTree() {
      return new BuilderSyntaxTree<StatementContainer>(new StatementBuffer(), this);
    }

    protected override void EmitNestedMatchExpr(NestedMatchExpr match, bool inLetExprBody, ConcreteSyntaxTree output,
      ConcreteSyntaxTree wStmts) {
      EmitExpr(match.Flattened, inLetExprBody, output, wStmts);
    }

    protected override void TrOptNestedMatchExpr(NestedMatchExpr match, Type resultType, ConcreteSyntaxTree wr, ConcreteSyntaxTree wStmts,
      bool inLetExprBody, IVariable accumulatorVar, OptimizedExpressionContinuation continuation) {
      TrExprOpt(match.Flattened, resultType, wr, wStmts, inLetExprBody, accumulatorVar, continuation);
    }

    protected override void EmitNestedMatchStmt(NestedMatchStmt match, ConcreteSyntaxTree writer) {
      TrStmt(match.Flattened, writer);
    }
  }
}
