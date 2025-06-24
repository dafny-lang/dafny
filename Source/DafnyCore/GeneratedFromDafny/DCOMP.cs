// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace DCOMP {


  public partial class COMP {
    public COMP() {
      this.error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default();
      this.optimizations = Dafny.Sequence<Func<RAST._IMod, RAST._IMod>>.Empty;
      this._rootType = Defs.RootType.Default();
      this._charType = Defs.CharType.Default();
      this._pointerType = Defs.PointerType.Default();
      this._syncType = Defs.SyncType.Default();
      this._rcDatatypeThis = RAST.Expr.Default();
      this._borrowedRcDatatypeThis = RAST.Expr.Default();
    }
    public RAST._IType Object(RAST._IType underlying) {
      if (((this).pointerType).is_Raw) {
        return RAST.__default.PtrType(underlying);
      } else {
        return RAST.__default.ObjectType(underlying);
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public Dafny.ISequence<Func<RAST._IMod, RAST._IMod>> optimizations {get; set;}
    public void __ctor(Defs._ICharType charType, Defs._IPointerType pointerType, Defs._IRootType rootType, Defs._ISyncType syncType)
    {
      (this)._charType = charType;
      (this)._pointerType = pointerType;
      (this)._rootType = rootType;
      (this)._syncType = syncType;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      (this).optimizations = Dafny.Sequence<Func<RAST._IMod, RAST._IMod>>.FromElements(ExpressionOptimization.__default.apply, FactorPathsOptimization.__default.apply((this).thisFile));
      RAST._IExpr _0_thisAsSelf;
      _0_thisAsSelf = Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>((this).rcNew)((RAST.__default.self).Clone());
      (this)._rcDatatypeThis = _0_thisAsSelf;
      (this)._borrowedRcDatatypeThis = RAST.__default.Borrow(_0_thisAsSelf);
    }
    public bool HasAttribute(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, Dafny.ISequence<Dafny.Rune>, bool>>((_0_attributes, _1_name) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_0_attributes).UniqueElements, false, (((_exists_var_0) => {
        DAST._IAttribute _2_attribute = (DAST._IAttribute)_exists_var_0;
        return ((_0_attributes).Contains(_2_attribute)) && ((((_2_attribute).dtor_name).Equals(_1_name)) && ((new BigInteger(((_2_attribute).dtor_args).Count)).Sign == 0));
      }))))(attributes, name);
    }
    public DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> s = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName((mod).dtor_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_innerPath = _let_tmp_rhs0.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1_innerName = _let_tmp_rhs0.dtor__1;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_containingPath;
      _2_containingPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, _0_innerPath);
      Dafny.ISequence<Dafny.Rune> _3_modName;
      _3_modName = Defs.__default.escapeName(_1_innerName);
      if (((mod).dtor_body).is_None) {
        s = DafnyCompilerRustUtils.GatheringModule.Wrap(Defs.__default.ContainingPathToRust(_2_containingPath), RAST.Mod.create_ExternMod(_3_modName));
      } else {
        Defs._IExternAttribute _4_optExtern;
        _4_optExtern = Defs.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IAttribute> _5_attributes;
        _5_attributes = Dafny.Sequence<RAST._IAttribute>.FromElements();
        if ((this).HasAttribute((mod).dtor_attributes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_cfg_test"))) {
          _5_attributes = Dafny.Sequence<RAST._IAttribute>.FromElements(RAST.Attribute.CfgTest);
        }
        Dafny.ISequence<RAST._IModDecl> _6_body;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _7_allmodules;
        Dafny.ISequence<RAST._IModDecl> _out0;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out1;
        (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2_containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1_innerName)), out _out0, out _out1);
        _6_body = _out0;
        _7_allmodules = _out1;
        if ((_4_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _6_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((((this).thisFile).MSel(Defs.__default.DAFNY__EXTERN__MODULE)).MSels(Defs.__default.SplitRustPathElement(Defs.__default.ReplaceDotByDoubleColon((_4_optExtern).dtor_overrideName), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _6_body);
          }
        } else if ((_4_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_4_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_4_optExtern).dtor_reason);
        }
        s = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(DafnyCompilerRustUtils.GatheringModule.Wrap(Defs.__default.ContainingPathToRust(_2_containingPath), RAST.Mod.create_Mod((mod).dtor_docString, _5_attributes, _3_modName, _6_body)), _7_allmodules);
      }
      return s;
    }
    public void GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath, out Dafny.ISequence<RAST._IModDecl> s, out DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> allmodules)
    {
      s = Dafny.Sequence<RAST._IModDecl>.Empty;
      allmodules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      allmodules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi0 = new BigInteger((body).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        Dafny.ISequence<RAST._IModDecl> _1_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source0 = (body).Select(_0_i);
        {
          if (_source0.is_Module) {
            DAST._IModule _2_m = _source0.dtor_Module_a0;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _3_mm;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out0;
            _out0 = (this).GenModule(_2_m, containingPath);
            _3_mm = _out0;
            allmodules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(allmodules, _3_mm);
            _1_generated = Dafny.Sequence<RAST._IModDecl>.FromElements();
            goto after_match0;
          }
        }
        {
          if (_source0.is_Class) {
            DAST._IClass _4_c = _source0.dtor_Class_a0;
            Dafny.ISequence<RAST._IModDecl> _out1;
            _out1 = (this).GenClass(_4_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_4_c).dtor_name)));
            _1_generated = _out1;
            goto after_match0;
          }
        }
        {
          if (_source0.is_Trait) {
            DAST._ITrait _5_t = _source0.dtor_Trait_a0;
            Dafny.ISequence<RAST._IModDecl> _out2;
            _out2 = (this).GenTrait(_5_t, containingPath);
            _1_generated = _out2;
            goto after_match0;
          }
        }
        {
          if (_source0.is_Newtype) {
            DAST._INewtype _6_n = _source0.dtor_Newtype_a0;
            Dafny.ISequence<RAST._IModDecl> _out3;
            _out3 = (this).GenNewtype(_6_n, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_6_n).dtor_name)));
            _1_generated = _out3;
            goto after_match0;
          }
        }
        {
          if (_source0.is_SynonymType) {
            DAST._ISynonymType _7_s = _source0.dtor_SynonymType_a0;
            Dafny.ISequence<RAST._IModDecl> _out4;
            _out4 = (this).GenSynonymType(_7_s);
            _1_generated = _out4;
            goto after_match0;
          }
        }
        {
          DAST._IDatatype _8_d = _source0.dtor_Datatype_a0;
          Dafny.ISequence<RAST._IModDecl> _out5;
          _out5 = (this).GenDatatype(_8_d, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_8_d).dtor_name)));
          _1_generated = _out5;
        }
      after_match0: ;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1_generated);
      }
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      bool _0_supportsEquality;
      _0_supportsEquality = false;
      bool _1_supportsDefault;
      _1_supportsDefault = false;
      Dafny.ISequence<RAST._IType> _2_genTpConstraint;
      _2_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger(((tp).dtor_bounds).Count);
      for (BigInteger _3_i = BigInteger.Zero; _3_i < _hi0; _3_i++) {
        DAST._ITypeArgBound _4_bound;
        _4_bound = ((tp).dtor_bounds).Select(_3_i);
        DAST._ITypeArgBound _source0 = _4_bound;
        {
          if (_source0.is_SupportsEquality) {
            _0_supportsEquality = true;
            goto after_match0;
          }
        }
        {
          if (_source0.is_SupportsDefault) {
            _1_supportsDefault = true;
            goto after_match0;
          }
        }
        {
          DAST._IType _5_typ = _source0.dtor_typ;
          RAST._IType _6_tpe;
          RAST._IType _out0;
          _out0 = (this).GenType(_5_typ, Defs.GenTypeContext.ForTraitParents());
          _6_tpe = _out0;
          RAST._IType _7_upcast__tpe;
          _7_upcast__tpe = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastBox"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_6_tpe)));
          _2_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_2_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(_7_upcast__tpe));
        }
      after_match0: ;
      }
      if (_1_supportsDefault) {
        _2_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait), _2_genTpConstraint);
      }
      RAST._IType _8_dafnyType;
      if (_0_supportsEquality) {
        _8_dafnyType = RAST.__default.DafnyTypeEq;
      } else {
        _8_dafnyType = RAST.__default.DafnyType;
      }
      _2_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.FromElements(_8_dafnyType), _2_genTpConstraint);
      typeParam = RAST.TypeParamDecl.create(Defs.__default.escapeName(((tp).dtor_name)), _2_genTpConstraint);
    }
    public void GenTypeParameters(Dafny.ISequence<DAST._ITypeArgDecl> @params, out Dafny.ISequence<DAST._IType> typeParamsSeq, out Dafny.ISequence<RAST._IType> rTypeParams, out Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls)
    {
      typeParamsSeq = Dafny.Sequence<DAST._IType>.Empty;
      rTypeParams = Dafny.Sequence<RAST._IType>.Empty;
      rTypeParamsDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Empty;
      typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      rTypeParams = Dafny.Sequence<RAST._IType>.FromElements();
      rTypeParamsDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((@params).Count)).Sign == 1) {
        BigInteger _hi0 = new BigInteger((@params).Count);
        for (BigInteger _0_tpI = BigInteger.Zero; _0_tpI < _hi0; _0_tpI++) {
          DAST._ITypeArgDecl _1_tp;
          _1_tp = (@params).Select(_0_tpI);
          DAST._IType _2_typeArg;
          RAST._ITypeParamDecl _3_typeParam;
          DAST._IType _out0;
          RAST._ITypeParamDecl _out1;
          (this).GenTypeParam(_1_tp, out _out0, out _out1);
          _2_typeArg = _out0;
          _3_typeParam = _out1;
          RAST._IType _4_rType;
          RAST._IType _out2;
          _out2 = (this).GenType(_2_typeArg, Defs.GenTypeContext.@default());
          _4_rType = _out2;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_2_typeArg));
          rTypeParams = Dafny.Sequence<RAST._IType>.Concat(rTypeParams, Dafny.Sequence<RAST._IType>.FromElements(_4_rType));
          rTypeParamsDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(rTypeParamsDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_3_typeParam));
        }
      }
    }
    public bool IsSameResolvedTypeAnyArgs(DAST._IResolvedType r1, DAST._IResolvedType r2)
    {
      return (((r1).dtor_path).Equals((r2).dtor_path)) && (object.Equals((r1).dtor_kind, (r2).dtor_kind));
    }
    public bool IsSameResolvedType(DAST._IResolvedType r1, DAST._IResolvedType r2)
    {
      return ((this).IsSameResolvedTypeAnyArgs(r1, r2)) && (((r1).dtor_typeArgs).Equals((r2).dtor_typeArgs));
    }
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> GatherTypeParamNames(Dafny.ISet<Dafny.ISequence<Dafny.Rune>> types, RAST._IType typ)
    {
      return (typ).Fold<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>(types, ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>, RAST._IType, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)((_0_types, _1_currentType) => {
        return (((_1_currentType).is_TIdentifier) ? (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_0_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1_currentType).dtor_name))) : (_0_types));
      })));
    }
    public void GenField(DAST._IField field, out RAST._IField rfield, out RAST._IAssignIdentifier fieldInit, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> usedTypeParams)
    {
      rfield = RAST.Field.Default();
      fieldInit = RAST.AssignIdentifier.Default();
      usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      RAST._IType _0_fieldType;
      RAST._IType _out0;
      _out0 = (this).GenType(((field).dtor_formal).dtor_typ, Defs.GenTypeContext.@default());
      _0_fieldType = _out0;
      if (!((field).dtor_isConstant)) {
        _0_fieldType = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Field"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_0_fieldType));
      }
      usedTypeParams = (this).GatherTypeParamNames(usedTypeParams, _0_fieldType);
      Dafny.ISequence<Dafny.Rune> _1_fieldRustName;
      _1_fieldRustName = Defs.__default.escapeVar(((field).dtor_formal).dtor_name);
      rfield = RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1_fieldRustName, _0_fieldType));
      Std.Wrappers._IOption<DAST._IExpression> _source0 = (field).dtor_defaultValue;
      {
        if (_source0.is_Some) {
          DAST._IExpression _2_e = _source0.dtor_value;
          {
            RAST._IExpr _3_expr;
            Defs._IOwnership _4___v0;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _5___v1;
            RAST._IExpr _out1;
            Defs._IOwnership _out2;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
            (this).GenExpr(_2_e, Defs.SelfInfo.create_NoSelf(), Defs.Environment.Empty(), Defs.Ownership.create_OwnershipOwned(), out _out1, out _out2, out _out3);
            _3_expr = _out1;
            _4___v0 = _out2;
            _5___v1 = _out3;
            fieldInit = RAST.AssignIdentifier.create(_1_fieldRustName, _3_expr);
          }
          goto after_match0;
        }
      }
      {
        {
          RAST._IExpr _6_default;
          _6_default = RAST.__default.std__default__Default__default;
          if ((_0_fieldType).IsObjectOrPointer()) {
            _6_default = (_0_fieldType).ToNullExpr();
          }
          fieldInit = RAST.AssignIdentifier.create(_1_fieldRustName, _6_default);
        }
      }
    after_match0: ;
    }
    public void GetName(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> kind, out Dafny.ISequence<Dafny.Rune> rName, out Defs._IExternAttribute @extern)
    {
      rName = Dafny.Sequence<Dafny.Rune>.Empty;
      @extern = Defs.ExternAttribute.Default();
      @extern = Defs.__default.ExtractExtern(attributes, name);
      if ((@extern).is_SimpleExtern) {
        rName = (@extern).dtor_overrideName;
      } else {
        rName = Defs.__default.escapeName(name);
        if ((@extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for "), kind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" yet")));
        }
      }
    }
    public Dafny.ISequence<RAST._IModDecl> GenTraitImplementations(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> classPath, Dafny.ISequence<RAST._IType> rTypeParams, Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, Dafny.ISequence<DAST._IType> superTraitTypes, Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies, Defs._IExternAttribute @extern, bool supportsEquality, Dafny.ISequence<Dafny.Rune> kind)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      RAST._IPath _0_genPath;
      RAST._IPath _out0;
      _out0 = (this).GenPath(classPath, true);
      _0_genPath = _out0;
      RAST._IType _1_genSelfPath;
      _1_genSelfPath = (_0_genPath).AsType();
      RAST._IExpr _2_genPathExpr;
      _2_genPathExpr = (_0_genPath).AsExpr();
      BigInteger _hi0 = new BigInteger((superTraitTypes).Count);
      for (BigInteger _3_i = BigInteger.Zero; _3_i < _hi0; _3_i++) {
        DAST._IType _4_superTraitType;
        _4_superTraitType = (superTraitTypes).Select(_3_i);
        DAST._IType _source0 = _4_superTraitType;
        {
          if (_source0.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source0.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _5_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _6_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              DAST._ITraitType _7_traitType = kind0.dtor_traitType;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _8_properMethods = resolved0.dtor_properMethods;
              {
                RAST._IPath _9_path;
                RAST._IPath _out1;
                _out1 = (this).GenPath(_5_traitPath, true);
                _9_path = _out1;
                RAST._IType _10_pathType;
                _10_pathType = (_9_path).AsType();
                Dafny.ISequence<RAST._IType> _11_typeArgs;
                Dafny.ISequence<RAST._IType> _out2;
                _out2 = (this).GenTypeArgs(_6_typeArgs, Defs.GenTypeContext.@default());
                _11_typeArgs = _out2;
                Dafny.ISequence<RAST._IImplMember> _12_body;
                _12_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((traitBodies).Contains(_5_traitPath)) {
                  _12_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_5_traitPath);
                }
                RAST._IType _13_fullTraitPath;
                _13_fullTraitPath = RAST.Type.create_TypeApp(_10_pathType, _11_typeArgs);
                RAST._IExpr _14_fullTraitExpr;
                _14_fullTraitExpr = ((_9_path).AsExpr()).ApplyType(_11_typeArgs);
                if (!((@extern).is_NoExtern)) {
                  if (((new BigInteger((_12_body).Count)).Sign == 0) && ((new BigInteger((_8_properMethods).Count)).Sign != 0)) {
                    goto continue_0;
                  }
                  if ((new BigInteger((_12_body).Count)) != (new BigInteger((_8_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the "), kind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(classPath, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_15_s) => {
  return ((_15_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_13_fullTraitPath)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_8_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_16_s) => {
  return (_16_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                if ((_7_traitType).is_GeneralTrait) {
                  _12_body = Dafny.Sequence<RAST._IImplMember>.Concat(_12_body, Dafny.Sequence<RAST._IImplMember>.FromElements(Defs.__default.clone__trait(_13_fullTraitPath), Defs.__default.print__trait, Defs.__default.hasher__trait(supportsEquality, (this).pointerType), Defs.__default.eq__trait(_13_fullTraitPath, _14_fullTraitExpr, supportsEquality, (this).pointerType), Defs.__default.as__any__trait));
                } else {
                  if (((kind).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("datatype"))) || ((kind).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("newtype")))) {
                    RAST._IExpr _17_dummy;
                    RAST._IExpr _out3;
                    _out3 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot extend non-general traits"), (this).InitEmptyExpr());
                    _17_dummy = _out3;
                  }
                }
                RAST._IModDecl _18_x;
                _18_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, _13_fullTraitPath, RAST.Type.create_TypeApp(_1_genSelfPath, rTypeParams), _12_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_18_x));
                if ((_7_traitType).is_GeneralTrait) {
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastBox"))).AsType()).Apply1(RAST.Type.create_DynType(_13_fullTraitPath)), RAST.Type.create_TypeApp(_1_genSelfPath, rTypeParams), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Box(RAST.Type.create_DynType(_13_fullTraitPath))), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((_9_path).AsExpr()).ApplyType(_11_typeArgs)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_clone"))).Apply1(RAST.__default.self)))))))));
                } else {
                  s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_13_fullTraitPath))), RAST.Type.create_TypeApp(_1_genSelfPath, rTypeParams), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_13_fullTraitPath)))))))));
                }
              }
              goto after_match0;
            }
          }
        }
        {
        }
      after_match0: ;
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      Dafny.ISequence<Dafny.Rune> _3_constrainedTypeParams;
      _3_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _4_fields;
      _4_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _5_fieldInits;
      _5_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _6_usedTypeParams;
      _6_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi0 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _7_fieldI = BigInteger.Zero; _7_fieldI < _hi0; _7_fieldI++) {
        DAST._IField _8_field;
        _8_field = ((c).dtor_fields).Select(_7_fieldI);
        RAST._IField _9_rfield;
        RAST._IAssignIdentifier _10_fieldInit;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _11_fieldUsedTypeParams;
        RAST._IField _out3;
        RAST._IAssignIdentifier _out4;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
        (this).GenField(_8_field, out _out3, out _out4, out _out5);
        _9_rfield = _out3;
        _10_fieldInit = _out4;
        _11_fieldUsedTypeParams = _out5;
        _4_fields = Dafny.Sequence<RAST._IField>.Concat(_4_fields, Dafny.Sequence<RAST._IField>.FromElements(_9_rfield));
        _5_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_5_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(_10_fieldInit));
        _6_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_6_usedTypeParams, _11_fieldUsedTypeParams);
      }
      BigInteger _hi1 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _12_typeParamI = BigInteger.Zero; _12_typeParamI < _hi1; _12_typeParamI++) {
        DAST._IType _13_typeArg;
        RAST._ITypeParamDecl _14_typeParam;
        DAST._IType _out6;
        RAST._ITypeParamDecl _out7;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_12_typeParamI), out _out6, out _out7);
        _13_typeArg = _out6;
        _14_typeParam = _out7;
        RAST._IType _15_rTypeArg;
        RAST._IType _out8;
        _out8 = (this).GenType(_13_typeArg, Defs.GenTypeContext.@default());
        _15_rTypeArg = _out8;
        if ((_6_usedTypeParams).Contains((_14_typeParam).dtor_name)) {
          goto continue_0;
        }
        _4_fields = Dafny.Sequence<RAST._IField>.Concat(_4_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_12_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_15_rTypeArg))))));
        _5_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_5_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_12_typeParamI)), (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsExpr())));
      continue_0: ;
      }
    after_0: ;
      Dafny.ISequence<Dafny.Rune> _16_className;
      Defs._IExternAttribute _17_extern;
      Dafny.ISequence<Dafny.Rune> _out9;
      Defs._IExternAttribute _out10;
      (this).GetName((c).dtor_attributes, (c).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("classes"), out _out9, out _out10);
      _16_className = _out9;
      _17_extern = _out10;
      RAST._IStruct _18_struct;
      _18_struct = RAST.Struct.create((c).dtor_docString, Dafny.Sequence<RAST._IAttribute>.FromElements(), _16_className, _2_rTypeParamsDecls, RAST.Fields.create_NamedFields(_4_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_17_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_18_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _19_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _20_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out11;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out12;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out11, out _out12);
      _19_implBody = _out11;
      _20_traitBodies = _out12;
      if (((_17_extern).is_NoExtern) && (!(_16_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _19_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Allocates an UNINITIALIZED instance. Only the Dafny compiler should use that."), RAST.__default.NoAttr, RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply0())))), _19_implBody);
      }
      RAST._IType _21_selfTypeForImpl = RAST.Type.Default();
      if (((_17_extern).is_NoExtern) || ((_17_extern).is_UnsupportedExtern)) {
        _21_selfTypeForImpl = RAST.Type.create_TIdentifier(_16_className);
      } else if ((_17_extern).is_AdvancedExtern) {
        _21_selfTypeForImpl = (((RAST.__default.crate).MSels((_17_extern).dtor_enclosingModule)).MSel((_17_extern).dtor_overrideName)).AsType();
      } else if ((_17_extern).is_SimpleExtern) {
        _21_selfTypeForImpl = RAST.Type.create_TIdentifier((_17_extern).dtor_overrideName);
      }
      if ((new BigInteger((_19_implBody).Count)).Sign == 1) {
        RAST._IImpl _22_i;
        _22_i = RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(_21_selfTypeForImpl, _1_rTypeParams), _19_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_22_i)));
      }
      Dafny.ISequence<RAST._IModDecl> _23_testMethods;
      _23_testMethods = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_16_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        BigInteger _hi2 = new BigInteger(((c).dtor_body).Count);
        for (BigInteger _24_i = BigInteger.Zero; _24_i < _hi2; _24_i++) {
          DAST._IMethod _25_m;
          DAST._IMethod _source0 = ((c).dtor_body).Select(_24_i);
          {
            DAST._IMethod _26_m = _source0;
            _25_m = _26_m;
          }
        after_match0: ;
          if (((this).HasAttribute((_25_m).dtor_attributes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))) && ((new BigInteger(((_25_m).dtor_params).Count)).Sign == 0)) {
            Dafny.ISequence<Dafny.Rune> _27_fnName;
            _27_fnName = Defs.__default.escapeName((_25_m).dtor_name);
            _23_testMethods = Dafny.Sequence<RAST._IModDecl>.Concat(_23_testMethods, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create((_25_m).dtor_docString, Dafny.Sequence<RAST._IAttribute>.FromElements(RAST.Attribute.Name(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))), RAST.Visibility.create_PUB(), RAST.Fn.create(_27_fnName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))).FSel(_27_fnName)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())))))));
          }
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _23_testMethods);
      }
      RAST._IType _28_genSelfPath;
      RAST._IType _out13;
      _out13 = (this).GenPathType(path);
      _28_genSelfPath = _out13;
      if (!(_16_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements((this).DynAny)), RAST.Type.create_TypeApp(_28_genSelfPath, _1_rTypeParams), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType((this).DynAny))))))));
      }
      Dafny.ISequence<DAST._IType> _29_superTraitTypes;
      if ((_16_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        _29_superTraitTypes = Dafny.Sequence<DAST._IType>.FromElements();
      } else {
        _29_superTraitTypes = (c).dtor_superTraitTypes;
      }
      Dafny.ISequence<RAST._IModDecl> _30_superTraitImplementations;
      Dafny.ISequence<RAST._IModDecl> _out14;
      _out14 = (this).GenTraitImplementations(path, _1_rTypeParams, _2_rTypeParamsDecls, _29_superTraitTypes, _20_traitBodies, _17_extern, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("class"));
      _30_superTraitImplementations = _out14;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _30_superTraitImplementations);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      _0_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1_rTypeParamsDecls;
      _1_rTypeParamsDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _2_typeParams;
      _2_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi0 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _3_tpI = BigInteger.Zero; _3_tpI < _hi0; _3_tpI++) {
          DAST._ITypeArgDecl _4_tp;
          _4_tp = ((t).dtor_typeParams).Select(_3_tpI);
          DAST._IType _5_typeArg;
          RAST._ITypeParamDecl _6_typeParamDecl;
          DAST._IType _out0;
          RAST._ITypeParamDecl _out1;
          (this).GenTypeParam(_4_tp, out _out0, out _out1);
          _5_typeArg = _out0;
          _6_typeParamDecl = _out1;
          _0_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_0_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_5_typeArg));
          _1_rTypeParamsDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1_rTypeParamsDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_6_typeParamDecl));
          RAST._IType _7_typeParam;
          RAST._IType _out2;
          _out2 = (this).GenType(_5_typeArg, Defs.GenTypeContext.@default());
          _7_typeParam = _out2;
          _2_typeParams = Dafny.Sequence<RAST._IType>.Concat(_2_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_7_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _8_fullPath;
      _8_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<Dafny.Rune> _9_name;
      _9_name = Defs.__default.escapeName((t).dtor_name);
      RAST._IType _10_traitFullType;
      _10_traitFullType = (RAST.Type.create_TIdentifier(_9_name)).Apply(_2_typeParams);
      RAST._IExpr _11_traitFullExpr;
      _11_traitFullExpr = (RAST.Expr.create_Identifier(_9_name)).ApplyType(_2_typeParams);
      Dafny.ISequence<RAST._IImplMember> _12_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _13_implBodyImplementingOtherTraits;
      Dafny.ISequence<RAST._IImplMember> _out3;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out4;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_8_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait((t).dtor_traitType), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _0_typeParamsSeq, out _out3, out _out4);
      _12_implBody = _out3;
      _13_implBodyImplementingOtherTraits = _out4;
      if (((t).dtor_traitType).is_GeneralTrait) {
        _12_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_12_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_clone"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType))), Std.Wrappers.Option<RAST._IExpr>.create_None())), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Defs.__default.fmt__print__parameters, Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.fmt__print__result), Std.Wrappers.Option<RAST._IExpr>.create_None())), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64()), Std.Wrappers.Option<RAST._IExpr>.create_None())), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.Type.create_Borrowed(RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_None())), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as_any"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(RAST.Type.create_DynType(RAST.__default.AnyTrait))), Std.Wrappers.Option<RAST._IExpr>.create_None()))));
      }
      while ((new BigInteger((_13_implBodyImplementingOtherTraits).Count)).Sign == 1) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _14_otherTrait;
        foreach (Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _assign_such_that_0 in (_13_implBodyImplementingOtherTraits).Keys.Elements) {
          _14_otherTrait = (Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>)_assign_such_that_0;
          if ((_13_implBodyImplementingOtherTraits).Contains(_14_otherTrait)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value");
      after__ASSIGN_SUCH_THAT_0: ;
        Dafny.ISequence<RAST._IImplMember> _15_otherMethods;
        _15_otherMethods = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_13_implBodyImplementingOtherTraits,_14_otherTrait);
        BigInteger _hi1 = new BigInteger((_15_otherMethods).Count);
        for (BigInteger _16_i = BigInteger.Zero; _16_i < _hi1; _16_i++) {
          _12_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_12_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements((_15_otherMethods).Select(_16_i)));
        }
        _13_implBodyImplementingOtherTraits = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Subtract(_13_implBodyImplementingOtherTraits, Dafny.Set<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.FromElements(_14_otherTrait));
      }
      Dafny.ISequence<RAST._IType> _17_parents;
      _17_parents = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _18_upcastImplemented;
      _18_upcastImplemented = Dafny.Sequence<RAST._IModDecl>.FromElements();
      RAST._IType _19_instantiatedFullType = RAST.Type.Default();
      if (((t).dtor_traitType).is_GeneralTrait) {
        _19_instantiatedFullType = RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType));
        RAST._IModDecl _20_upcastDynTrait;
        _20_upcastDynTrait = Defs.__default.UpcastDynTraitFor(_1_rTypeParamsDecls, _19_instantiatedFullType, _10_traitFullType, _11_traitFullExpr);
        _18_upcastImplemented = Dafny.Sequence<RAST._IModDecl>.Concat(_18_upcastImplemented, Dafny.Sequence<RAST._IModDecl>.FromElements(_20_upcastDynTrait));
      }
      BigInteger _hi2 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _21_i = BigInteger.Zero; _21_i < _hi2; _21_i++) {
        DAST._IType _22_parentTyp;
        _22_parentTyp = ((t).dtor_parents).Select(_21_i);
        RAST._IType _23_parentTpe;
        RAST._IType _out5;
        _out5 = (this).GenType(_22_parentTyp, Defs.GenTypeContext.ForTraitParents());
        _23_parentTpe = _out5;
        _17_parents = Dafny.Sequence<RAST._IType>.Concat(_17_parents, Dafny.Sequence<RAST._IType>.FromElements(_23_parentTpe));
        Dafny.ISequence<Dafny.Rune> _24_upcastTrait;
        if ((_22_parentTyp).IsGeneralTrait()) {
          _24_upcastTrait = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastBox");
        } else {
          _24_upcastTrait = (this).Upcast;
        }
        _17_parents = Dafny.Sequence<RAST._IType>.Concat(_17_parents, Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel(_24_upcastTrait)).AsType()).Apply1(RAST.Type.create_DynType(_23_parentTpe))));
        if ((((_22_parentTyp).IsGeneralTrait()) && (((t).dtor_traitType).is_GeneralTrait)) && (!object.Equals(_23_parentTpe, (this).AnyTrait))) {
          Std.Wrappers._IOption<RAST._IExpr> _25_parentTpeExprMaybe;
          _25_parentTpeExprMaybe = (_23_parentTpe).ToExpr();
          RAST._IExpr _26_parentTpeExpr = RAST.Expr.Default();
          if ((_25_parentTpeExprMaybe).is_None) {
            RAST._IExpr _out6;
            _out6 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot convert "), (_23_parentTpe)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to an expression")), (this).InitEmptyExpr());
            _26_parentTpeExpr = _out6;
          } else {
            _26_parentTpeExpr = (_25_parentTpeExprMaybe).dtor_value;
          }
          RAST._IModDecl _27_upcastDynTrait;
          _27_upcastDynTrait = Defs.__default.UpcastDynTraitFor(_1_rTypeParamsDecls, _19_instantiatedFullType, _23_parentTpe, _26_parentTpeExpr);
          _18_upcastImplemented = Dafny.Sequence<RAST._IModDecl>.Concat(_18_upcastImplemented, Dafny.Sequence<RAST._IModDecl>.FromElements(_27_upcastDynTrait));
        }
      }
      Dafny.ISequence<RAST._IModDecl> _28_downcastDefinition;
      _28_downcastDefinition = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if (((new BigInteger(((t).dtor_parents).Count)).Sign == 1) && (((t).dtor_traitType).is_GeneralTrait)) {
        Std.Wrappers._IOption<RAST._IModDecl> _29_downcastDefinitionOpt;
        _29_downcastDefinitionOpt = Defs.__default.DowncastTraitDeclFor(_1_rTypeParamsDecls, _19_instantiatedFullType);
        if ((_29_downcastDefinitionOpt).is_None) {
          RAST._IExpr _30_dummy;
          RAST._IExpr _out7;
          _out7 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate downcast definition for "), (_19_instantiatedFullType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (this).InitEmptyExpr());
          _30_dummy = _out7;
        } else {
          _28_downcastDefinition = Dafny.Sequence<RAST._IModDecl>.FromElements((_29_downcastDefinitionOpt).dtor_value);
        }
      } else if (((t).dtor_traitType).is_GeneralTrait) {
        _17_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AnyRef"))).AsType()), _17_parents);
      }
      if (((new BigInteger(((t).dtor_downcastableTraits).Count)).Sign == 1) && (((t).dtor_traitType).is_GeneralTrait)) {
        BigInteger _hi3 = new BigInteger(((t).dtor_downcastableTraits).Count);
        for (BigInteger _31_i = BigInteger.Zero; _31_i < _hi3; _31_i++) {
          RAST._IType _32_downcastableTrait;
          RAST._IType _out8;
          _out8 = (this).GenType(((t).dtor_downcastableTraits).Select(_31_i), Defs.GenTypeContext.ForTraitParents());
          _32_downcastableTrait = _out8;
          Std.Wrappers._IOption<RAST._IType> _33_downcastTraitOpt;
          _33_downcastTraitOpt = (_32_downcastableTrait).ToDowncast();
          if ((_33_downcastTraitOpt).is_Some) {
            _17_parents = Dafny.Sequence<RAST._IType>.Concat(_17_parents, Dafny.Sequence<RAST._IType>.FromElements((_33_downcastTraitOpt).dtor_value));
          } else {
            RAST._IExpr _34_r;
            RAST._IExpr _out9;
            _out9 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot convert "), (_32_downcastableTrait)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to its downcast version")), (this).InitEmptyExpr());
            _34_r = _out9;
          }
        }
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create((t).dtor_docString, Dafny.Sequence<RAST._IAttribute>.FromElements(), _1_rTypeParamsDecls, _10_traitFullType, _17_parents, _12_implBody)));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _28_downcastDefinition);
      if (((t).dtor_traitType).is_GeneralTrait) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Clone"))).AsType(), RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType)), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Std.Wrappers.Option<RAST._IExpr>.create_Some(((_11_traitFullExpr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_clone"))).Apply1(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0()))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType)), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Defs.__default.fmt__print__parameters, Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.fmt__print__result), Std.Wrappers.Option<RAST._IExpr>.create_Some(((_11_traitFullExpr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0(), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"))))))))))));
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cmp"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PartialEq"))).AsType(), RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType)), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(((_11_traitFullExpr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_eq"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0(), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other")))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cmp"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Eq"))).AsType(), RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType)), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1_rTypeParamsDecls, RAST.__default.Hash, RAST.__default.Box(RAST.Type.create_DynType(_10_traitFullType)), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Defs.__default.hash__type__parameters, Defs.__default.hash__parameters, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some((Defs.__default.hash__function).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.Borrow(((_11_traitFullExpr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_hash"))).Apply1(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0())), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _18_upcastImplemented);
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      Dafny.ISequence<Dafny.Rune> _3_constrainedTypeParams;
      _3_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_2_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _4_wrappedType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _5_rustType;
      _5_rustType = Defs.__default.NewtypeRangeToUnwrappedBoundedRustType((c).dtor_base, (c).dtor_range);
      if ((_5_rustType).is_Some) {
        _4_wrappedType = (_5_rustType).dtor_value;
      } else {
        RAST._IType _out3;
        _out3 = (this).GenType((c).dtor_base, Defs.GenTypeContext.@default());
        _4_wrappedType = _out3;
      }
      DAST._IType _6_newtypeType;
      _6_newtypeType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, _0_typeParamsSeq, DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _7_newtypeName;
      _7_newtypeName = Defs.__default.escapeName((c).dtor_name);
      RAST._IType _8_resultingType;
      _8_resultingType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_7_newtypeName), _1_rTypeParams);
      Dafny.ISequence<Dafny.Rune> _9_attributes = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _10_deriveTraits;
      _10_deriveTraits = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Clone"));
      if (Defs.__default.IsNewtypeCopy((c).dtor_range)) {
        _10_deriveTraits = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_10_deriveTraits, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Copy")));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create((c).dtor_docString, Dafny.Sequence<RAST._IAttribute>.FromElements(RAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("derive"), _10_deriveTraits), RAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("repr"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("transparent")))), _7_newtypeName, _2_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _4_wrappedType))))));
      if (((c).dtor_equalitySupport).is_ConsultTypeArguments) {
        RAST._IExpr _11_eqImplBody;
        _11_eqImplBody = ((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Equals((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
        RAST._IExpr _12_hashImplBody;
        _12_hashImplBody = (Defs.__default.hash__function).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.Borrow((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
        Dafny.ISequence<RAST._IModDecl> _13_impls;
        Dafny.ISequence<RAST._IModDecl> _out4;
        _out4 = (this).GenEqHashImpls((c).dtor_typeParams, _2_rTypeParamsDecls, _1_rTypeParams, _8_resultingType, _11_eqImplBody, _12_hashImplBody);
        _13_impls = _out4;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _13_impls);
      }
      RAST._IExpr _14_fnBody = RAST.Expr.Default();
      Std.Wrappers._IOption<DAST._IExpression> _source0 = (c).dtor_witnessExpr;
      {
        if (_source0.is_Some) {
          DAST._IExpression _15_e = _source0.dtor_value;
          {
            DAST._IExpression _16_e;
            _16_e = DAST.Expression.create_Convert(_15_e, (c).dtor_base, _6_newtypeType);
            RAST._IExpr _17_r;
            Defs._IOwnership _18___v5;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _19___v6;
            RAST._IExpr _out5;
            Defs._IOwnership _out6;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
            (this).GenExpr(_16_e, Defs.SelfInfo.create_NoSelf(), Defs.Environment.Empty(), Defs.Ownership.create_OwnershipOwned(), out _out5, out _out6, out _out7);
            _17_r = _out5;
            _18___v5 = _out6;
            _19___v6 = _out7;
            _14_fnBody = _17_r;
          }
          goto after_match0;
        }
      }
      {
        {
          _14_fnBody = (RAST.Expr.create_Identifier(_7_newtypeName)).Apply1(RAST.__default.std__default__Default__default);
        }
      }
    after_match0: ;
      RAST._IImplMember _20_body;
      _20_body = RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("An element of "), _7_newtypeName), Dafny.Sequence<RAST._IAttribute>.FromElements(), RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Std.Wrappers.Option<RAST._IExpr>.create_Some(_14_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source1 = (c).dtor_constraint;
      {
        if (_source1.is_None) {
          goto after_match1;
        }
      }
      {
        DAST._INewtypeConstraint value0 = _source1.dtor_value;
        DAST._IFormal _21_formal = value0.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _22_constraintStmts = value0.dtor_constraintStmts;
        RAST._IExpr _23_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _24___v7;
        Defs._IEnvironment _25_newEnv;
        RAST._IExpr _out8;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
        Defs._IEnvironment _out10;
        (this).GenStmts(_22_constraintStmts, Defs.SelfInfo.create_NoSelf(), Defs.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out8, out _out9, out _out10);
        _23_rStmts = _out8;
        _24___v7 = _out9;
        _25_newEnv = _out10;
        Dafny.ISequence<RAST._IFormal> _26_rFormals;
        Dafny.ISequence<RAST._IFormal> _out11;
        _out11 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_21_formal), Dafny.Sequence<DAST._IFormal>.FromElements(_21_formal), false);
        _26_rFormals = _out11;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, _8_resultingType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Constraint check"), RAST.__default.NoAttr, RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _26_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(_23_rStmts))))))));
      }
    after_match1: ;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DefaultTrait, _8_resultingType, Dafny.Sequence<RAST._IImplMember>.FromElements(_20_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, RAST.__default.DafnyPrint, _8_resultingType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("For Dafny print statements"), RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Defs.__default.fmt__print__parameters, Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.fmt__print__result), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.Borrow((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"))))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_2_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ops"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Deref"))).AsType(), _8_resultingType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_TypeDeclMember(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"), _4_wrappedType), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.Borrow((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, _8_resultingType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SAFETY: The newtype is marked as transparent"), RAST.__default.NoAttr, RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_from_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("o"), RAST.Type.create_Borrowed(_4_wrappedType))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed((RAST.Path.create_Self()).AsType())), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.Unsafe(RAST.Expr.create_Block(((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mem"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("transmute"))).AsExpr()).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("o")))))))))))));
      if (((c).dtor_range).HasArithmeticOperations()) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.OpsImpl(new Dafny.Rune('+'), _2_rTypeParamsDecls, _8_resultingType, _7_newtypeName), Defs.__default.OpsImpl(new Dafny.Rune('-'), _2_rTypeParamsDecls, _8_resultingType, _7_newtypeName), Defs.__default.OpsImpl(new Dafny.Rune('*'), _2_rTypeParamsDecls, _8_resultingType, _7_newtypeName), Defs.__default.OpsImpl(new Dafny.Rune('/'), _2_rTypeParamsDecls, _8_resultingType, _7_newtypeName), Defs.__default.PartialOrdImpl(_2_rTypeParamsDecls, _8_resultingType, _7_newtypeName)));
      }
      if (((c).dtor_range).is_Bool) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.UnaryOpsImpl(new Dafny.Rune('!'), _2_rTypeParamsDecls, _8_resultingType, _7_newtypeName)));
      }
      Dafny.ISequence<RAST._IImplMember> _27_implementation;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _28_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out12;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out13;
      (this).GenClassImplBody((c).dtor_classItems, false, _6_newtypeType, _0_typeParamsSeq, out _out12, out _out13);
      _27_implementation = _out12;
      _28_traitBodies = _out13;
      if ((new BigInteger((_28_traitBodies).Count)).Sign == 1) {
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("No support for trait in newtypes yet"));
      }
      if ((new BigInteger((_27_implementation).Count)).Sign == 1) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_2_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_7_newtypeName), _1_rTypeParams), _27_implementation))));
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _0_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _2_rTypeParamsDecls;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2);
      _0_typeParamsSeq = _out0;
      _1_rTypeParams = _out1;
      _2_rTypeParamsDecls = _out2;
      Dafny.ISequence<Dafny.Rune> _3_synonymTypeName;
      _3_synonymTypeName = Defs.__default.escapeName((c).dtor_name);
      RAST._IType _4_resultingType;
      RAST._IType _out3;
      _out3 = (this).GenType((c).dtor_base, Defs.GenTypeContext.@default());
      _4_resultingType = _out3;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create((c).dtor_docString, Dafny.Sequence<RAST._IAttribute>.FromElements(), _3_synonymTypeName, _2_rTypeParamsDecls, _4_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _5_defaultConstrainedTypeParams;
      _5_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_2_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source0 = (c).dtor_witnessExpr;
      {
        if (_source0.is_Some) {
          DAST._IExpression _6_e = _source0.dtor_value;
          {
            RAST._IExpr _7_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _8___v8;
            Defs._IEnvironment _9_newEnv;
            RAST._IExpr _out4;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
            Defs._IEnvironment _out6;
            (this).GenStmts((c).dtor_witnessStmts, Defs.SelfInfo.create_NoSelf(), Defs.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out4, out _out5, out _out6);
            _7_rStmts = _out4;
            _8___v8 = _out5;
            _9_newEnv = _out6;
            RAST._IExpr _10_rExpr;
            Defs._IOwnership _11___v9;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _12___v10;
            RAST._IExpr _out7;
            Defs._IOwnership _out8;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out9;
            (this).GenExpr(_6_e, Defs.SelfInfo.create_NoSelf(), _9_newEnv, Defs.Ownership.create_OwnershipOwned(), out _out7, out _out8, out _out9);
            _10_rExpr = _out7;
            _11___v9 = _out8;
            _12___v10 = _out9;
            Dafny.ISequence<Dafny.Rune> _13_constantName;
            _13_constantName = Defs.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("An element of "), _3_synonymTypeName), Dafny.Sequence<RAST._IAttribute>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_13_constantName, _5_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_4_resultingType), Std.Wrappers.Option<RAST._IExpr>.create_Some((_7_rStmts).Then(_10_rExpr)))))));
          }
          goto after_match0;
        }
      }
      {
      }
    after_match0: ;
      return s;
    }
    public RAST._IExpr write(RAST._IExpr r, bool final)
    {
      RAST._IExpr _0_result = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), r));
      if (final) {
        return _0_result;
      } else {
        return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"), _0_result, DAST.Format.UnaryOpFormat.create_NoFormat());
      }
    }
    public RAST._IExpr writeStr(Dafny.ISequence<Dafny.Rune> s, bool final)
    {
      return (this).write(RAST.Expr.create_LiteralString(s, false, false), false);
    }
    public Dafny.ISequence<RAST._IModDecl> GenEqHashImpls(Dafny.ISequence<DAST._ITypeArgDecl> typeParamsDecls, Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, Dafny.ISequence<RAST._IType> rTypeParams, RAST._IType datatypeType, RAST._IExpr eqImplBody, RAST._IExpr hashImplBody)
    {
      Dafny.ISequence<RAST._IModDecl> impls = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<RAST._ITypeParamDecl> _0_rTypeParamsDeclsWithEq;
      _0_rTypeParamsDeclsWithEq = rTypeParamsDecls;
      Dafny.ISequence<RAST._ITypeParamDecl> _1_rTypeParamsDeclsWithHash;
      _1_rTypeParamsDeclsWithHash = rTypeParamsDecls;
      BigInteger _hi0 = new BigInteger((rTypeParamsDecls).Count);
      for (BigInteger _2_i = BigInteger.Zero; _2_i < _hi0; _2_i++) {
        if ((((typeParamsDecls).Select(_2_i)).dtor_info).dtor_necessaryForEqualitySupportOfSurroundingInductiveDatatype) {
          _0_rTypeParamsDeclsWithEq = Dafny.Sequence<RAST._ITypeParamDecl>.Update(_0_rTypeParamsDeclsWithEq, _2_i, ((_0_rTypeParamsDeclsWithEq).Select(_2_i)).AddConstraints(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq, RAST.__default.Hash)));
          _1_rTypeParamsDeclsWithHash = Dafny.Sequence<RAST._ITypeParamDecl>.Update(_1_rTypeParamsDeclsWithHash, _2_i, ((_1_rTypeParamsDeclsWithHash).Select(_2_i)).AddConstraints(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash)));
        }
      }
      impls = Defs.__default.EqImpl(_0_rTypeParamsDeclsWithEq, datatypeType, rTypeParams, eqImplBody);
      impls = Dafny.Sequence<RAST._IModDecl>.Concat(impls, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.HashImpl(_1_rTypeParamsDeclsWithHash, datatypeType, hashImplBody)));
      return impls;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      bool _0_isRcWrapped;
      _0_isRcWrapped = Defs.__default.IsRcWrapped((c).dtor_attributes);
      Dafny.ISequence<DAST._IType> _1_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _2_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _3_rTypeParamsDecls;
      Dafny.ISequence<DAST._IType> _out0;
      Dafny.ISequence<RAST._IType> _out1;
      Dafny.ISequence<RAST._ITypeParamDecl> _out2;
      (this).GenTypeParameters((c).dtor_typeParams, out _out0, out _out1, out _out2);
      _1_typeParamsSeq = _out0;
      _2_rTypeParams = _out1;
      _3_rTypeParamsDecls = _out2;
      Dafny.ISequence<Dafny.Rune> _4_datatypeName;
      Defs._IExternAttribute _5_extern;
      Dafny.ISequence<Dafny.Rune> _out3;
      Defs._IExternAttribute _out4;
      (this).GetName((c).dtor_attributes, (c).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("datatypes"), out _out3, out _out4);
      _4_datatypeName = _out3;
      _5_extern = _out4;
      Dafny.ISequence<RAST._IEnumCase> _6_ctors;
      _6_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._ITypeParameterInfo> _7_typeParamInfos;
      _7_typeParamInfos = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._ITypeParameterInfo>(((System.Func<DAST._ITypeArgDecl, DAST._ITypeParameterInfo>)((_8_typeParamDecl) => {
        return (_8_typeParamDecl).dtor_info;
      })), (c).dtor_typeParams);
      Dafny.ISequence<RAST._IExpr> _9_singletonConstructors;
      _9_singletonConstructors = Dafny.Sequence<RAST._IExpr>.FromElements();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _10_usedTypeParams;
      _10_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi0 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _11_i = BigInteger.Zero; _11_i < _hi0; _11_i++) {
        DAST._IDatatypeCtor _12_ctor;
        _12_ctor = ((c).dtor_ctors).Select(_11_i);
        Dafny.ISequence<RAST._IField> _13_ctorArgs;
        _13_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _14_isNumeric;
        _14_isNumeric = false;
        if ((new BigInteger(((_12_ctor).dtor_args).Count)).Sign == 0) {
          RAST._IExpr _15_instantiation;
          _15_instantiation = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_4_datatypeName)).FSel(Defs.__default.escapeName((_12_ctor).dtor_name)), Dafny.Sequence<RAST._IAssignIdentifier>.FromElements());
          if (_0_isRcWrapped) {
            _15_instantiation = Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>((this).rcNew)(_15_instantiation);
          }
          _9_singletonConstructors = Dafny.Sequence<RAST._IExpr>.Concat(_9_singletonConstructors, Dafny.Sequence<RAST._IExpr>.FromElements(_15_instantiation));
        }
        BigInteger _hi1 = new BigInteger(((_12_ctor).dtor_args).Count);
        for (BigInteger _16_j = BigInteger.Zero; _16_j < _hi1; _16_j++) {
          DAST._IDatatypeDtor _17_dtor;
          _17_dtor = ((_12_ctor).dtor_args).Select(_16_j);
          RAST._IType _18_formalType;
          RAST._IType _out5;
          _out5 = (this).GenType(((_17_dtor).dtor_formal).dtor_typ, Defs.GenTypeContext.@default());
          _18_formalType = _out5;
          _10_usedTypeParams = (this).GatherTypeParamNames(_10_usedTypeParams, _18_formalType);
          Dafny.ISequence<Dafny.Rune> _19_formalName;
          _19_formalName = Defs.__default.escapeVar(((_17_dtor).dtor_formal).dtor_name);
          if (((_16_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_19_formalName))) {
            _14_isNumeric = true;
          }
          if ((((_16_j).Sign != 0) && (_14_isNumeric)) && (!(Std.Strings.__default.OfNat(_16_j)).Equals(_19_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _19_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_16_j)));
            _14_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _13_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_13_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_19_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_18_formalType))))));
          } else {
            _13_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_13_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_19_formalName, _18_formalType))));
          }
        }
        RAST._IFields _20_namedFields;
        _20_namedFields = RAST.Fields.create_NamedFields(_13_ctorArgs);
        if (_14_isNumeric) {
          _20_namedFields = (_20_namedFields).ToNamelessFields();
        }
        _6_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_6_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create((_12_ctor).dtor_docString, Defs.__default.escapeName((_12_ctor).dtor_name), _20_namedFields)));
      }
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _21_unusedTypeParams;
      _21_unusedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._ITypeParamDecl>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_22_rTypeParamsDecls) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
        foreach (RAST._ITypeParamDecl _compr_0 in (_22_rTypeParamsDecls).CloneAsArray()) {
          RAST._ITypeParamDecl _23_tp = (RAST._ITypeParamDecl)_compr_0;
          if ((_22_rTypeParamsDecls).Contains(_23_tp)) {
            _coll0.Add((_23_tp).dtor_name);
          }
        }
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll0);
      }))())(_3_rTypeParamsDecls), _10_usedTypeParams);
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _24_selfPath;
      _24_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _25_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _26_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out6;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out7;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_24_selfPath, _1_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype((c).dtor_equalitySupport, _7_typeParamInfos), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1_typeParamsSeq, out _out6, out _out7);
      _25_implBodyRaw = _out6;
      _26_traitBodies = _out7;
      Dafny.ISequence<RAST._IImplMember> _27_implBody;
      _27_implBody = _25_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _28_emittedFields;
      _28_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi2 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _29_i = BigInteger.Zero; _29_i < _hi2; _29_i++) {
        DAST._IDatatypeCtor _30_ctor;
        _30_ctor = ((c).dtor_ctors).Select(_29_i);
        BigInteger _hi3 = new BigInteger(((_30_ctor).dtor_args).Count);
        for (BigInteger _31_j = BigInteger.Zero; _31_j < _hi3; _31_j++) {
          DAST._IDatatypeDtor _32_dtor;
          _32_dtor = ((_30_ctor).dtor_args).Select(_31_j);
          Dafny.ISequence<Dafny.Rune> _33_callName;
          _33_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_32_dtor).dtor_callName, Defs.__default.escapeVar(((_32_dtor).dtor_formal).dtor_name));
          if (!((_28_emittedFields).Contains(_33_callName))) {
            _28_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_28_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_33_callName));
            RAST._IType _34_formalType;
            RAST._IType _out8;
            _out8 = (this).GenType(((_32_dtor).dtor_formal).dtor_typ, Defs.GenTypeContext.@default());
            _34_formalType = _out8;
            Dafny.ISequence<RAST._IMatchCase> _35_cases;
            _35_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi4 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _36_k = BigInteger.Zero; _36_k < _hi4; _36_k++) {
              DAST._IDatatypeCtor _37_ctor2;
              _37_ctor2 = ((c).dtor_ctors).Select(_36_k);
              Dafny.ISequence<Dafny.Rune> _38_pattern;
              _38_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), Defs.__default.escapeName((_37_ctor2).dtor_name));
              RAST._IExpr _39_rhs = RAST.Expr.Default();
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _40_hasMatchingField;
              _40_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _41_patternInner;
              _41_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _42_isNumeric;
              _42_isNumeric = false;
              BigInteger _hi5 = new BigInteger(((_37_ctor2).dtor_args).Count);
              for (BigInteger _43_l = BigInteger.Zero; _43_l < _hi5; _43_l++) {
                DAST._IDatatypeDtor _44_dtor2;
                _44_dtor2 = ((_37_ctor2).dtor_args).Select(_43_l);
                Dafny.ISequence<Dafny.Rune> _45_patternName;
                _45_patternName = Defs.__default.escapeVar(((_44_dtor2).dtor_formal).dtor_name);
                if (((_43_l).Sign == 0) && ((_45_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _42_isNumeric = true;
                }
                if (_42_isNumeric) {
                  _45_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_44_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_43_l)));
                }
                if (object.Equals(((_32_dtor).dtor_formal).dtor_name, ((_44_dtor2).dtor_formal).dtor_name)) {
                  _40_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_45_patternName);
                }
                _41_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_41_patternInner, _45_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_42_isNumeric) {
                _38_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_38_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _41_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _38_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_38_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _41_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_40_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _39_rhs = (((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ops"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Deref"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"))).Apply1(RAST.__default.Borrow((RAST.Expr.create_Identifier((_40_hasMatchingField).dtor_value)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))));
                } else {
                  _39_rhs = RAST.Expr.create_Identifier((_40_hasMatchingField).dtor_value);
                }
              } else {
                _39_rhs = Defs.__default.UnreachablePanicIfVerified((this).pointerType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _46_ctorMatch;
              _46_ctorMatch = RAST.MatchCase.create(_38_pattern, _39_rhs);
              _35_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_35_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_46_ctorMatch));
            }
            if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_21_unusedTypeParams).Count)).Sign == 1)) {
              _35_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_35_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), Defs.__default.UnreachablePanicIfVerified((this).pointerType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            }
            RAST._IExpr _47_methodBody;
            _47_methodBody = RAST.Expr.create_Match(RAST.__default.self, _35_cases);
            _27_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_27_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl((((new BigInteger(((c).dtor_ctors).Count)) == (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Returns a borrow of the field "), _33_callName)) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Gets the field "), _33_callName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" for all enum members which have it")))), Dafny.Sequence<RAST._IAttribute>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_33_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_34_formalType)), Std.Wrappers.Option<RAST._IExpr>.create_Some(_47_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _48_coerceTypes;
      _48_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _49_rCoerceTypeParams;
      _49_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _50_coerceArguments;
      _50_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _51_coerceMap;
      _51_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _52_rCoerceMap;
      _52_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _53_coerceMapToArg;
      _53_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _54_types;
        _54_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi6 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _55_typeI = BigInteger.Zero; _55_typeI < _hi6; _55_typeI++) {
          DAST._ITypeArgDecl _56_typeParam;
          _56_typeParam = ((c).dtor_typeParams).Select(_55_typeI);
          DAST._IType _57_typeArg;
          RAST._ITypeParamDecl _58_rTypeParamDecl;
          DAST._IType _out9;
          RAST._ITypeParamDecl _out10;
          (this).GenTypeParam(_56_typeParam, out _out9, out _out10);
          _57_typeArg = _out9;
          _58_rTypeParamDecl = _out10;
          RAST._IType _59_rTypeArg;
          RAST._IType _out11;
          _out11 = (this).GenType(_57_typeArg, Defs.GenTypeContext.@default());
          _59_rTypeArg = _out11;
          _54_types = Dafny.Sequence<RAST._IType>.Concat(_54_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_59_rTypeArg))));
          if (((_55_typeI) < (new BigInteger((_7_typeParamInfos).Count))) && ((((_7_typeParamInfos).Select(_55_typeI)).dtor_variance).is_Nonvariant)) {
            _48_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_48_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_59_rTypeArg));
            goto continue_2_0;
          }
          DAST._ITypeArgDecl _60_coerceTypeParam;
          DAST._ITypeArgDecl _61_dt__update__tmp_h0 = _56_typeParam;
          Dafny.ISequence<Dafny.Rune> _62_dt__update_hname_h0 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_55_typeI));
          _60_coerceTypeParam = DAST.TypeArgDecl.create(_62_dt__update_hname_h0, (_61_dt__update__tmp_h0).dtor_bounds, (_61_dt__update__tmp_h0).dtor_info);
          DAST._IType _63_coerceTypeArg;
          RAST._ITypeParamDecl _64_rCoerceTypeParamDecl;
          DAST._IType _out12;
          RAST._ITypeParamDecl _out13;
          (this).GenTypeParam(_60_coerceTypeParam, out _out12, out _out13);
          _63_coerceTypeArg = _out12;
          _64_rCoerceTypeParamDecl = _out13;
          _51_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_51_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_57_typeArg, _63_coerceTypeArg)));
          RAST._IType _65_rCoerceType;
          RAST._IType _out14;
          _out14 = (this).GenType(_63_coerceTypeArg, Defs.GenTypeContext.@default());
          _65_rCoerceType = _out14;
          _52_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_52_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_59_rTypeArg, _65_rCoerceType)));
          _48_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_48_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_65_rCoerceType));
          _49_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_49_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_64_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _66_coerceFormal;
          _66_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_55_typeI));
          _53_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_53_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_59_rTypeArg, _65_rCoerceType), (RAST.Expr.create_Identifier(_66_coerceFormal)).Clone())));
          _50_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_50_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_66_coerceFormal, Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>((this).rc)(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_59_rTypeArg), _65_rCoerceType)), RAST.__default.StaticTrait)))));
        continue_2_0: ;
        }
      after_2_0: ;
        if ((new BigInteger((_21_unusedTypeParams).Count)).Sign == 1) {
          _6_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_6_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_67_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _67_tpe);
})), _54_types)))));
        }
      }
      bool _68_cIsAlwaysEq;
      _68_cIsAlwaysEq = (((c).dtor_equalitySupport).is_ConsultTypeArguments) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_69_c) => Dafny.Helpers.Quantifier<DAST._ITypeArgDecl>(((_69_c).dtor_typeParams).UniqueElements, true, (((_forall_var_0) => {
        DAST._ITypeArgDecl _70_t = (DAST._ITypeArgDecl)_forall_var_0;
        return !(((_69_c).dtor_typeParams).Contains(_70_t)) || (!(((_70_t).dtor_info).dtor_necessaryForEqualitySupportOfSurroundingInductiveDatatype));
      }))))(c));
      RAST._IType _71_datatypeType;
      _71_datatypeType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_4_datatypeName), _2_rTypeParams);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create((c).dtor_docString, Dafny.Sequence<RAST._IAttribute>.FromElements(RAST.Attribute.DeriveClone), _4_datatypeName, _3_rTypeParamsDecls, _6_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_3_rTypeParamsDecls, _71_datatypeType, _27_implBody)));
      if ((new BigInteger(((c).dtor_superTraitTypes).Count)).Sign == 1) {
        RAST._IType _72_fullType;
        if (_0_isRcWrapped) {
          _72_fullType = Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>((this).rc)(_71_datatypeType);
        } else {
          _72_fullType = _71_datatypeType;
        }
        Std.Wrappers._IOption<RAST._IModDecl> _73_downcastDefinitionOpt;
        _73_downcastDefinitionOpt = Defs.__default.DowncastTraitDeclFor(_3_rTypeParamsDecls, _72_fullType);
        if ((_73_downcastDefinitionOpt).is_None) {
          RAST._IExpr _74_dummy;
          RAST._IExpr _out15;
          _out15 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate downcast definition for "), (_72_fullType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (this).InitEmptyExpr());
          _74_dummy = _out15;
        } else {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements((_73_downcastDefinitionOpt).dtor_value));
        }
        Std.Wrappers._IOption<RAST._IModDecl> _75_downcastImplementationsOpt;
        _75_downcastImplementationsOpt = Defs.__default.DowncastImplFor((this).rcNew, _3_rTypeParamsDecls, _72_fullType);
        if ((_75_downcastImplementationsOpt).is_None) {
          RAST._IExpr _76_dummy;
          RAST._IExpr _out16;
          _out16 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate downcast implementation for "), (_72_fullType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (this).InitEmptyExpr());
          _76_dummy = _out16;
        } else {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements((_75_downcastImplementationsOpt).dtor_value));
        }
        BigInteger _hi7 = new BigInteger(((c).dtor_superTraitNegativeTypes).Count);
        for (BigInteger _77_i = BigInteger.Zero; _77_i < _hi7; _77_i++) {
          RAST._IType _78_negativeTraitType;
          RAST._IType _out17;
          _out17 = (this).GenType(((c).dtor_superTraitNegativeTypes).Select(_77_i), Defs.GenTypeContext.@default());
          _78_negativeTraitType = _out17;
          Std.Wrappers._IOption<RAST._IModDecl> _79_downcastDefinitionOpt;
          _79_downcastDefinitionOpt = Defs.__default.DowncastNotImplFor(_3_rTypeParamsDecls, _78_negativeTraitType, _72_fullType);
          if ((_79_downcastDefinitionOpt).is_None) {
            RAST._IExpr _80_dummy;
            RAST._IExpr _out18;
            _out18 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate negative downcast definition for "), (_72_fullType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (this).InitEmptyExpr());
            _80_dummy = _out18;
          } else {
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements((_79_downcastDefinitionOpt).dtor_value));
          }
        }
        BigInteger _hi8 = new BigInteger(((c).dtor_superTraitTypes).Count);
        for (BigInteger _81_i = BigInteger.Zero; _81_i < _hi8; _81_i++) {
          DAST._IType _82_c;
          _82_c = ((c).dtor_superTraitTypes).Select(_81_i);
          if ((((_82_c).is_UserDefined) && ((((_82_c).dtor_resolved).dtor_kind).is_Trait)) && ((new BigInteger((((_82_c).dtor_resolved).dtor_extendedTypes).Count)).Sign == 0)) {
            goto continue_3_0;
          }
          RAST._IType _83_cType;
          RAST._IType _out19;
          _out19 = (this).GenType(_82_c, Defs.GenTypeContext.@default());
          _83_cType = _out19;
          bool _84_isImplementing;
          _84_isImplementing = true;
          Std.Wrappers._IOption<RAST._IModDecl> _85_downcastImplementationsOpt;
          _85_downcastImplementationsOpt = Defs.__default.DowncastImplTraitFor(_3_rTypeParamsDecls, _83_cType, _84_isImplementing, _72_fullType);
          if ((_85_downcastImplementationsOpt).is_None) {
            RAST._IExpr _86_dummy;
            RAST._IExpr _out20;
            _out20 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate downcast implementation of "), (_83_cType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" for ")), (_72_fullType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (this).InitEmptyExpr());
            _86_dummy = _out20;
          } else {
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements((_85_downcastImplementationsOpt).dtor_value));
          }
        continue_3_0: ;
        }
      after_3_0: ;
      }
      Dafny.ISequence<RAST._IMatchCase> _87_printImplBodyCases;
      _87_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _88_hashImplBodyCases;
      _88_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _89_coerceImplBodyCases;
      _89_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _90_partialEqImplBodyCases;
      _90_partialEqImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi9 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _91_i = BigInteger.Zero; _91_i < _hi9; _91_i++) {
        DAST._IDatatypeCtor _92_ctor;
        _92_ctor = ((c).dtor_ctors).Select(_91_i);
        Dafny.ISequence<Dafny.Rune> _93_ctorMatch;
        _93_ctorMatch = Defs.__default.escapeName((_92_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _94_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _94_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _94_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _95_ctorName;
        _95_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_94_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_92_ctor).dtor_name));
        if (((new BigInteger((_95_ctorName).Count)) >= (new BigInteger(13))) && (((_95_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _95_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _96_printRhs;
        _96_printRhs = (this).writeStr(Dafny.Sequence<Dafny.Rune>.Concat(_95_ctorName, (((_92_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), false);
        RAST._IExpr _97_hashRhs;
        _97_hashRhs = (this).InitEmptyExpr();
        RAST._IExpr _98_partialEqRhs;
        _98_partialEqRhs = RAST.Expr.create_LiteralBool(true);
        Dafny.ISequence<RAST._IAssignIdentifier> _99_coerceRhsArgs;
        _99_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _100_isNumeric;
        _100_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _101_ctorMatchInner;
        _101_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        Dafny.ISequence<Dafny.Rune> _102_ctorMatchInner2;
        _102_ctorMatchInner2 = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi10 = new BigInteger(((_92_ctor).dtor_args).Count);
        for (BigInteger _103_j = BigInteger.Zero; _103_j < _hi10; _103_j++) {
          DAST._IDatatypeDtor _104_dtor;
          _104_dtor = ((_92_ctor).dtor_args).Select(_103_j);
          Dafny.ISequence<Dafny.Rune> _105_patternName;
          _105_patternName = Defs.__default.escapeVar(((_104_dtor).dtor_formal).dtor_name);
          DAST._IType _106_formalType;
          _106_formalType = ((_104_dtor).dtor_formal).dtor_typ;
          if (((_103_j).Sign == 0) && ((_105_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _100_isNumeric = true;
          }
          if (_100_isNumeric) {
            _105_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_104_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_103_j)));
          }
          if ((_106_formalType).is_Arrow) {
            _97_hashRhs = (_97_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          } else {
            _97_hashRhs = (_97_hashRhs).Then((Defs.__default.hash__function).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_105_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))));
          }
          _101_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_101_ctorMatchInner, _105_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          Dafny.ISequence<Dafny.Rune> _107_matchingVariable2;
          _107_matchingVariable2 = Defs.__default.prefixWith2(_105_patternName);
          Dafny.ISequence<Dafny.Rune> _108_patternPrefix;
          if (_100_isNumeric) {
            _108_patternPrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          } else {
            _108_patternPrefix = Dafny.Sequence<Dafny.Rune>.Concat(_105_patternName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "));
          }
          _102_ctorMatchInner2 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_102_ctorMatchInner2, _108_patternPrefix), _107_matchingVariable2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_106_formalType).is_Arrow) {
            _98_partialEqRhs = (_98_partialEqRhs).And(RAST.Expr.create_LiteralBool(false));
          } else {
            _98_partialEqRhs = (_98_partialEqRhs).And((RAST.Expr.create_Identifier(_105_patternName)).Equals(RAST.Expr.create_Identifier(_107_matchingVariable2)));
          }
          if ((_103_j).Sign == 1) {
            _96_printRhs = (_96_printRhs).Then((this).writeStr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "), false));
          }
          _96_printRhs = (_96_printRhs).Then((((_106_formalType).is_Arrow) ? ((this).writeStr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<function>"), false)) : (RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"), ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_105_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), RAST.Expr.create_LiteralBool(false))), DAST.Format.UnaryOpFormat.create_NoFormat()))));
          RAST._IExpr _109_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _110_formalTpe;
          RAST._IType _out21;
          _out21 = (this).GenType(_106_formalType, Defs.GenTypeContext.@default());
          _110_formalTpe = _out21;
          DAST._IType _111_newFormalType;
          _111_newFormalType = (_106_formalType).Replace(_51_coerceMap);
          RAST._IType _112_newFormalTpe;
          _112_newFormalTpe = (_110_formalTpe).ReplaceMap(_52_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _113_upcastConverter;
          _113_upcastConverter = (this).UpcastConversionLambda(_106_formalType, _110_formalTpe, _111_newFormalType, _112_newFormalTpe, _53_coerceMapToArg);
          if ((_113_upcastConverter).is_Success) {
            RAST._IExpr _114_coercionFunction;
            _114_coercionFunction = (_113_upcastConverter).dtor_value;
            _109_coerceRhsArg = (_114_coercionFunction).Apply1(RAST.Expr.create_Identifier(_105_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_103_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _4_datatypeName));
            _109_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _99_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_99_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_105_patternName, _109_coerceRhsArg)));
        }
        RAST._IExpr _115_coerceRhs;
        _115_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_4_datatypeName)).FSel(Defs.__default.escapeName((_92_ctor).dtor_name)), _99_coerceRhsArgs);
        Dafny.ISequence<Dafny.Rune> _116_pattern = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _117_pattern2 = Dafny.Sequence<Dafny.Rune>.Empty;
        if (_100_isNumeric) {
          _116_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_93_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _101_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          _117_pattern2 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_93_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _102_ctorMatchInner2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _116_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_93_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _101_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          _117_pattern2 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_93_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _102_ctorMatchInner2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_92_ctor).dtor_hasAnyArgs) {
          _96_printRhs = (_96_printRhs).Then((this).writeStr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"), false));
        }
        _96_printRhs = (_96_printRhs).Then((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements()))));
        _87_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_87_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _116_pattern), RAST.Expr.create_Block(_96_printRhs))));
        _88_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_88_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _116_pattern), RAST.Expr.create_Block(_97_hashRhs))));
        _90_partialEqImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_90_partialEqImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _4_datatypeName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _116_pattern), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _4_datatypeName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _117_pattern2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), RAST.Expr.create_Block(_98_partialEqRhs))));
        _89_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_89_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _116_pattern), RAST.Expr.create_Block(_115_coerceRhs))));
      }
      _90_partialEqImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_90_partialEqImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), RAST.Expr.create_Block(RAST.Expr.create_LiteralBool(false)))));
      if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_21_unusedTypeParams).Count)).Sign == 1)) {
        Dafny.ISequence<RAST._IMatchCase> _118_extraCases;
        _118_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_4_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_Block(Defs.__default.UnreachablePanicIfVerified((this).pointerType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
        _87_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_87_printImplBodyCases, _118_extraCases);
        _88_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_88_hashImplBodyCases, _118_extraCases);
        _89_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_89_coerceImplBodyCases, _118_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _119_defaultConstrainedTypeParams;
      _119_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_3_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      RAST._IExpr _120_printImplBody;
      _120_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _87_printImplBodyCases);
      RAST._IExpr _121_hashImplBody;
      _121_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _88_hashImplBodyCases);
      RAST._IExpr _122_eqImplBody;
      _122_eqImplBody = RAST.Expr.create_Match(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other")))), _90_partialEqImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.DebugImpl(_3_rTypeParamsDecls, _71_datatypeType, _2_rTypeParams), Defs.__default.PrintImpl(_3_rTypeParamsDecls, _71_datatypeType, _2_rTypeParams, _120_printImplBody)));
      if ((new BigInteger((_49_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _123_coerceImplBody;
        _123_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _89_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.CoerceImpl((this).rc, (this).rcNew, _3_rTypeParamsDecls, _4_datatypeName, _71_datatypeType, _49_rCoerceTypeParams, _50_coerceArguments, _48_coerceTypes, _123_coerceImplBody)));
      }
      if ((new BigInteger((_9_singletonConstructors).Count)) == (new BigInteger(((c).dtor_ctors).Count))) {
        RAST._IType _124_instantiationType;
        if (_0_isRcWrapped) {
          _124_instantiationType = Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>((this).rc)(_71_datatypeType);
        } else {
          _124_instantiationType = _71_datatypeType;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.SingletonsImpl(_3_rTypeParamsDecls, _71_datatypeType, _124_instantiationType, _9_singletonConstructors)));
      }
      if (((c).dtor_equalitySupport).is_ConsultTypeArguments) {
        Dafny.ISequence<RAST._IModDecl> _125_impls;
        Dafny.ISequence<RAST._IModDecl> _out22;
        _out22 = (this).GenEqHashImpls((c).dtor_typeParams, _3_rTypeParamsDecls, _2_rTypeParams, _71_datatypeType, _122_eqImplBody, _121_hashImplBody);
        _125_impls = _out22;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _125_impls);
      }
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _126_structName;
        _126_structName = (RAST.Expr.create_Identifier(_4_datatypeName)).FSel(Defs.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _127_structAssignments;
        _127_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi11 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _128_i = BigInteger.Zero; _128_i < _hi11; _128_i++) {
          DAST._IDatatypeDtor _129_dtor;
          _129_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_128_i);
          _127_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_127_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Defs.__default.escapeVar(((_129_dtor).dtor_formal).dtor_name), (((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).Apply0())));
        }
        if ((false) && (_68_cIsAlwaysEq)) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.DefaultDatatypeImpl(_3_rTypeParamsDecls, _71_datatypeType, _126_structName, _127_structAssignments)));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(Defs.__default.AsRefDatatypeImpl(_3_rTypeParamsDecls, _71_datatypeType)));
      }
      Dafny.ISequence<RAST._IModDecl> _130_superTraitImplementations;
      Dafny.ISequence<RAST._IModDecl> _out23;
      _out23 = (this).GenTraitImplementations(path, _2_rTypeParams, _3_rTypeParamsDecls, (c).dtor_superTraitTypes, _26_traitBodies, _5_extern, _68_cIsAlwaysEq, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("datatype"));
      _130_superTraitImplementations = _out23;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _130_superTraitImplementations);
      return s;
    }
    public RAST._IPath GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IPath r = RAST.Path.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.Path.create_Self();
        return r;
      } else {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_p;
        _0_p = p;
        Dafny.ISequence<Dafny.Rune> _1_name;
        _1_name = (((_0_p).Select(BigInteger.Zero)));
        if (((new BigInteger((_1_name).Count)) >= (new BigInteger(2))) && (((_1_name).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")))) {
          r = RAST.Path.create_Global();
          _0_p = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Update(_0_p, BigInteger.Zero, (_1_name).Drop(new BigInteger(2)));
        } else if (((((_0_p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) {
          r = RAST.__default.dafny__runtime;
        } else {
          r = (this).thisFile;
        }
        BigInteger _hi0 = new BigInteger((_0_p).Count);
        for (BigInteger _2_i = BigInteger.Zero; _2_i < _hi0; _2_i++) {
          Dafny.ISequence<Dafny.Rune> _3_name;
          _3_name = ((_0_p).Select(_2_i));
          if (escape) {
            _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName(_3_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4_modules = _let_tmp_rhs0.dtor__0;
            Dafny.ISequence<Dafny.Rune> _5_finalName = _let_tmp_rhs0.dtor__1;
            BigInteger _hi1 = new BigInteger((_4_modules).Count);
            for (BigInteger _6_j = BigInteger.Zero; _6_j < _hi1; _6_j++) {
              r = (r).MSel(Defs.__default.escapeName(((_4_modules).Select(_6_j))));
            }
            r = (r).MSel(Defs.__default.escapeName(_5_finalName));
          } else {
            r = (r).MSels(Defs.__default.SplitRustPathElement(Defs.__default.ReplaceDotByDoubleColon((_3_name)), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
          }
        }
      }
      return r;
    }
    public RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _0_p;
      RAST._IPath _out0;
      _out0 = (this).GenPath(p, true);
      _0_p = _out0;
      t = (_0_p).AsType();
      return t;
    }
    public RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _0_p;
      RAST._IPath _out0;
      _out0 = (this).GenPath(p, escape);
      _0_p = _out0;
      e = (_0_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger((args).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        RAST._IType _1_genTp;
        RAST._IType _out0;
        _out0 = (this).GenType((args).Select(_0_i), genTypeContext);
        _1_genTp = _out0;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1_genTp));
      }
      return s;
    }
    public RAST._IType GenType(DAST._IType c, bool genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source0 = c;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType _0_resolved = _source0.dtor_resolved;
          {
            RAST._IType _1_t;
            RAST._IType _out0;
            _out0 = (this).GenPathType((_0_resolved).dtor_path);
            _1_t = _out0;
            Dafny.ISequence<RAST._IType> _2_typeArgs;
            Dafny.ISequence<RAST._IType> _out1;
            _out1 = (this).GenTypeArgs((_0_resolved).dtor_typeArgs, false);
            _2_typeArgs = _out1;
            if ((new BigInteger((_2_typeArgs).Count)).Sign == 1) {
              s = RAST.Type.create_TypeApp(_1_t, _2_typeArgs);
            } else {
              s = _1_t;
            }
            DAST._IResolvedTypeBase _source1 = (_0_resolved).dtor_kind;
            {
              if (_source1.is_Class) {
                {
                  s = (this).Object(s);
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_Datatype) {
                {
                  if (Defs.__default.IsRcWrapped((_0_resolved).dtor_attributes)) {
                    s = Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>((this).rc)(s);
                  }
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_Trait) {
                DAST._ITraitType traitType0 = _source1.dtor_traitType;
                if (traitType0.is_GeneralTrait) {
                  {
                    if (!((genTypeContext))) {
                      s = RAST.__default.Box(RAST.Type.create_DynType(s));
                    }
                  }
                  goto after_match1;
                }
              }
            }
            {
              if (_source1.is_Trait) {
                DAST._ITraitType traitType1 = _source1.dtor_traitType;
                if (traitType1.is_ObjectTrait) {
                  {
                    if (((_0_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                      s = (this).AnyTrait;
                    }
                    if (!((genTypeContext))) {
                      s = (this).Object(RAST.Type.create_DynType(s));
                    }
                  }
                  goto after_match1;
                }
              }
            }
            {
              if (_source1.is_SynonymType) {
                DAST._IType _3_base = _source1.dtor_baseType;
                {
                  RAST._IType _4_underlying;
                  RAST._IType _out2;
                  _out2 = (this).GenType(_3_base, Defs.GenTypeContext.@default());
                  _4_underlying = _out2;
                  s = RAST.Type.create_TSynonym(s, _4_underlying);
                }
                goto after_match1;
              }
            }
            {
              DAST._IType _5_base = _source1.dtor_baseType;
              DAST._INewtypeRange _6_range = _source1.dtor_range;
              bool _7_erased = _source1.dtor_erase;
              {
                if (_7_erased) {
                  Std.Wrappers._IOption<RAST._IType> _8_unwrappedType;
                  _8_unwrappedType = Defs.__default.NewtypeRangeToUnwrappedBoundedRustType(_5_base, _6_range);
                  if ((_8_unwrappedType).is_Some) {
                    s = (_8_unwrappedType).dtor_value;
                  } else {
                    RAST._IType _9_unwrappedType;
                    RAST._IType _out3;
                    _out3 = (this).GenType(_5_base, Defs.GenTypeContext.@default());
                    _9_unwrappedType = _out3;
                    s = _9_unwrappedType;
                  }
                } else if (Defs.__default.IsNewtypeCopy(_6_range)) {
                  s = RAST.Type.create_TMetaData(s, true, (_6_range).CanOverflow());
                }
              }
            }
          after_match1: ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Object) {
          {
            s = (this).AnyTrait;
            if (!((genTypeContext))) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IType> _10_types = _source0.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IType> _11_args;
            _11_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _12_i;
            _12_i = BigInteger.Zero;
            while ((_12_i) < (new BigInteger((_10_types).Count))) {
              RAST._IType _13_generated;
              RAST._IType _out4;
              _out4 = (this).GenType((_10_types).Select(_12_i), false);
              _13_generated = _out4;
              _11_args = Dafny.Sequence<RAST._IType>.Concat(_11_args, Dafny.Sequence<RAST._IType>.FromElements(_13_generated));
              _12_i = (_12_i) + (BigInteger.One);
            }
            if ((new BigInteger((_10_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              s = RAST.Type.create_TupleType(_11_args);
            } else {
              s = RAST.__default.SystemTupleType(_11_args);
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Array) {
          DAST._IType _14_element = _source0.dtor_element;
          BigInteger _15_dims = _source0.dtor_dims;
          {
            if ((_15_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _16_elem;
              RAST._IType _out5;
              _out5 = (this).GenType(_14_element, false);
              _16_elem = _out5;
              if ((_15_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_16_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _17_n;
                _17_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_15_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_17_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_16_elem));
                s = (this).Object(s);
              }
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Seq) {
          DAST._IType _18_element = _source0.dtor_element;
          {
            RAST._IType _19_elem;
            RAST._IType _out6;
            _out6 = (this).GenType(_18_element, false);
            _19_elem = _out6;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_19_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Set) {
          DAST._IType _20_element = _source0.dtor_element;
          {
            RAST._IType _21_elem;
            RAST._IType _out7;
            _out7 = (this).GenType(_20_element, false);
            _21_elem = _out7;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_21_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Multiset) {
          DAST._IType _22_element = _source0.dtor_element;
          {
            RAST._IType _23_elem;
            RAST._IType _out8;
            _out8 = (this).GenType(_22_element, false);
            _23_elem = _out8;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_23_elem));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Map) {
          DAST._IType _24_key = _source0.dtor_key;
          DAST._IType _25_value = _source0.dtor_value;
          {
            RAST._IType _26_keyType;
            RAST._IType _out9;
            _out9 = (this).GenType(_24_key, false);
            _26_keyType = _out9;
            RAST._IType _27_valueType;
            RAST._IType _out10;
            _out10 = (this).GenType(_25_value, genTypeContext);
            _27_valueType = _out10;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_26_keyType, _27_valueType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _28_key = _source0.dtor_key;
          DAST._IType _29_value = _source0.dtor_value;
          {
            RAST._IType _30_keyType;
            RAST._IType _out11;
            _out11 = (this).GenType(_28_key, false);
            _30_keyType = _out11;
            RAST._IType _31_valueType;
            RAST._IType _out12;
            _out12 = (this).GenType(_29_value, genTypeContext);
            _31_valueType = _out12;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_30_keyType, _31_valueType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _32_elem = _source0.dtor_element;
          {
            RAST._IType _33_elemType;
            RAST._IType _out13;
            _out13 = (this).GenType(_32_elem, false);
            _33_elemType = _out13;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_33_elemType));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Arrow) {
          Dafny.ISequence<DAST._IType> _34_args = _source0.dtor_args;
          DAST._IType _35_result = _source0.dtor_result;
          {
            Dafny.ISequence<RAST._IType> _36_argTypes;
            _36_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _37_i;
            _37_i = BigInteger.Zero;
            while ((_37_i) < (new BigInteger((_34_args).Count))) {
              RAST._IType _38_generated;
              RAST._IType _out14;
              _out14 = (this).GenType((_34_args).Select(_37_i), false);
              _38_generated = _out14;
              _36_argTypes = Dafny.Sequence<RAST._IType>.Concat(_36_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_38_generated)));
              _37_i = (_37_i) + (BigInteger.One);
            }
            RAST._IType _39_resultType;
            RAST._IType _out15;
            _out15 = (this).GenType(_35_result, Defs.GenTypeContext.@default());
            _39_resultType = _out15;
            RAST._IType _40_fnType;
            _40_fnType = RAST.Type.create_DynType(RAST.Type.create_FnType(_36_argTypes, _39_resultType));
            if (((this).syncType).is_Sync) {
              _40_fnType = RAST.Type.create_IntersectionType(_40_fnType, (this).SyncSendType);
            }
            s = Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>((this).rc)(_40_fnType);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source0.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _41_name = _h90;
          s = RAST.Type.create_TIdentifier(Defs.__default.escapeName(_41_name));
          goto after_match0;
        }
      }
      {
        if (_source0.is_Primitive) {
          DAST._IPrimitive _42_p = _source0.dtor_Primitive_a0;
          {
            DAST._IPrimitive _source2 = _42_p;
            {
              if (_source2.is_Int) {
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
                goto after_match2;
              }
            }
            {
              if (_source2.is_Real) {
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsType();
                goto after_match2;
              }
            }
            {
              if (_source2.is_String) {
                s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType()));
                goto after_match2;
              }
            }
            {
              if (_source2.is_Native) {
                s = RAST.Type.create_USIZE();
                goto after_match2;
              }
            }
            {
              if (_source2.is_Bool) {
                s = RAST.Type.create_Bool();
                goto after_match2;
              }
            }
            {
              s = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType();
            }
          after_match2: ;
          }
          goto after_match0;
        }
      }
      {
        Dafny.ISequence<Dafny.Rune> _43_v = _source0.dtor_Passthrough_a0;
        s = RAST.__default.RawType(_43_v);
      }
    after_match0: ;
      return s;
    }
    public bool EnclosingIsTrait(DAST._IType tpe) {
      return ((tpe).is_UserDefined) && ((((tpe).dtor_resolved).dtor_kind).is_Trait);
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _hi0 = new BigInteger((body).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DAST._IMethod _source0 = (body).Select(_0_i);
        {
          DAST._IMethod _1_m = _source0;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source1 = (_1_m).dtor_overridingPath;
            {
              if (_source1.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_p = _source1.dtor_value;
                {
                  Dafny.ISequence<RAST._IImplMember> _3_existing;
                  _3_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_2_p)) {
                    _3_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_2_p);
                  }
                  if (((new BigInteger(((_1_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _4_genMethod;
                  RAST._IImplMember _out0;
                  _out0 = (this).GenMethod(_1_m, true, enclosingType, enclosingTypeParams);
                  _4_genMethod = _out0;
                  _3_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_3_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_4_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_2_p, _3_existing)));
                }
                goto after_match1;
              }
            }
            {
              {
                RAST._IImplMember _5_generated;
                RAST._IImplMember _out1;
                _out1 = (this).GenMethod(_1_m, forTrait, enclosingType, enclosingTypeParams);
                _5_generated = _out1;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_5_generated));
              }
            }
          after_match1: ;
          }
        }
      after_match0: ;
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IFormal> inheritedParams, bool forLambda)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi0 = new BigInteger((@params).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DAST._IFormal _1_param;
        _1_param = (@params).Select(_0_i);
        DAST._IFormal _2_inheritedParam;
        if ((_0_i) < (new BigInteger((inheritedParams).Count))) {
          _2_inheritedParam = (inheritedParams).Select(_0_i);
        } else {
          _2_inheritedParam = _1_param;
        }
        RAST._IType _3_paramType;
        RAST._IType _out0;
        _out0 = (this).GenType((_1_param).dtor_typ, Defs.GenTypeContext.@default());
        _3_paramType = _out0;
        RAST._IType _4_inheritedParamType;
        RAST._IType _out1;
        _out1 = (this).GenType((_2_inheritedParam).dtor_typ, Defs.GenTypeContext.@default());
        _4_inheritedParamType = _out1;
        if (((!((_4_inheritedParamType).CanReadWithoutClone())) || (forLambda)) && (!((_1_param).dtor_attributes).Contains(Defs.__default.AttributeOwned))) {
          _3_paramType = RAST.Type.create_Borrowed(_3_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Defs.__default.escapeVar((_1_param).dtor_name), _3_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _0_params;
      Dafny.ISequence<RAST._IFormal> _out0;
      _out0 = (this).GenParams((m).dtor_params, (m).dtor_inheritedParams, false);
      _0_params = _out0;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1_paramNames;
      _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2_paramTypes;
      _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _3_paramI = BigInteger.Zero; _3_paramI < _hi0; _3_paramI++) {
        DAST._IFormal _4_dafny__formal;
        _4_dafny__formal = ((m).dtor_params).Select(_3_paramI);
        RAST._IFormal _5_formal;
        _5_formal = (_0_params).Select(_3_paramI);
        Dafny.ISequence<Dafny.Rune> _6_name;
        _6_name = (_5_formal).dtor_name;
        _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_6_name));
        _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2_paramTypes, _6_name, (_5_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _7_fnName;
      _7_fnName = Defs.__default.escapeName((m).dtor_name);
      Defs._ISelfInfo _8_selfIdent;
      _8_selfIdent = Defs.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _9_selfId;
        _9_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _9_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv0 = enclosingTypeParams;
        DAST._IType _10_instanceType;
        DAST._IType _source0 = enclosingType;
        {
          if (_source0.is_UserDefined) {
            DAST._IResolvedType _11_r = _source0.dtor_resolved;
            _10_instanceType = DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_11_r, _pat_let72_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let72_0, _12_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv0, _pat_let73_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let73_0, _13_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_12_dt__update__tmp_h0).dtor_path, _13_dt__update_htypeArgs_h0, (_12_dt__update__tmp_h0).dtor_kind, (_12_dt__update__tmp_h0).dtor_attributes, (_12_dt__update__tmp_h0).dtor_properMethods, (_12_dt__update__tmp_h0).dtor_extendedTypes))))));
            goto after_match0;
          }
        }
        {
          _10_instanceType = enclosingType;
        }
      after_match0: ;
        if (forTrait) {
          RAST._IFormal _14_selfFormal;
          _14_selfFormal = RAST.Formal.selfBorrowed;
          _0_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_14_selfFormal), _0_params);
        } else {
          RAST._IType _15_tpe;
          RAST._IType _out1;
          _out1 = (this).GenType(_10_instanceType, Defs.GenTypeContext.@default());
          _15_tpe = _out1;
          if ((_9_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            if (((this).pointerType).is_RcMut) {
              _15_tpe = RAST.Type.create_Borrowed(_15_tpe);
            }
          } else if ((_9_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_15_tpe).IsObjectOrPointer()) {
              _15_tpe = RAST.__default.SelfBorrowed;
            } else {
              if (((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Newtype)) && (Defs.__default.IsNewtypeCopy((((enclosingType).dtor_resolved).dtor_kind).dtor_range))) && (!(forTrait))) {
                _15_tpe = RAST.Type.create_TMetaData(RAST.__default.SelfOwned, true, ((((enclosingType).dtor_resolved).dtor_kind).dtor_range).CanOverflow());
              } else {
                _15_tpe = RAST.__default.SelfBorrowed;
              }
            }
          }
          RAST._IFormal _16_formal;
          _16_formal = RAST.Formal.create(_9_selfId, _15_tpe);
          _0_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_16_formal), _0_params);
          Dafny.ISequence<Dafny.Rune> _17_name;
          _17_name = (_16_formal).dtor_name;
          _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_17_name), _1_paramNames);
          _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2_paramTypes, _17_name, (_16_formal).dtor_tpe);
        }
        _8_selfIdent = Defs.SelfInfo.create_ThisTyped(_9_selfId, _10_instanceType);
      }
      Dafny.ISequence<RAST._IType> _18_retTypeArgs;
      _18_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _19_typeI;
      _19_typeI = BigInteger.Zero;
      while ((_19_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _20_typeExpr;
        RAST._IType _out2;
        _out2 = (this).GenType(((m).dtor_outTypes).Select(_19_typeI), Defs.GenTypeContext.@default());
        _20_typeExpr = _out2;
        _18_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_18_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_20_typeExpr));
        _19_typeI = (_19_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _21_visibility;
      if (forTrait) {
        _21_visibility = RAST.Visibility.create_PRIV();
      } else {
        _21_visibility = RAST.Visibility.create_PUB();
      }
      Dafny.ISequence<DAST._ITypeArgDecl> _22_typeParamsFiltered;
      _22_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi1 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _23_typeParamI = BigInteger.Zero; _23_typeParamI < _hi1; _23_typeParamI++) {
        DAST._ITypeArgDecl _24_typeParam;
        _24_typeParam = ((m).dtor_typeParams).Select(_23_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_24_typeParam).dtor_name)))) {
          _22_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_22_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_24_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _25_typeParams;
      _25_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_22_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi2 = new BigInteger((_22_typeParamsFiltered).Count);
        for (BigInteger _26_i = BigInteger.Zero; _26_i < _hi2; _26_i++) {
          DAST._IType _27_typeArg;
          RAST._ITypeParamDecl _28_rTypeParamDecl;
          DAST._IType _out3;
          RAST._ITypeParamDecl _out4;
          (this).GenTypeParam((_22_typeParamsFiltered).Select(_26_i), out _out3, out _out4);
          _27_typeArg = _out3;
          _28_rTypeParamDecl = _out4;
          RAST._ITypeParamDecl _29_dt__update__tmp_h1 = _28_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _30_dt__update_hconstraints_h0 = (_28_rTypeParamDecl).dtor_constraints;
          _28_rTypeParamDecl = RAST.TypeParamDecl.create((_29_dt__update__tmp_h1).dtor_name, _30_dt__update_hconstraints_h0);
          _25_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_25_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_28_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _31_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      Defs._IEnvironment _32_env = Defs.Environment.Default();
      RAST._IExpr _33_preBody;
      _33_preBody = (this).InitEmptyExpr();
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _34_preAssignNames;
      _34_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _35_preAssignTypes;
      _35_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _36_earlyReturn;
        _36_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source1 = (m).dtor_outVars;
        {
          if (_source1.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _37_outVars = _source1.dtor_value;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _36_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi3 = new BigInteger((_37_outVars).Count);
                for (BigInteger _38_outI = BigInteger.Zero; _38_outI < _hi3; _38_outI++) {
                  Dafny.ISequence<Dafny.Rune> _39_outVar;
                  _39_outVar = (_37_outVars).Select(_38_outI);
                  Dafny.ISequence<Dafny.Rune> _40_outName;
                  _40_outName = Defs.__default.escapeVar(_39_outVar);
                  Dafny.ISequence<Dafny.Rune> _41_tracker__name;
                  _41_tracker__name = Defs.__default.AddAssignedPrefix(_40_outName);
                  _34_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_34_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_41_tracker__name));
                  _35_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_35_preAssignTypes, _41_tracker__name, RAST.Type.create_Bool());
                  _33_preBody = (_33_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _41_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _42_tupleArgs;
                _42_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                bool _43_isTailRecursive;
                _43_isTailRecursive = ((new BigInteger(((m).dtor_body).Count)) == (BigInteger.One)) && ((((m).dtor_body).Select(BigInteger.Zero)).is_TailRecursive);
                BigInteger _hi4 = new BigInteger((_37_outVars).Count);
                for (BigInteger _44_outI = BigInteger.Zero; _44_outI < _hi4; _44_outI++) {
                  Dafny.ISequence<Dafny.Rune> _45_outVar;
                  _45_outVar = (_37_outVars).Select(_44_outI);
                  DAST._IType _46_outTyp;
                  _46_outTyp = ((m).dtor_outTypes).Select(_44_outI);
                  RAST._IType _47_outType;
                  RAST._IType _out5;
                  _out5 = (this).GenType(_46_outTyp, Defs.GenTypeContext.@default());
                  _47_outType = _out5;
                  Dafny.ISequence<Dafny.Rune> _48_outName;
                  _48_outName = Defs.__default.escapeVar(_45_outVar);
                  if (!(_43_isTailRecursive)) {
                    _1_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_48_outName));
                    RAST._IType _49_outMaybeType;
                    if ((_47_outType).CanReadWithoutClone()) {
                      _49_outMaybeType = _47_outType;
                    } else {
                      _49_outMaybeType = RAST.__default.MaybePlaceboType(_47_outType);
                    }
                    _2_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2_paramTypes, _48_outName, _49_outMaybeType);
                  }
                  _42_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_42_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_48_outName));
                }
                _36_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_42_tupleArgs);
              }
            }
            goto after_match1;
          }
        }
        {
        }
      after_match1: ;
        _32_env = Defs.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_34_preAssignNames, _1_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_35_preAssignTypes, _2_paramTypes), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements());
        RAST._IExpr _50_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _51___v14;
        Defs._IEnvironment _52___v15;
        RAST._IExpr _out6;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
        Defs._IEnvironment _out8;
        (this).GenStmts((m).dtor_body, _8_selfIdent, _32_env, true, _36_earlyReturn, out _out6, out _out7, out _out8);
        _50_body = _out6;
        _51___v14 = _out7;
        _52___v15 = _out8;
        _31_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_33_preBody).Then(_50_body));
      } else {
        _32_env = Defs.Environment.create(_1_paramNames, _2_paramTypes, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _31_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl((m).dtor_docString, RAST.__default.NoAttr, _21_visibility, RAST.Fn.create(_7_fnName, _25_typeParams, _0_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_18_retTypeArgs).Count)) == (BigInteger.One)) ? ((_18_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_18_retTypeArgs)))), _31_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out Defs._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = Defs.Environment.Default();
      generated = (this).InitEmptyExpr();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _0_declarations;
      _0_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1_i;
      _1_i = BigInteger.Zero;
      newEnv = env;
      while ((_1_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _2_stmt;
        _2_stmt = (stmts).Select(_1_i);
        if (((((((_2_stmt).is_DeclareVar) && (((_2_stmt).dtor_maybeValue).is_None)) && (((_1_i) + (BigInteger.One)) < (new BigInteger((stmts).Count)))) && (((stmts).Select((_1_i) + (BigInteger.One))).is_Assign)) && ((((stmts).Select((_1_i) + (BigInteger.One))).dtor_lhs).is_Ident)) && (object.Equals((((stmts).Select((_1_i) + (BigInteger.One))).dtor_lhs).dtor_ident, (_2_stmt).dtor_name))) {
          Dafny.ISequence<Dafny.Rune> _3_name;
          _3_name = (_2_stmt).dtor_name;
          DAST._IType _4_typ;
          _4_typ = (_2_stmt).dtor_typ;
          RAST._IExpr _5_stmtExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _6_recIdents;
          Defs._IEnvironment _7_newEnv2;
          RAST._IExpr _out0;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1;
          Defs._IEnvironment _out2;
          (this).GenDeclareVarAssign(_3_name, _4_typ, ((stmts).Select((_1_i) + (BigInteger.One))).dtor_value, selfIdent, newEnv, out _out0, out _out1, out _out2);
          _5_stmtExpr = _out0;
          _6_recIdents = _out1;
          _7_newEnv2 = _out2;
          newEnv = _7_newEnv2;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_6_recIdents, _0_declarations));
          _0_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_0_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Defs.__default.escapeVar(_3_name)));
          generated = (generated).Then(_5_stmtExpr);
          _1_i = (_1_i) + (new BigInteger(2));
        } else {
          DAST._IStatement _source0 = _2_stmt;
          {
            if (_source0.is_DeclareVar) {
              Dafny.ISequence<Dafny.Rune> _8_name = _source0.dtor_name;
              DAST._IType _9_optType = _source0.dtor_typ;
              Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source0.dtor_maybeValue;
              if (maybeValue0.is_None) {
                Defs._IAssignmentStatus _10_laterAssignmentStatus;
                _10_laterAssignmentStatus = Defs.__default.DetectAssignmentStatus((stmts).Drop((_1_i) + (BigInteger.One)), _8_name);
                newEnv = (newEnv).AddAssignmentStatus(Defs.__default.escapeVar(_8_name), _10_laterAssignmentStatus);
                goto after_match0;
              }
            }
          }
          {
            if (_source0.is_DeclareVar) {
              Dafny.ISequence<Dafny.Rune> _11_name = _source0.dtor_name;
              DAST._IType _12_optType = _source0.dtor_typ;
              Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source0.dtor_maybeValue;
              if (maybeValue1.is_Some) {
                DAST._IExpression value0 = maybeValue1.dtor_value;
                if (value0.is_InitializationValue) {
                  DAST._IType _13_typ = value0.dtor_typ;
                  RAST._IType _14_tpe;
                  RAST._IType _out3;
                  _out3 = (this).GenType(_13_typ, Defs.GenTypeContext.@default());
                  _14_tpe = _out3;
                  Dafny.ISequence<Dafny.Rune> _15_varName;
                  _15_varName = Defs.__default.escapeVar(_11_name);
                  Defs._IAssignmentStatus _16_laterAssignmentStatus;
                  _16_laterAssignmentStatus = Defs.__default.DetectAssignmentStatus((stmts).Drop((_1_i) + (BigInteger.One)), _11_name);
                  newEnv = (newEnv).AddAssignmentStatus(_15_varName, _16_laterAssignmentStatus);
                  goto after_match0;
                }
              }
            }
          }
          {
          }
        after_match0: ;
          RAST._IExpr _17_stmtExpr;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _18_recIdents;
          Defs._IEnvironment _19_newEnv2;
          RAST._IExpr _out4;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
          Defs._IEnvironment _out6;
          (this).GenStmt(_2_stmt, selfIdent, newEnv, (isLast) && ((_1_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out4, out _out5, out _out6);
          _17_stmtExpr = _out4;
          _18_recIdents = _out5;
          _19_newEnv2 = _out6;
          newEnv = _19_newEnv2;
          DAST._IStatement _source1 = _2_stmt;
          {
            if (_source1.is_DeclareVar) {
              Dafny.ISequence<Dafny.Rune> _20_name = _source1.dtor_name;
              {
                _0_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_0_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Defs.__default.escapeVar(_20_name)));
              }
              goto after_match1;
            }
          }
          {
          }
        after_match1: ;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_18_recIdents, _0_declarations));
          generated = (generated).Then(_17_stmtExpr);
          if ((_17_stmtExpr).is_Return) {
            goto after_0;
          }
          _1_i = (_1_i) + (BigInteger.One);
        }
      continue_0: ;
      }
    after_0: ;
    }
    public void GenDeclareVarAssign(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, DAST._IExpression rhs, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out Defs._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = Defs.Environment.Default();
      RAST._IType _0_tpe;
      RAST._IType _out0;
      _out0 = (this).GenType(typ, Defs.GenTypeContext.@default());
      _0_tpe = _out0;
      Dafny.ISequence<Dafny.Rune> _1_varName;
      _1_varName = Defs.__default.escapeVar(name);
      RAST._IExpr _2_exprRhs = RAST.Expr.Default();
      if (((rhs).is_InitializationValue) && ((_0_tpe).IsObjectOrPointer())) {
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        if ((rhs).is_NewUninitArray) {
          _0_tpe = (_0_tpe).TypeAtInitialization();
        } else {
          _0_tpe = _0_tpe;
        }
        _2_exprRhs = (_0_tpe).ToNullExpr();
      } else {
        RAST._IExpr _3_expr = RAST.Expr.Default();
        Defs._IOwnership _4_exprOwnership = Defs.Ownership.Default();
        RAST._IExpr _out1;
        Defs._IOwnership _out2;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
        (this).GenExpr(rhs, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out1, out _out2, out _out3);
        _3_expr = _out1;
        _4_exprOwnership = _out2;
        readIdents = _out3;
        if ((rhs).is_NewUninitArray) {
          _0_tpe = (_0_tpe).TypeAtInitialization();
        } else {
          _0_tpe = _0_tpe;
        }
        _2_exprRhs = _3_expr;
      }
      generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_0_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2_exprRhs));
      newEnv = (env).AddAssigned(_1_varName, _0_tpe);
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out Defs._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = Defs.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source0 = lhs;
      {
        if (_source0.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _0_id = _source0.dtor_ident;
          {
            Dafny.ISequence<Dafny.Rune> _1_idRust;
            _1_idRust = Defs.__default.escapeVar(_0_id);
            if (((env).IsBorrowed(_1_idRust)) || ((env).IsBorrowedMut(_1_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1_idRust);
            needsIIFE = false;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Select) {
          DAST._IExpression _2_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _3_field = _source0.dtor_field;
          bool _4_isConstant = _source0.dtor_isConstant;
          {
            Dafny.ISequence<Dafny.Rune> _5_fieldName;
            _5_fieldName = Defs.__default.escapeVar(_3_field);
            RAST._IExpr _6_onExpr;
            Defs._IOwnership _7_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _8_recIdents;
            RAST._IExpr _out0;
            Defs._IOwnership _out1;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
            (this).GenExpr(_2_on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out0, out _out1, out _out2);
            _6_onExpr = _out0;
            _7_onOwned = _out1;
            _8_recIdents = _out2;
            RAST._IExpr _source1 = _6_onExpr;
            {
              bool disjunctiveMatch0 = false;
              if (_source1.is_Call) {
                RAST._IExpr obj0 = _source1.dtor_obj;
                if (obj0.is_Select) {
                  RAST._IExpr obj1 = obj0.dtor_obj;
                  if (obj1.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name0 = obj1.dtor_name;
                    if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name1 = obj0.dtor_name;
                      if (object.Equals(name1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch0 = true;
                      }
                    }
                  }
                }
              }
              if (_source1.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name2 = _source1.dtor_name;
                if (object.Equals(name2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch0 = true;
                }
              }
              if (_source1.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op10 = _source1.dtor_op1;
                if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying0 = _source1.dtor_underlying;
                  if (underlying0.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name3 = underlying0.dtor_name;
                    if (object.Equals(name3, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch0 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch0) {
                Dafny.ISequence<Dafny.Rune> _9_isAssignedVar;
                _9_isAssignedVar = Defs.__default.AddAssignedPrefix(_5_fieldName);
                if (((newEnv).dtor_names).Contains(_9_isAssignedVar)) {
                  Dafny.ISequence<Dafny.Rune> _10_update__field__uninit;
                  if (_4_isConstant) {
                    _10_update__field__uninit = (this).update__field__uninit__macro;
                  } else {
                    _10_update__field__uninit = (this).update__field__mut__uninit__macro;
                  }
                  generated = (((RAST.__default.dafny__runtime).MSel(_10_update__field__uninit)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_5_fieldName), RAST.Expr.create_Identifier(_9_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_9_isAssignedVar);
                } else {
                  generated = ((this).modify__mutable__field__macro).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((((this).read__macro).Apply1((this).thisInConstructor)).Sel(_5_fieldName), rhs));
                }
                goto after_match1;
              }
            }
            {
              if (!object.Equals(_6_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _6_onExpr = ((this).read__macro).Apply1(_6_onExpr);
              }
              generated = ((this).modify__mutable__field__macro).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((_6_onExpr).Sel(_5_fieldName), rhs));
            }
          after_match1: ;
            readIdents = _8_recIdents;
            needsIIFE = false;
          }
          goto after_match0;
        }
      }
      {
        DAST._IExpression _11_on = _source0.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _12_indices = _source0.dtor_indices;
        {
          RAST._IExpr _13_onExpr;
          Defs._IOwnership _14_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _15_recIdents;
          RAST._IExpr _out3;
          Defs._IOwnership _out4;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
          (this).GenExpr(_11_on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out3, out _out4, out _out5);
          _13_onExpr = _out3;
          _14_onOwned = _out4;
          _15_recIdents = _out5;
          readIdents = _15_recIdents;
          _13_onExpr = ((this).modify__macro).Apply1(_13_onExpr);
          RAST._IExpr _16_r;
          _16_r = (this).InitEmptyExpr();
          Dafny.ISequence<RAST._IExpr> _17_indicesExpr;
          _17_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi0 = new BigInteger((_12_indices).Count);
          for (BigInteger _18_i = BigInteger.Zero; _18_i < _hi0; _18_i++) {
            RAST._IExpr _19_idx;
            Defs._IOwnership _20___v23;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _21_recIdentsIdx;
            RAST._IExpr _out6;
            Defs._IOwnership _out7;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out8;
            (this).GenExpr((_12_indices).Select(_18_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out6, out _out7, out _out8);
            _19_idx = _out6;
            _20___v23 = _out7;
            _21_recIdentsIdx = _out8;
            Dafny.ISequence<Dafny.Rune> _22_varName;
            _22_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_18_i));
            _17_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_17_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_22_varName)));
            _16_r = (_16_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _22_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_19_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _21_recIdentsIdx);
          }
          if ((new BigInteger((_12_indices).Count)) > (BigInteger.One)) {
            _13_onExpr = (_13_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          generated = (_16_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_13_onExpr, _17_indicesExpr)), rhs));
          needsIIFE = true;
        }
      }
    after_match0: ;
    }
    public RAST._IExpr FromGeneralBorrowToSelfBorrow(RAST._IExpr onExpr, Defs._IOwnership onExprOwnership, Defs._IEnvironment env)
    {
      if (((onExpr).is_Identifier) && ((env).NeedsAsRefForBorrow((onExpr).dtor_name))) {
        return ((onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0();
      } else if (((object.Equals(onExpr, RAST.__default.self)) || (object.Equals(onExpr, (this).rcDatatypeThis))) || (object.Equals(onExpr, (this).borrowedRcDatatypeThis))) {
        return RAST.__default.self;
      } else if ((onExprOwnership).is_OwnershipBorrowed) {
        return (((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply1(onExpr);
      } else {
        return onExpr;
      }
    }
    public void GenCall(DAST._IExpression @on, Defs._ISelfInfo selfIdent, DAST._ICallName name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, Defs._IEnvironment env, out RAST._IExpr r, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      Dafny.ISequence<RAST._IExpr> _0_argExprs;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1_recIdents;
      Dafny.ISequence<RAST._IType> _2_typeExprs;
      Std.Wrappers._IOption<DAST._IResolvedType> _3_fullNameQualifier;
      Dafny.ISequence<RAST._IExpr> _out0;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1;
      Dafny.ISequence<RAST._IType> _out2;
      Std.Wrappers._IOption<DAST._IResolvedType> _out3;
      (this).GenArgs(selfIdent, name, typeArgs, args, env, out _out0, out _out1, out _out2, out _out3);
      _0_argExprs = _out0;
      _1_recIdents = _out1;
      _2_typeExprs = _out2;
      _3_fullNameQualifier = _out3;
      readIdents = _1_recIdents;
      if ((((((selfIdent).IsSelf()) && ((name).is_CallName)) && (((name).dtor_receiverArg).is_Some)) && ((new BigInteger((_0_argExprs).Count)).Sign == 1)) && (RAST.__default.IsBorrowUpcastBox((_0_argExprs).Select(BigInteger.Zero)))) {
        _0_argExprs = Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))), (_0_argExprs).Drop(BigInteger.One));
      }
      Std.Wrappers._IOption<DAST._IResolvedType> _source0 = _3_fullNameQualifier;
      {
        if (_source0.is_Some) {
          DAST._IResolvedType value0 = _source0.dtor_value;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4_path = value0.dtor_path;
          Dafny.ISequence<DAST._IType> _5_onTypeArgs = value0.dtor_typeArgs;
          DAST._IResolvedTypeBase _6_base = value0.dtor_kind;
          RAST._IExpr _7_fullPath;
          RAST._IExpr _out4;
          _out4 = (this).GenPathExpr(_4_path, true);
          _7_fullPath = _out4;
          Dafny.ISequence<RAST._IType> _8_onTypeExprs;
          Dafny.ISequence<RAST._IType> _out5;
          _out5 = (this).GenTypeArgs(_5_onTypeArgs, Defs.GenTypeContext.@default());
          _8_onTypeExprs = _out5;
          RAST._IExpr _9_onExpr = RAST.Expr.Default();
          Defs._IOwnership _10_recOwnership = Defs.Ownership.Default();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _11_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
          if ((((_6_base).is_Trait) && (((_6_base).dtor_traitType).is_ObjectTrait)) || ((_6_base).is_Class)) {
            RAST._IExpr _out6;
            Defs._IOwnership _out7;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out8;
            (this).GenExpr(@on, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out6, out _out7, out _out8);
            _9_onExpr = _out6;
            _10_recOwnership = _out7;
            _11_recIdents = _out8;
            _9_onExpr = ((this).read__macro).Apply1(_9_onExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _11_recIdents);
          } else if (((_6_base).is_Trait) && (((_6_base).dtor_traitType).is_GeneralTrait)) {
            if ((@on).IsThisUpcast()) {
              _9_onExpr = RAST.__default.self;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")));
            } else {
              RAST._IExpr _out9;
              Defs._IOwnership _out10;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out11;
              (this).GenExpr(@on, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out9, out _out10, out _out11);
              _9_onExpr = _out9;
              _10_recOwnership = _out10;
              _11_recIdents = _out11;
              _9_onExpr = (this).FromGeneralBorrowToSelfBorrow(_9_onExpr, _10_recOwnership, env);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _11_recIdents);
            }
          } else if (((_6_base).is_Newtype) && (Defs.__default.IsNewtypeCopy((_6_base).dtor_range))) {
            RAST._IExpr _out12;
            Defs._IOwnership _out13;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out14;
            (this).GenExpr(@on, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out12, out _out13, out _out14);
            _9_onExpr = _out12;
            _10_recOwnership = _out13;
            _11_recIdents = _out14;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _11_recIdents);
          } else {
            RAST._IExpr _out15;
            Defs._IOwnership _out16;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out17;
            (this).GenExpr(@on, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out15, out _out16, out _out17);
            _9_onExpr = _out15;
            _10_recOwnership = _out16;
            _11_recIdents = _out17;
            _9_onExpr = (this).FromGeneralBorrowToSelfBorrow(_9_onExpr, _10_recOwnership, env);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _11_recIdents);
          }
          r = ((((_7_fullPath).ApplyType(_8_onTypeExprs)).FSel(Defs.__default.escapeName((name).dtor_name))).ApplyType(_2_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_9_onExpr), _0_argExprs));
          goto after_match0;
        }
      }
      {
        RAST._IExpr _12_onExpr = RAST.Expr.Default();
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _13_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
        Defs._IOwnership _14_dummy = Defs.Ownership.Default();
        if ((@on).IsThisUpcast()) {
          _12_onExpr = RAST.__default.self;
          _13_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"));
        } else {
          RAST._IExpr _out18;
          Defs._IOwnership _out19;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out20;
          (this).GenExpr(@on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out18, out _out19, out _out20);
          _12_onExpr = _out18;
          _14_dummy = _out19;
          _13_recIdents = _out20;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _13_recIdents);
        Dafny.ISequence<Dafny.Rune> _15_renderedName;
        _15_renderedName = (this).GetMethodName(@on, name);
        DAST._IExpression _source1 = @on;
        {
          bool disjunctiveMatch0 = false;
          if (_source1.is_Companion) {
            disjunctiveMatch0 = true;
          }
          if (_source1.is_ExternCompanion) {
            disjunctiveMatch0 = true;
          }
          if (disjunctiveMatch0) {
            {
              _12_onExpr = (_12_onExpr).FSel(_15_renderedName);
            }
            goto after_match1;
          }
        }
        {
          {
            if (!object.Equals(_12_onExpr, RAST.__default.self)) {
              DAST._ICallName _source2 = name;
              {
                if (_source2.is_CallName) {
                  Std.Wrappers._IOption<DAST._IType> onType0 = _source2.dtor_onType;
                  if (onType0.is_Some) {
                    DAST._IType _16_tpe = onType0.dtor_value;
                    RAST._IType _17_typ;
                    RAST._IType _out21;
                    _out21 = (this).GenType(_16_tpe, Defs.GenTypeContext.@default());
                    _17_typ = _out21;
                    if (((_17_typ).IsObjectOrPointer()) && (!object.Equals(_12_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                      _12_onExpr = ((this).read__macro).Apply1(_12_onExpr);
                    }
                    goto after_match2;
                  }
                }
              }
              {
              }
            after_match2: ;
            }
            _12_onExpr = (_12_onExpr).Sel(_15_renderedName);
          }
        }
      after_match1: ;
        r = ((_12_onExpr).ApplyType(_2_typeExprs)).Apply(_0_argExprs);
      }
    after_match0: ;
    }
    public void GenStmt(DAST._IStatement stmt, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out Defs._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = Defs.Environment.Default();
      DAST._IStatement _source0 = stmt;
      {
        if (_source0.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IField> _0_fields = _source0.dtor_fields;
          {
            generated = (this).InitEmptyExpr();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi0 = new BigInteger((_0_fields).Count);
            for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
              DAST._IField _2_field;
              _2_field = (_0_fields).Select(_1_i);
              Dafny.ISequence<Dafny.Rune> _3_fieldName;
              _3_fieldName = Defs.__default.escapeVar(((_2_field).dtor_formal).dtor_name);
              RAST._IType _4_fieldTyp;
              RAST._IType _out0;
              _out0 = (this).GenType(((_2_field).dtor_formal).dtor_typ, Defs.GenTypeContext.@default());
              _4_fieldTyp = _out0;
              Dafny.ISequence<Dafny.Rune> _5_isAssignedVar;
              _5_isAssignedVar = Defs.__default.AddAssignedPrefix(_3_fieldName);
              if (((newEnv).dtor_names).Contains(_5_isAssignedVar)) {
                Dafny.ISequence<Dafny.Rune> _6_panicked;
                _6_panicked = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Field "), _3_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" is not initialized"));
                RAST._IExpr _7_rhs;
                _7_rhs = Defs.__default.UnreachablePanicIfVerified((this).pointerType, _6_panicked);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_5_isAssignedVar));
                Dafny.ISequence<Dafny.Rune> _8_update__if__uninit;
                if ((_2_field).dtor_isConstant) {
                  _8_update__if__uninit = (this).update__field__if__uninit__macro;
                } else {
                  _8_update__if__uninit = (this).update__field__mut__if__uninit__macro;
                }
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel(_8_update__if__uninit)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_3_fieldName), RAST.Expr.create_Identifier(_5_isAssignedVar), _7_rhs)));
                newEnv = (newEnv).RemoveAssigned(_5_isAssignedVar);
              }
            }
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _9_name = _source0.dtor_name;
          DAST._IType _10_typ = _source0.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source0.dtor_maybeValue;
          if (maybeValue0.is_Some) {
            DAST._IExpression _11_expression = maybeValue0.dtor_value;
            {
              RAST._IType _12_tpe;
              RAST._IType _out1;
              _out1 = (this).GenType(_10_typ, Defs.GenTypeContext.@default());
              _12_tpe = _out1;
              Dafny.ISequence<Dafny.Rune> _13_varName;
              _13_varName = Defs.__default.escapeVar(_9_name);
              bool _14_hasCopySemantics;
              _14_hasCopySemantics = (_12_tpe).CanReadWithoutClone();
              if (((_11_expression).is_InitializationValue) && (!(_14_hasCopySemantics))) {
                if ((env).IsAssignmentStatusKnown(_13_varName)) {
                  generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _13_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_12_tpe), Std.Wrappers.Option<RAST._IExpr>.create_None());
                } else {
                  generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _13_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_12_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply0()));
                  _12_tpe = RAST.__default.MaybePlaceboType(_12_tpe);
                }
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_13_varName, _12_tpe);
              } else {
                RAST._IExpr _out2;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
                Defs._IEnvironment _out4;
                (this).GenDeclareVarAssign(_9_name, _10_typ, _11_expression, selfIdent, env, out _out2, out _out3, out _out4);
                generated = _out2;
                readIdents = _out3;
                newEnv = _out4;
                return ;
              }
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _15_name = _source0.dtor_name;
          DAST._IType _16_typ = _source0.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source0.dtor_maybeValue;
          if (maybeValue1.is_None) {
            {
              Dafny.ISequence<Dafny.Rune> _17_varName;
              _17_varName = Defs.__default.escapeVar(_15_name);
              if ((env).IsAssignmentStatusKnown(_17_varName)) {
                RAST._IType _18_tpe;
                RAST._IType _out5;
                _out5 = (this).GenType(_16_typ, Defs.GenTypeContext.@default());
                _18_tpe = _out5;
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _17_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_18_tpe), Std.Wrappers.Option<RAST._IExpr>.create_None());
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_17_varName, _18_tpe);
              } else {
                DAST._IStatement _19_newStmt;
                _19_newStmt = DAST.Statement.create_DeclareVar(_15_name, _16_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_16_typ)));
                RAST._IExpr _out6;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out7;
                Defs._IEnvironment _out8;
                (this).GenStmt(_19_newStmt, selfIdent, env, isLast, earlyReturn, out _out6, out _out7, out _out8);
                generated = _out6;
                readIdents = _out7;
                newEnv = _out8;
              }
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Assign) {
          DAST._IAssignLhs _20_lhs = _source0.dtor_lhs;
          DAST._IExpression _21_expression = _source0.dtor_value;
          {
            RAST._IExpr _22_exprGen;
            Defs._IOwnership _23___v37;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _24_exprIdents;
            RAST._IExpr _out9;
            Defs._IOwnership _out10;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out11;
            (this).GenExpr(_21_expression, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out9, out _out10, out _out11);
            _22_exprGen = _out9;
            _23___v37 = _out10;
            _24_exprIdents = _out11;
            if ((_20_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _25_rustId;
              _25_rustId = Defs.__default.escapeVar((_20_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _26_tpe;
              _26_tpe = (env).GetType(_25_rustId);
              if (((_26_tpe).is_Some) && ((((_26_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _22_exprGen = RAST.__default.MaybePlacebo(_22_exprGen);
              }
            }
            if (((_20_lhs).is_Index) && (((_20_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _27_rustId;
              _27_rustId = Defs.__default.escapeVar(((_20_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _28_tpe;
              _28_tpe = (env).GetType(_27_rustId);
              if (((_28_tpe).is_Some) && ((((_28_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _22_exprGen = RAST.__default.MaybeUninitNew(_22_exprGen);
              }
            }
            RAST._IExpr _29_lhsGen;
            bool _30_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _31_recIdents;
            Defs._IEnvironment _32_resEnv;
            RAST._IExpr _out12;
            bool _out13;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out14;
            Defs._IEnvironment _out15;
            (this).GenAssignLhs(_20_lhs, _22_exprGen, selfIdent, env, out _out12, out _out13, out _out14, out _out15);
            _29_lhsGen = _out12;
            _30_needsIIFE = _out13;
            _31_recIdents = _out14;
            _32_resEnv = _out15;
            generated = _29_lhsGen;
            newEnv = _32_resEnv;
            if (_30_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_31_recIdents, _24_exprIdents);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_If) {
          DAST._IExpression _33_cond = _source0.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _34_thnDafny = _source0.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _35_elsDafny = _source0.dtor_els;
          {
            RAST._IExpr _36_cond;
            Defs._IOwnership _37___v38;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _38_recIdents;
            RAST._IExpr _out16;
            Defs._IOwnership _out17;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out18;
            (this).GenExpr(_33_cond, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out16, out _out17, out _out18);
            _36_cond = _out16;
            _37___v38 = _out17;
            _38_recIdents = _out18;
            Dafny.ISequence<Dafny.Rune> _39_condString;
            _39_condString = (_36_cond)._ToString(Defs.__default.IND);
            readIdents = _38_recIdents;
            RAST._IExpr _40_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _41_thnIdents;
            Defs._IEnvironment _42_thnEnv;
            RAST._IExpr _out19;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out20;
            Defs._IEnvironment _out21;
            (this).GenStmts(_34_thnDafny, selfIdent, env, isLast, earlyReturn, out _out19, out _out20, out _out21);
            _40_thn = _out19;
            _41_thnIdents = _out20;
            _42_thnEnv = _out21;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _41_thnIdents);
            RAST._IExpr _43_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _44_elsIdents;
            Defs._IEnvironment _45_elsEnv;
            RAST._IExpr _out22;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out23;
            Defs._IEnvironment _out24;
            (this).GenStmts(_35_elsDafny, selfIdent, env, isLast, earlyReturn, out _out22, out _out23, out _out24);
            _43_els = _out22;
            _44_elsIdents = _out23;
            _45_elsEnv = _out24;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _44_elsIdents);
            newEnv = (env).Join(_42_thnEnv, _45_elsEnv);
            generated = RAST.Expr.create_IfExpr(_36_cond, _40_thn, _43_els);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _46_lbl = _source0.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _47_body = _source0.dtor_body;
          {
            RAST._IExpr _48_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _49_bodyIdents;
            Defs._IEnvironment _50_env2;
            RAST._IExpr _out25;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out26;
            Defs._IEnvironment _out27;
            (this).GenStmts(_47_body, selfIdent, env, isLast, earlyReturn, out _out25, out _out26, out _out27);
            _48_body = _out25;
            _49_bodyIdents = _out26;
            _50_env2 = _out27;
            readIdents = _49_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _46_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_48_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_While) {
          DAST._IExpression _51_cond = _source0.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _52_body = _source0.dtor_body;
          {
            RAST._IExpr _53_cond;
            Defs._IOwnership _54___v39;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _55_recIdents;
            RAST._IExpr _out28;
            Defs._IOwnership _out29;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out30;
            (this).GenExpr(_51_cond, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out28, out _out29, out _out30);
            _53_cond = _out28;
            _54___v39 = _out29;
            _55_recIdents = _out30;
            readIdents = _55_recIdents;
            RAST._IExpr _56_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _57_bodyIdents;
            Defs._IEnvironment _58_bodyEnv;
            RAST._IExpr _out31;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
            Defs._IEnvironment _out33;
            (this).GenStmts(_52_body, selfIdent, env, false, earlyReturn, out _out31, out _out32, out _out33);
            _56_bodyExpr = _out31;
            _57_bodyIdents = _out32;
            _58_bodyEnv = _out33;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _57_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_53_cond), _56_bodyExpr);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _59_boundName = _source0.dtor_boundName;
          DAST._IType _60_boundType = _source0.dtor_boundType;
          DAST._IExpression _61_overExpr = _source0.dtor_over;
          Dafny.ISequence<DAST._IStatement> _62_body = _source0.dtor_body;
          {
            RAST._IExpr _63_over;
            Defs._IOwnership _64___v40;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _65_recIdents;
            RAST._IExpr _out34;
            Defs._IOwnership _out35;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out36;
            (this).GenExpr(_61_overExpr, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out34, out _out35, out _out36);
            _63_over = _out34;
            _64___v40 = _out35;
            _65_recIdents = _out36;
            if (((_61_overExpr).is_MapBoundedPool) || ((_61_overExpr).is_SetBoundedPool)) {
              _63_over = ((_63_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply0();
            }
            RAST._IType _66_boundTpe;
            RAST._IType _out37;
            _out37 = (this).GenType(_60_boundType, Defs.GenTypeContext.@default());
            _66_boundTpe = _out37;
            readIdents = _65_recIdents;
            Dafny.ISequence<Dafny.Rune> _67_boundRName;
            _67_boundRName = Defs.__default.escapeVar(_59_boundName);
            RAST._IExpr _68_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _69_bodyIdents;
            Defs._IEnvironment _70_bodyEnv;
            RAST._IExpr _out38;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out39;
            Defs._IEnvironment _out40;
            (this).GenStmts(_62_body, selfIdent, (env).AddAssigned(_67_boundRName, _66_boundTpe), false, earlyReturn, out _out38, out _out39, out _out40);
            _68_bodyExpr = _out38;
            _69_bodyIdents = _out39;
            _70_bodyEnv = _out40;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _69_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_67_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_67_boundRName, _63_over, _68_bodyExpr);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _71_toLabel = _source0.dtor_toLabel;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source1 = _71_toLabel;
            {
              if (_source1.is_Some) {
                Dafny.ISequence<Dafny.Rune> _72_lbl = _source1.dtor_value;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _72_lbl)));
                }
                goto after_match1;
              }
            }
            {
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
          after_match1: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _73_body = _source0.dtor_body;
          {
            generated = (this).InitEmptyExpr();
            Defs._IEnvironment _74_oldEnv;
            _74_oldEnv = env;
            if (!object.Equals(selfIdent, Defs.SelfInfo.create_NoSelf())) {
              RAST._IExpr _75_selfClone;
              Defs._IOwnership _76___v41;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _77___v42;
              RAST._IExpr _out41;
              Defs._IOwnership _out42;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out43;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, Defs.Environment.Empty(), Defs.Ownership.create_OwnershipOwned(), out _out41, out _out42, out _out43);
              _75_selfClone = _out41;
              _76___v41 = _out42;
              _77___v42 = _out43;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_75_selfClone)));
              if (((_74_oldEnv).dtor_names).Contains((selfIdent).dtor_rSelfName)) {
                _74_oldEnv = (_74_oldEnv).RemoveAssigned((selfIdent).dtor_rSelfName);
              }
            }
            RAST._IExpr _78_loopBegin;
            _78_loopBegin = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            newEnv = env;
            BigInteger _hi1 = new BigInteger(((_74_oldEnv).dtor_names).Count);
            for (BigInteger _79_paramI = BigInteger.Zero; _79_paramI < _hi1; _79_paramI++) {
              Dafny.ISequence<Dafny.Rune> _80_param;
              _80_param = ((_74_oldEnv).dtor_names).Select(_79_paramI);
              if ((_80_param).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_accumulator"))) {
                goto continue_4;
              }
              RAST._IExpr _81_paramInit;
              Defs._IOwnership _82___v43;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _83___v44;
              RAST._IExpr _out44;
              Defs._IOwnership _out45;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out46;
              (this).GenIdent(_80_param, selfIdent, _74_oldEnv, Defs.Ownership.create_OwnershipOwned(), out _out44, out _out45, out _out46);
              _81_paramInit = _out44;
              _82___v43 = _out45;
              _83___v44 = _out46;
              Dafny.ISequence<Dafny.Rune> _84_recVar;
              _84_recVar = Dafny.Sequence<Dafny.Rune>.Concat(Defs.__default.TailRecursionPrefix, Std.Strings.__default.OfNat(_79_paramI));
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _84_recVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_81_paramInit)));
              if (((_74_oldEnv).dtor_types).Contains(_80_param)) {
                RAST._IType _85_declaredType;
                _85_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((_74_oldEnv).dtor_types,_80_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_80_param, _85_declaredType);
                newEnv = (newEnv).AddAssigned(_84_recVar, _85_declaredType);
              }
              _78_loopBegin = (_78_loopBegin).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _80_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Identifier(_84_recVar))));
            continue_4: ;
            }
          after_4: ;
            RAST._IExpr _86_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _87_bodyIdents;
            Defs._IEnvironment _88_bodyEnv;
            RAST._IExpr _out47;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out48;
            Defs._IEnvironment _out49;
            (this).GenStmts(_73_body, ((!object.Equals(selfIdent, Defs.SelfInfo.create_NoSelf())) ? (Defs.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (Defs.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out47, out _out48, out _out49);
            _86_bodyExpr = _out47;
            _87_bodyIdents = _out48;
            _88_bodyEnv = _out49;
            readIdents = _87_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), (_78_loopBegin).Then(_86_bodyExpr))));
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_JumpTailCallStart) {
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Call) {
          DAST._IExpression _89_on = _source0.dtor_on;
          DAST._ICallName _90_name = _source0.dtor_callName;
          Dafny.ISequence<DAST._IType> _91_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _92_args = _source0.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _93_maybeOutVars = _source0.dtor_outs;
          {
            RAST._IExpr _out50;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out51;
            (this).GenCall(_89_on, selfIdent, _90_name, _91_typeArgs, _92_args, env, out _out50, out _out51);
            generated = _out50;
            readIdents = _out51;
            newEnv = env;
            if (((_93_maybeOutVars).is_Some) && ((new BigInteger(((_93_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _94_outVar;
              _94_outVar = Defs.__default.escapeVar(((_93_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if ((env).IsMaybePlacebo(_94_outVar)) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_94_outVar, generated);
            } else if (((_93_maybeOutVars).is_None) || ((new BigInteger(((_93_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _95_tmpVar;
              _95_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _96_tmpId;
              _96_tmpId = RAST.Expr.create_Identifier(_95_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _95_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _97_outVars;
              _97_outVars = (_93_maybeOutVars).dtor_value;
              BigInteger _hi2 = new BigInteger((_97_outVars).Count);
              for (BigInteger _98_outI = BigInteger.Zero; _98_outI < _hi2; _98_outI++) {
                Dafny.ISequence<Dafny.Rune> _99_outVar;
                _99_outVar = Defs.__default.escapeVar((_97_outVars).Select(_98_outI));
                RAST._IExpr _100_rhs;
                _100_rhs = (_96_tmpId).Sel(Std.Strings.__default.OfNat(_98_outI));
                if ((env).IsMaybePlacebo(_99_outVar)) {
                  _100_rhs = RAST.__default.MaybePlacebo(_100_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_99_outVar, _100_rhs));
              }
            }
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Return) {
          DAST._IExpression _101_exprDafny = _source0.dtor_expr;
          {
            RAST._IExpr _102_expr;
            Defs._IOwnership _103___v45;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _104_recIdents;
            RAST._IExpr _out52;
            Defs._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_101_exprDafny, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _102_expr = _out52;
            _103___v45 = _out53;
            _104_recIdents = _out54;
            readIdents = _104_recIdents;
            if (isLast) {
              generated = _102_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_102_expr));
            }
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_EarlyReturn) {
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source2 = earlyReturn;
            {
              if (_source2.is_None) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
                goto after_match2;
              }
            }
            {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _105_rustIdents = _source2.dtor_value;
              Dafny.ISequence<RAST._IExpr> _106_tupleArgs;
              _106_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi3 = new BigInteger((_105_rustIdents).Count);
              for (BigInteger _107_i = BigInteger.Zero; _107_i < _hi3; _107_i++) {
                RAST._IExpr _108_rIdent;
                Defs._IOwnership _109___v46;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _110___v47;
                RAST._IExpr _out55;
                Defs._IOwnership _out56;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
                (this).GenIdent((_105_rustIdents).Select(_107_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out55, out _out56, out _out57);
                _108_rIdent = _out55;
                _109___v46 = _out56;
                _110___v47 = _out57;
                _106_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_106_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_108_rIdent));
              }
              if ((new BigInteger((_106_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_106_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_106_tupleArgs)));
              }
            }
          after_match2: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Halt) {
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match0;
        }
      }
      {
        DAST._IExpression _111_e = _source0.dtor_Print_a0;
        {
          RAST._IExpr _112_printedExpr;
          Defs._IOwnership _113_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _114_recIdents;
          RAST._IExpr _out58;
          Defs._IOwnership _out59;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
          (this).GenExpr(_111_e, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out58, out _out59, out _out60);
          _112_printedExpr = _out58;
          _113_recOwnership = _out59;
          _114_recIdents = _out60;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_112_printedExpr)));
          readIdents = _114_recIdents;
          newEnv = env;
        }
      }
    after_match0: ;
    }
    public void FromOwned(RAST._IExpr r, Defs._IOwnership expectedOwnership, out RAST._IExpr @out, out Defs._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      if ((object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipAutoBorrowed()))) {
        @out = r;
        resultingOwnership = Defs.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
        @out = RAST.__default.Borrow(r);
        resultingOwnership = Defs.Ownership.create_OwnershipBorrowed();
      } else {
        RAST._IExpr _out0;
        _out0 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Conversion from Borrowed or BorrowedMut to BorrowedMut"), r);
        @out = _out0;
        @out = ((this).modify__macro).Apply1(@out);
        resultingOwnership = Defs.Ownership.create_OwnershipBorrowedMut();
      }
    }
    public void FromOwnership(RAST._IExpr r, Defs._IOwnership ownership, Defs._IOwnership expectedOwnership, out RAST._IExpr @out, out Defs._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      if (object.Equals(ownership, expectedOwnership)) {
        @out = r;
        resultingOwnership = expectedOwnership;
        return ;
      }
      if (object.Equals(ownership, Defs.Ownership.create_OwnershipOwned())) {
        RAST._IExpr _out0;
        Defs._IOwnership _out1;
        (this).FromOwned(r, expectedOwnership, out _out0, out _out1);
        @out = _out0;
        resultingOwnership = _out1;
        return ;
      } else if ((object.Equals(ownership, Defs.Ownership.create_OwnershipBorrowed())) || (object.Equals(ownership, Defs.Ownership.create_OwnershipBorrowedMut()))) {
        if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipOwned())) {
          resultingOwnership = Defs.Ownership.create_OwnershipOwned();
          @out = (r).Clone();
        } else if ((object.Equals(expectedOwnership, ownership)) || (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipAutoBorrowed()))) {
          resultingOwnership = ownership;
          @out = r;
        } else if ((object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipBorrowed())) && (object.Equals(ownership, Defs.Ownership.create_OwnershipBorrowedMut()))) {
          resultingOwnership = Defs.Ownership.create_OwnershipBorrowed();
          @out = r;
        } else {
          resultingOwnership = Defs.Ownership.create_OwnershipBorrowedMut();
          @out = RAST.__default.BorrowMut(r);
        }
        return ;
      } else {
      }
    }
    public void GenExprLiteral(DAST._IExpression e, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source0 = e;
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h670 = _source0.dtor_Literal_a0;
          if (_h670.is_BoolLiteral) {
            bool _0_b = _h670.dtor_BoolLiteral_a0;
            {
              RAST._IExpr _out0;
              Defs._IOwnership _out1;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_0_b), expectedOwnership, out _out0, out _out1);
              r = _out0;
              resultingOwnership = _out1;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h671 = _source0.dtor_Literal_a0;
          if (_h671.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1_i = _h671.dtor_IntLiteral_a0;
            DAST._IType _2_t = _h671.dtor_IntLiteral_a1;
            {
              DAST._IType _source1 = _2_t;
              {
                if (_source1.is_Primitive) {
                  DAST._IPrimitive _h70 = _source1.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    {
                      if ((new BigInteger((_1_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1_i, true, false));
                      }
                    }
                    goto after_match1;
                  }
                }
              }
              {
                DAST._IType _3_o = _source1;
                {
                  RAST._IType _4_genType;
                  RAST._IType _out2;
                  _out2 = (this).GenType(_3_o, Defs.GenTypeContext.@default());
                  _4_genType = _out2;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_LiteralInt(_1_i), _4_genType);
                }
              }
            after_match1: ;
              RAST._IExpr _out3;
              Defs._IOwnership _out4;
              (this).FromOwned(r, expectedOwnership, out _out3, out _out4);
              r = _out3;
              resultingOwnership = _out4;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h672 = _source0.dtor_Literal_a0;
          if (_h672.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _5_n = _h672.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _6_d = _h672.dtor_DecLiteral_a1;
            DAST._IType _7_t = _h672.dtor_DecLiteral_a2;
            {
              DAST._IType _source2 = _7_t;
              {
                if (_source2.is_Primitive) {
                  DAST._IPrimitive _h71 = _source2.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    {
                      r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigInt"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("parse_bytes"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(_5_n, true, false), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("10"))))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0(), ((((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigInt"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("parse_bytes"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(_6_d, true, false), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("10"))))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0()));
                    }
                    goto after_match2;
                  }
                }
              }
              {
                DAST._IType _8_o = _source2;
                {
                  RAST._IType _9_genType;
                  RAST._IType _out5;
                  _out5 = (this).GenType(_8_o, Defs.GenTypeContext.@default());
                  _9_genType = _out5;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"), (RAST.Expr.create_LiteralInt(_5_n)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (RAST.Expr.create_LiteralInt(_6_d)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat()), _9_genType);
                }
              }
            after_match2: ;
              RAST._IExpr _out6;
              Defs._IOwnership _out7;
              (this).FromOwned(r, expectedOwnership, out _out6, out _out7);
              r = _out6;
              resultingOwnership = _out7;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h673 = _source0.dtor_Literal_a0;
          if (_h673.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _10_l = _h673.dtor_StringLiteral_a0;
            bool _11_verbatim = _h673.dtor_verbatim;
            {
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_10_l, false, _11_verbatim));
              RAST._IExpr _out8;
              Defs._IOwnership _out9;
              (this).FromOwned(r, expectedOwnership, out _out8, out _out9);
              r = _out8;
              resultingOwnership = _out9;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h674 = _source0.dtor_Literal_a0;
          if (_h674.is_CharLiteralUTF16) {
            BigInteger _12_c = _h674.dtor_CharLiteralUTF16_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_12_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
              RAST._IExpr _out10;
              Defs._IOwnership _out11;
              (this).FromOwned(r, expectedOwnership, out _out10, out _out11);
              r = _out10;
              resultingOwnership = _out11;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_Literal) {
          DAST._ILiteral _h675 = _source0.dtor_Literal_a0;
          if (_h675.is_CharLiteral) {
            Dafny.Rune _13_c = _h675.dtor_CharLiteral_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_13_c).Value)));
              if (!(((this).charType).is_UTF32)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0();
              }
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
              RAST._IExpr _out12;
              Defs._IOwnership _out13;
              (this).FromOwned(r, expectedOwnership, out _out12, out _out13);
              r = _out12;
              resultingOwnership = _out13;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        DAST._ILiteral _h676 = _source0.dtor_Literal_a0;
        DAST._IType _14_tpe = _h676.dtor_Null_a0;
        {
          RAST._IType _15_tpeGen;
          RAST._IType _out14;
          _out14 = (this).GenType(_14_tpe, Defs.GenTypeContext.@default());
          _15_tpeGen = _out14;
          if (((this).pointerType).is_Raw) {
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ptr"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _15_tpeGen);
          }
          RAST._IExpr _out15;
          Defs._IOwnership _out16;
          (this).FromOwned(r, expectedOwnership, out _out15, out _out16);
          r = _out15;
          resultingOwnership = _out16;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      }
    after_match0: ;
    }
    public RAST._IExpr ToPrimitive(RAST._IExpr r, DAST._IType typ, DAST._IType primitiveType, Defs._IEnvironment env)
    {
      RAST._IExpr @out = RAST.Expr.Default();
      @out = r;
      if (!object.Equals(typ, primitiveType)) {
        Defs._IOwnership _0_dummy = Defs.Ownership.Default();
        RAST._IExpr _out0;
        Defs._IOwnership _out1;
        (this).GenExprConvertTo(r, Defs.Ownership.create_OwnershipOwned(), typ, primitiveType, env, Defs.Ownership.create_OwnershipOwned(), out _out0, out _out1);
        @out = _out0;
        _0_dummy = _out1;
      }
      return @out;
    }
    public RAST._IExpr ToBool(RAST._IExpr r, DAST._IType typ, Defs._IEnvironment env)
    {
      RAST._IExpr @out = RAST.Expr.Default();
      RAST._IExpr _out0;
      _out0 = (this).ToPrimitive(r, typ, DAST.Type.create_Primitive(DAST.Primitive.create_Bool()), env);
      @out = _out0;
      return @out;
    }
    public RAST._IExpr ToInt(RAST._IExpr r, DAST._IType typ, Defs._IEnvironment env)
    {
      RAST._IExpr @out = RAST.Expr.Default();
      RAST._IExpr _out0;
      _out0 = (this).ToPrimitive(r, typ, DAST.Type.create_Primitive(DAST.Primitive.create_Int()), env);
      @out = _out0;
      return @out;
    }
    public RAST._IExpr FromPrimitive(RAST._IExpr r, DAST._IType primitiveType, DAST._IType typ, Defs._IEnvironment env)
    {
      RAST._IExpr @out = RAST.Expr.Default();
      @out = r;
      if (!object.Equals(typ, primitiveType)) {
        Defs._IOwnership _0_dummy = Defs.Ownership.Default();
        RAST._IExpr _out0;
        Defs._IOwnership _out1;
        (this).GenExprConvertTo(r, Defs.Ownership.create_OwnershipOwned(), primitiveType, typ, env, Defs.Ownership.create_OwnershipOwned(), out _out0, out _out1);
        @out = _out0;
        _0_dummy = _out1;
      }
      return @out;
    }
    public RAST._IExpr FromBool(RAST._IExpr r, DAST._IType typ, Defs._IEnvironment env)
    {
      RAST._IExpr @out = RAST.Expr.Default();
      RAST._IExpr _out0;
      _out0 = (this).FromPrimitive(r, DAST.Type.create_Primitive(DAST.Primitive.create_Bool()), typ, env);
      @out = _out0;
      return @out;
    }
    public RAST._IExpr FromInt(RAST._IExpr r, DAST._IType typ, Defs._IEnvironment env)
    {
      RAST._IExpr @out = RAST.Expr.Default();
      RAST._IExpr _out0;
      _out0 = (this).FromPrimitive(r, DAST.Type.create_Primitive(DAST.Primitive.create_Int()), typ, env);
      @out = _out0;
      return @out;
    }
    public void GenExprBinary(DAST._IExpression e, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._ITypedBinOp _let_tmp_rhs1 = _let_tmp_rhs0.dtor_op;
      DAST._IBinOp _0_op = _let_tmp_rhs1.dtor_op;
      DAST._IType _1_lType = _let_tmp_rhs1.dtor_leftType;
      DAST._IType _2_rType = _let_tmp_rhs1.dtor_rightType;
      DAST._IType _3_resType = _let_tmp_rhs1.dtor_resultType;
      DAST._IExpression _4_lExpr = _let_tmp_rhs0.dtor_left;
      DAST._IExpression _5_rExpr = _let_tmp_rhs0.dtor_right;
      DAST.Format._IBinaryOpFormat _6_format = _let_tmp_rhs0.dtor_format2;
      bool _7_becomesLeftCallsRight;
      _7_becomesLeftCallsRight = Defs.__default.BecomesLeftCallsRight(_0_op);
      bool _8_becomesRightCallsLeft;
      _8_becomesRightCallsLeft = Defs.__default.BecomesRightCallsLeft(_0_op);
      Defs._IOwnership _9_expectedLeftOwnership;
      if (_7_becomesLeftCallsRight) {
        _9_expectedLeftOwnership = Defs.Ownership.create_OwnershipAutoBorrowed();
      } else if (_8_becomesRightCallsLeft) {
        _9_expectedLeftOwnership = Defs.Ownership.create_OwnershipBorrowed();
      } else {
        _9_expectedLeftOwnership = Defs.Ownership.create_OwnershipOwned();
      }
      Defs._IOwnership _10_expectedRightOwnership;
      if (_7_becomesLeftCallsRight) {
        _10_expectedRightOwnership = Defs.Ownership.create_OwnershipBorrowed();
      } else if (_8_becomesRightCallsLeft) {
        _10_expectedRightOwnership = Defs.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _10_expectedRightOwnership = Defs.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _11_left;
      Defs._IOwnership _12___v48;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _13_recIdentsL;
      RAST._IExpr _out0;
      Defs._IOwnership _out1;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
      (this).GenExpr(_4_lExpr, selfIdent, env, _9_expectedLeftOwnership, out _out0, out _out1, out _out2);
      _11_left = _out0;
      _12___v48 = _out1;
      _13_recIdentsL = _out2;
      RAST._IExpr _14_right;
      Defs._IOwnership _15___v49;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _16_recIdentsR;
      RAST._IExpr _out3;
      Defs._IOwnership _out4;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
      (this).GenExpr(_5_rExpr, selfIdent, env, _10_expectedRightOwnership, out _out3, out _out4, out _out5);
      _14_right = _out3;
      _15___v49 = _out4;
      _16_recIdentsR = _out5;
      DAST._IBinOp _source0 = _0_op;
      {
        if (_source0.is_In) {
          {
            r = ((_14_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_11_left);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqProperPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _11_left, _14_right, _6_format);
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _11_left, _14_right, _6_format);
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetMerge) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetSubtraction) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetIntersection) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Subset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _11_left, _14_right, _6_format);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ProperSubset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _11_left, _14_right, _6_format);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetDisjoint) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapMerge) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapSubtraction) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetMerge) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetSubtraction) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetIntersection) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Submultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _11_left, _14_right, _6_format);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ProperSubmultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _11_left, _14_right, _6_format);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetDisjoint) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Concat) {
          {
            r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_14_right);
          }
          goto after_match0;
        }
      }
      {
        {
          if ((Defs.__default.OpTable).Contains(_0_op)) {
            if (Defs.__default.IsBooleanOperator(_0_op)) {
              RAST._IExpr _out6;
              _out6 = (this).ToBool(_11_left, _1_lType, env);
              _11_left = _out6;
              RAST._IExpr _out7;
              _out7 = (this).ToBool(_14_right, _2_rType, env);
              _14_right = _out7;
            }
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(Defs.__default.OpTable,_0_op), _11_left, _14_right, _6_format);
            if (Defs.__default.IsBooleanOperator(_0_op)) {
              RAST._IExpr _out8;
              _out8 = (this).FromBool(r, _3_resType, env);
              r = _out8;
            }
          } else {
            if (Defs.__default.IsComplexArithmetic(_0_op)) {
              RAST._IExpr _out9;
              _out9 = (this).ToInt(_11_left, _1_lType, env);
              _11_left = _out9;
              RAST._IExpr _out10;
              _out10 = (this).ToInt(_14_right, _2_rType, env);
              _14_right = _out10;
            }
            DAST._IBinOp _source1 = _0_op;
            {
              if (_source1.is_Eq) {
                bool _17_referential = _source1.dtor_referential;
                {
                  if (_17_referential) {
                    if (((this).pointerType).is_Raw) {
                      RAST._IExpr _out11;
                      _out11 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Raw pointer comparison not properly implemented yet"), (this).InitEmptyExpr());
                      r = _out11;
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _11_left, _14_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_5_rExpr).is_SeqValue) && ((new BigInteger(((_5_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0(), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_4_lExpr).is_SeqValue) && ((new BigInteger(((_4_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_14_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0(), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _11_left, _14_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                      if (!object.Equals(_3_resType, DAST.Type.create_Primitive(DAST.Primitive.create_Bool()))) {
                        RAST._IExpr _out12;
                        Defs._IOwnership _out13;
                        (this).GenExprConvertTo(r, Defs.Ownership.create_OwnershipOwned(), DAST.Type.create_Primitive(DAST.Primitive.create_Bool()), _3_resType, env, Defs.Ownership.create_OwnershipOwned(), out _out12, out _out13);
                        r = _out12;
                        resultingOwnership = _out13;
                      }
                    }
                  }
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_Div) {
                bool overflow0 = _source1.dtor_overflow;
                if ((overflow0) == (true)) {
                  r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("wrapping_div"))).Apply1(_14_right);
                  goto after_match1;
                }
              }
            }
            {
              if (_source1.is_Plus) {
                bool overflow1 = _source1.dtor_overflow;
                if ((overflow1) == (true)) {
                  r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("wrapping_add"))).Apply1(_14_right);
                  goto after_match1;
                }
              }
            }
            {
              if (_source1.is_Times) {
                bool overflow2 = _source1.dtor_overflow;
                if ((overflow2) == (true)) {
                  r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("wrapping_mul"))).Apply1(_14_right);
                  goto after_match1;
                }
              }
            }
            {
              if (_source1.is_Minus) {
                bool overflow3 = _source1.dtor_overflow;
                if ((overflow3) == (true)) {
                  r = ((_11_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("wrapping_sub"))).Apply1(_14_right);
                  goto after_match1;
                }
              }
            }
            {
              if (_source1.is_EuclidianDiv) {
                {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("euclidian_division"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_11_left, _14_right));
                }
                goto after_match1;
              }
            }
            {
              if (_source1.is_EuclidianMod) {
                {
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("euclidian_modulo"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_11_left, _14_right));
                }
                goto after_match1;
              }
            }
            {
              Dafny.ISequence<Dafny.Rune> _18_op = _source1.dtor_Passthrough_a0;
              {
                r = RAST.Expr.create_BinaryOp(_18_op, _11_left, _14_right, _6_format);
              }
            }
          after_match1: ;
            if (Defs.__default.IsComplexArithmetic(_0_op)) {
              RAST._IExpr _out14;
              _out14 = (this).FromInt(r, _3_resType, env);
              r = _out14;
            }
          }
        }
      }
    after_match0: ;
      RAST._IExpr _out15;
      Defs._IOwnership _out16;
      (this).FromOwned(r, expectedOwnership, out _out15, out _out16);
      r = _out15;
      resultingOwnership = _out16;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_13_recIdentsL, _16_recIdentsR);
      return ;
    }
    public RAST._IExpr UnwrapNewtype(RAST._IExpr expr, Defs._IOwnership exprOwnership, DAST._IType fromTpe)
    {
      RAST._IExpr r = RAST.Expr.Default();
      r = expr;
      if (!((((fromTpe).dtor_resolved).dtor_kind).dtor_erase)) {
        r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
        if (object.Equals(exprOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
          r = RAST.__default.Borrow(r);
        }
      }
      return r;
    }
    public RAST._IExpr WrapWithNewtype(RAST._IExpr expr, Defs._IOwnership exprOwnership, DAST._IType toTpe)
    {
      RAST._IExpr r = RAST.Expr.Default();
      r = expr;
      DAST._IResolvedTypeBase _0_toKind;
      _0_toKind = ((toTpe).dtor_resolved).dtor_kind;
      if (!((_0_toKind).dtor_erase)) {
        RAST._IExpr _1_fullPath;
        RAST._IExpr _out0;
        _out0 = (this).GenPathExpr(((toTpe).dtor_resolved).dtor_path, true);
        _1_fullPath = _out0;
        if (object.Equals(exprOwnership, Defs.Ownership.create_OwnershipOwned())) {
          r = (_1_fullPath).Apply1(r);
        } else {
          r = ((_1_fullPath).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_from_ref"))).Apply1(r);
        }
      }
      return r;
    }
    public void GenExprConvertTo(RAST._IExpr expr, Defs._IOwnership exprOwnership, DAST._IType fromTpeWithSynonyms, DAST._IType toTpeWithSynonyms, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      DAST._IType _0_fromTpe;
      _0_fromTpe = (fromTpeWithSynonyms).RemoveSynonyms();
      DAST._IType _1_toTpe;
      _1_toTpe = (toTpeWithSynonyms).RemoveSynonyms();
      RAST._IExpr _out0;
      Defs._IOwnership _out1;
      (this).GenExprConvertToWithoutSynonyms(expr, exprOwnership, _0_fromTpe, _1_toTpe, env, expectedOwnership, out _out0, out _out1);
      r = _out0;
      resultingOwnership = _out1;
    }
    public void GenExprConvertToWithoutSynonyms(RAST._IExpr expr, Defs._IOwnership exprOwnership, DAST._IType fromTpe, DAST._IType toTpe, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      r = expr;
      if (object.Equals(fromTpe, toTpe)) {
        RAST._IExpr _out0;
        Defs._IOwnership _out1;
        (this).FromOwnership(r, exprOwnership, expectedOwnership, out _out0, out _out1);
        r = _out0;
        resultingOwnership = _out1;
        return ;
      }
      if (Defs.__default.NeedsUnwrappingConversion(fromTpe)) {
        RAST._IExpr _out2;
        _out2 = (this).UnwrapNewtype(r, exprOwnership, fromTpe);
        r = _out2;
        RAST._IExpr _out3;
        Defs._IOwnership _out4;
        (this).GenExprConvertToWithoutSynonyms(r, exprOwnership, (((fromTpe).dtor_resolved).dtor_kind).dtor_baseType, toTpe, env, expectedOwnership, out _out3, out _out4);
        r = _out3;
        resultingOwnership = _out4;
        return ;
      }
      if (Defs.__default.NeedsUnwrappingConversion(toTpe)) {
        DAST._IResolvedTypeBase _0_toKind;
        _0_toKind = ((toTpe).dtor_resolved).dtor_kind;
        RAST._IExpr _out5;
        Defs._IOwnership _out6;
        (this).GenExprConvertToWithoutSynonyms(r, exprOwnership, fromTpe, (_0_toKind).dtor_baseType, env, expectedOwnership, out _out5, out _out6);
        r = _out5;
        resultingOwnership = _out6;
        RAST._IExpr _out7;
        _out7 = (this).WrapWithNewtype(r, resultingOwnership, toTpe);
        r = _out7;
        RAST._IExpr _out8;
        Defs._IOwnership _out9;
        (this).FromOwnership(r, resultingOwnership, expectedOwnership, out _out8, out _out9);
        r = _out8;
        resultingOwnership = _out9;
        return ;
      }
      Std.Wrappers._IOption<RAST._IType> _1_unwrappedFromType;
      _1_unwrappedFromType = Defs.__default.GetUnwrappedBoundedRustType(fromTpe);
      Std.Wrappers._IOption<RAST._IType> _2_unwrappedToType;
      _2_unwrappedToType = Defs.__default.GetUnwrappedBoundedRustType(toTpe);
      if ((_2_unwrappedToType).is_Some) {
        RAST._IType _3_boundedToType;
        _3_boundedToType = (_2_unwrappedToType).dtor_value;
        if ((_1_unwrappedFromType).is_Some) {
          RAST._IExpr _out10;
          _out10 = (this).UnwrapNewtype(r, exprOwnership, fromTpe);
          r = _out10;
          Defs._IOwnership _4_inOwnership;
          _4_inOwnership = exprOwnership;
          if (!object.Equals((_1_unwrappedFromType).dtor_value, (_2_unwrappedToType).dtor_value)) {
            RAST._IType _5_asType;
            _5_asType = _3_boundedToType;
            if (object.Equals(_4_inOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
              RAST._IExpr _source0 = r;
              {
                if (_source0.is_UnaryOp) {
                  Dafny.ISequence<Dafny.Rune> op10 = _source0.dtor_op1;
                  if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                    RAST._IExpr _6_underlying = _source0.dtor_underlying;
                    r = _6_underlying;
                    goto after_match0;
                  }
                }
              }
              {
                r = (r).Clone();
              }
            after_match0: ;
            }
            r = RAST.Expr.create_TypeAscription(r, _5_asType);
            _4_inOwnership = Defs.Ownership.create_OwnershipOwned();
          }
          RAST._IExpr _out11;
          _out11 = (this).WrapWithNewtype(r, Defs.Ownership.create_OwnershipOwned(), toTpe);
          r = _out11;
          RAST._IExpr _out12;
          Defs._IOwnership _out13;
          (this).FromOwnership(r, _4_inOwnership, expectedOwnership, out _out12, out _out13);
          r = _out12;
          resultingOwnership = _out13;
          return ;
        }
        if ((fromTpe).IsPrimitiveInt()) {
          if (object.Equals(exprOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
            r = (r).Clone();
          }
          r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r, RAST.Expr.create_ExprFromType(_3_boundedToType)));
          RAST._IExpr _out14;
          _out14 = (this).WrapWithNewtype(r, Defs.Ownership.create_OwnershipOwned(), toTpe);
          r = _out14;
          RAST._IExpr _out15;
          Defs._IOwnership _out16;
          (this).FromOwned(r, expectedOwnership, out _out15, out _out16);
          r = _out15;
          resultingOwnership = _out16;
          return ;
        }
        if (object.Equals(fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
          r = RAST.Expr.create_TypeAscription((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), _3_boundedToType);
          RAST._IExpr _out17;
          _out17 = (this).WrapWithNewtype(r, Defs.Ownership.create_OwnershipOwned(), toTpe);
          r = _out17;
          RAST._IExpr _out18;
          Defs._IOwnership _out19;
          (this).FromOwned(r, expectedOwnership, out _out18, out _out19);
          r = _out18;
          resultingOwnership = _out19;
          return ;
        }
        RAST._IType _7_fromTpeRust;
        RAST._IType _out20;
        _out20 = (this).GenType(fromTpe, Defs.GenTypeContext.@default());
        _7_fromTpeRust = _out20;
        RAST._IExpr _out21;
        _out21 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("No conversion available from "), (_7_fromTpeRust)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_3_boundedToType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (this).InitEmptyExpr());
        r = _out21;
        RAST._IExpr _out22;
        Defs._IOwnership _out23;
        (this).FromOwned(r, expectedOwnership, out _out22, out _out23);
        r = _out22;
        resultingOwnership = _out23;
        return ;
      }
      if ((_1_unwrappedFromType).is_Some) {
        if (!((((fromTpe).dtor_resolved).dtor_kind).dtor_erase)) {
          r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
        }
        if (object.Equals(toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
          RAST._IExpr _out24;
          Defs._IOwnership _out25;
          (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(r, (this).DafnyCharUnderlying)), exprOwnership, expectedOwnership, out _out24, out _out25);
          r = _out24;
          resultingOwnership = _out25;
          return ;
        }
        if ((toTpe).IsPrimitiveInt()) {
          RAST._IExpr _out26;
          Defs._IOwnership _out27;
          (this).FromOwnership(r, exprOwnership, Defs.Ownership.create_OwnershipOwned(), out _out26, out _out27);
          r = _out26;
          resultingOwnership = _out27;
          r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
          RAST._IExpr _out28;
          Defs._IOwnership _out29;
          (this).FromOwned(r, expectedOwnership, out _out28, out _out29);
          r = _out28;
          resultingOwnership = _out29;
          return ;
        }
        RAST._IType _8_toTpeRust;
        RAST._IType _out30;
        _out30 = (this).GenType(toTpe, Defs.GenTypeContext.@default());
        _8_toTpeRust = _out30;
        RAST._IExpr _out31;
        _out31 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("No conversion available from "), ((_1_unwrappedFromType).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_8_toTpeRust)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (this).InitEmptyExpr());
        r = _out31;
        RAST._IExpr _out32;
        Defs._IOwnership _out33;
        (this).FromOwned(r, expectedOwnership, out _out32, out _out33);
        r = _out32;
        resultingOwnership = _out33;
        return ;
      }
      _System._ITuple2<DAST._IType, DAST._IType> _source1 = _System.Tuple2<DAST._IType, DAST._IType>.create(fromTpe, toTpe);
      {
        DAST._IType _00 = _source1.dtor__0;
        if (_00.is_Primitive) {
          DAST._IPrimitive _h70 = _00.dtor_Primitive_a0;
          if (_h70.is_Int) {
            DAST._IType _10 = _source1.dtor__1;
            if (_10.is_Primitive) {
              DAST._IPrimitive _h71 = _10.dtor_Primitive_a0;
              if (_h71.is_Real) {
                {
                  r = Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>((this).rcNew)(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_integer"))).Apply1(r));
                  RAST._IExpr _out34;
                  Defs._IOwnership _out35;
                  (this).FromOwned(r, expectedOwnership, out _out34, out _out35);
                  r = _out34;
                  resultingOwnership = _out35;
                }
                goto after_match1;
              }
            }
          }
        }
      }
      {
        DAST._IType _01 = _source1.dtor__0;
        if (_01.is_Primitive) {
          DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
          if (_h72.is_Real) {
            DAST._IType _11 = _source1.dtor__1;
            if (_11.is_Primitive) {
              DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
              if (_h73.is_Int) {
                {
                  r = (((RAST.__default.dafny__runtime).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_rational_to_int"))).Apply1(r);
                  RAST._IExpr _out36;
                  Defs._IOwnership _out37;
                  (this).FromOwned(r, expectedOwnership, out _out36, out _out37);
                  r = _out36;
                  resultingOwnership = _out37;
                }
                goto after_match1;
              }
            }
          }
        }
      }
      {
        DAST._IType _02 = _source1.dtor__0;
        if (_02.is_Primitive) {
          DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
          if (_h74.is_Int) {
            DAST._IType _12 = _source1.dtor__1;
            if (_12.is_Primitive) {
              DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
              if (_h75.is_Char) {
                {
                  RAST._IType _9_rhsType;
                  RAST._IType _out38;
                  _out38 = (this).GenType(toTpe, Defs.GenTypeContext.@default());
                  _9_rhsType = _out38;
                  RAST._IType _10_uType;
                  if (((this).charType).is_UTF32) {
                    _10_uType = RAST.Type.create_U32();
                  } else {
                    _10_uType = RAST.Type.create_U16();
                  }
                  if (!object.Equals(exprOwnership, Defs.Ownership.create_OwnershipOwned())) {
                    r = (r).Clone();
                  }
                  r = ((((RAST.Expr.create_TraitCast(_10_uType, ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("NumCast"))).AsType())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0();
                  if (((this).charType).is_UTF32) {
                    r = ((((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0();
                  }
                  r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
                  RAST._IExpr _out39;
                  Defs._IOwnership _out40;
                  (this).FromOwned(r, expectedOwnership, out _out39, out _out40);
                  r = _out39;
                  resultingOwnership = _out40;
                }
                goto after_match1;
              }
            }
          }
        }
      }
      {
        DAST._IType _03 = _source1.dtor__0;
        if (_03.is_Primitive) {
          DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
          if (_h76.is_Char) {
            DAST._IType _13 = _source1.dtor__1;
            if (_13.is_Primitive) {
              DAST._IPrimitive _h77 = _13.dtor_Primitive_a0;
              if (_h77.is_Int) {
                {
                  RAST._IType _11_rhsType;
                  RAST._IType _out41;
                  _out41 = (this).GenType(fromTpe, Defs.GenTypeContext.@default());
                  _11_rhsType = _out41;
                  r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                  RAST._IExpr _out42;
                  Defs._IOwnership _out43;
                  (this).FromOwned(r, expectedOwnership, out _out42, out _out43);
                  r = _out42;
                  resultingOwnership = _out43;
                }
                goto after_match1;
              }
            }
          }
        }
      }
      {
        {
          RAST._IExpr _out44;
          Defs._IOwnership _out45;
          (this).GenExprConvertOther(expr, exprOwnership, fromTpe, toTpe, env, expectedOwnership, out _out44, out _out45);
          r = _out44;
          resultingOwnership = _out45;
        }
      }
    after_match1: ;
    }
    public bool IsBuiltinCollection(DAST._IType typ) {
      return ((((typ).is_Seq) || ((typ).is_Set)) || ((typ).is_Map)) || ((typ).is_Multiset);
    }
    public DAST._IType GetBuiltinCollectionElement(DAST._IType typ) {
      if ((typ).is_Map) {
        return (typ).dtor_value;
      } else {
        return (typ).dtor_element;
      }
    }
    public bool SameTypesButDifferentTypeParameters(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe)
    {
      return (((((((fromTpe).is_TypeApp) && ((toTpe).is_TypeApp)) && (object.Equals((fromTpe).dtor_baseName, (toTpe).dtor_baseName))) && ((fromType).is_UserDefined)) && ((toType).is_UserDefined)) && ((this).IsSameResolvedTypeAnyArgs((fromType).dtor_resolved, (toType).dtor_resolved))) && ((((new BigInteger((((fromType).dtor_resolved).dtor_typeArgs).Count)) == (new BigInteger((((toType).dtor_resolved).dtor_typeArgs).Count))) && ((new BigInteger((((toType).dtor_resolved).dtor_typeArgs).Count)) == (new BigInteger(((fromTpe).dtor_arguments).Count)))) && ((new BigInteger(((fromTpe).dtor_arguments).Count)) == (new BigInteger(((toTpe).dtor_arguments).Count))));
    }
    public Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> SeqResultToResultSeq<__T, __E>(Dafny.ISequence<Std.Wrappers._IResult<__T, __E>> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.FromElements());
      } else {
        Std.Wrappers._IResult<__T, __E> _0_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_0_valueOrError0).IsFailure()) {
          return (_0_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1_head = (_0_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _2_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_2_valueOrError1).IsFailure()) {
            return (_2_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _3_tail = (_2_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1_head), _3_tail));
          }
        }
      }
    }
    public Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> UpcastConversionLambda(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> typeParams)
    {
      var _pat_let_tv0 = fromType;
      var _pat_let_tv1 = fromTpe;
      var _pat_let_tv2 = toType;
      var _pat_let_tv3 = toTpe;
      var _pat_let_tv4 = typeParams;
      if (object.Equals(fromTpe, toTpe)) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_id"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe))).Apply0());
      } else if ((toTpe).IsBox()) {
        RAST._IType _0_toTpeUnderlying = (toTpe).BoxUnderlying();
        if (!((_0_toTpeUnderlying).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else if ((fromTpe).IsBox()) {
          RAST._IType _1_fromTpeUnderlying = (fromTpe).BoxUnderlying();
          if (!((_1_fromTpeUnderlying).is_DynType)) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_box_box"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1_fromTpeUnderlying, _0_toTpeUnderlying))).Apply0());
          }
        } else {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_box"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe, _0_toTpeUnderlying))).Apply0());
        }
      } else if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        RAST._IType _2_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
        if (!((_2_toTpeUnderlying).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else {
          RAST._IType _3_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3_fromTpeUnderlying, _2_toTpeUnderlying))).Apply0());
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _4_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_4_valueOrError0).IsFailure()) {
          return (_4_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _5_lambda = (_4_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_5_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_5_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Dafny.ISequence<BigInteger> _6_indices = ((((fromType).is_UserDefined) && ((((fromType).dtor_resolved).dtor_kind).is_Datatype)) ? (Std.Collections.Seq.__default.Filter<BigInteger>(Dafny.Helpers.Id<Func<RAST._IType, DAST._IType, Func<BigInteger, bool>>>((_7_fromTpe, _8_fromType) => ((System.Func<BigInteger, bool>)((_9_i) => {
          return ((((_9_i).Sign != -1) && ((_9_i) < (new BigInteger(((_7_fromTpe).dtor_arguments).Count)))) ? (!(((_9_i).Sign != -1) && ((_9_i) < (new BigInteger(((((_8_fromType).dtor_resolved).dtor_kind).dtor_info).Count)))) || (!(((((((_8_fromType).dtor_resolved).dtor_kind).dtor_info).Select(_9_i)).dtor_variance).is_Nonvariant))) : (false));
        })))(fromTpe, fromType), ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim17 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr17 = new BigInteger[Dafny.Helpers.ToIntChecked(dim17, "array size exceeds memory limit")];
          for (int i17 = 0; i17 < dim17; i17++) {
            var _10_i = (BigInteger) i17;
            arr17[(int)(_10_i)] = _10_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr17);
        }))())) : (((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim18 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr18 = new BigInteger[Dafny.Helpers.ToIntChecked(dim18, "array size exceeds memory limit")];
          for (int i18 = 0; i18 < dim18; i18++) {
            var _11_i = (BigInteger) i18;
            arr18[(int)(_11_i)] = _11_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr18);
        }))()));
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _12_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim19 = new BigInteger((_6_indices).Count);
          var arr19 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim19, "array size exceeds memory limit")];
          for (int i19 = 0; i19 < dim19; i19++) {
            var _13_j = (BigInteger) i19;
            arr19[(int)(_13_j)] = Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>((_6_indices).Select(_13_j), _pat_let74_0 => Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>(_pat_let74_0, _14_i => (this).UpcastConversionLambda((((_pat_let_tv0).dtor_resolved).dtor_typeArgs).Select(_14_i), ((_pat_let_tv1).dtor_arguments).Select(_14_i), (((_pat_let_tv2).dtor_resolved).dtor_typeArgs).Select(_14_i), ((_pat_let_tv3).dtor_arguments).Select(_14_i), _pat_let_tv4)));
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr19);
        }))());
        if ((_12_valueOrError1).IsFailure()) {
          return (_12_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _15_lambdas = (_12_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim20 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr20 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim20, "array size exceeds memory limit")];
  for (int i20 = 0; i20 < dim20; i20++) {
    var _16_i = (BigInteger) i20;
    arr20[(int)(_16_i)] = ((fromTpe).dtor_arguments).Select(_16_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr20);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_15_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _17_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _18_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _19_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _20_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _21_valueOrError2 = (this).UpcastConversionLambda(_19_newFromType, _17_newFromTpe, _20_newToType, _18_newToTpe, typeParams);
        if ((_21_valueOrError2).IsFailure()) {
          return (_21_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _22_coerceArg = (_21_valueOrError2).Extract();
          RAST._IPath _23_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _24_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_23_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _17_newFromTpe))) : (((_23_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_17_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_24_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_22_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _25_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_25_valueOrError3).IsFailure()) {
          return (_25_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _26_lambda = (_25_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_26_lambda));
        }
      } else {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
      }
    }
    public bool IsDowncastConversion(RAST._IType fromTpe, RAST._IType toTpe)
    {
      if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        return (((fromTpe).ObjectOrPointerUnderlying()).is_DynType) && (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType));
      } else {
        return false;
      }
    }
    public RAST._IExpr BorrowedToOwned(RAST._IExpr expr, Defs._IEnvironment env)
    {
      RAST._IExpr _source0 = expr;
      {
        if (_source0.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op10 = _source0.dtor_op1;
          if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
            RAST._IExpr _0_underlying = _source0.dtor_underlying;
            if (((_0_underlying).is_Identifier) && ((env).CanReadWithoutClone((_0_underlying).dtor_name))) {
              return _0_underlying;
            } else {
              return (_0_underlying).Clone();
            }
          }
        }
      }
      {
        return (expr).Clone();
      }
    }
    public void GenExprConvertOther(RAST._IExpr expr, Defs._IOwnership exprOwnership, DAST._IType fromTyp, DAST._IType toTyp, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      r = expr;
      resultingOwnership = exprOwnership;
      RAST._IType _0_fromTpeGen;
      RAST._IType _out0;
      _out0 = (this).GenType(fromTyp, Defs.GenTypeContext.@default());
      _0_fromTpeGen = _out0;
      RAST._IType _1_toTpeGen;
      RAST._IType _out1;
      _out1 = (this).GenType(toTyp, Defs.GenTypeContext.@default());
      _1_toTpeGen = _out1;
      bool _2_isDatatype;
      _2_isDatatype = (toTyp).IsDatatype();
      bool _3_isGeneralTrait;
      _3_isGeneralTrait = (!(_2_isDatatype)) && ((toTyp).IsGeneralTrait());
      if ((_2_isDatatype) || (_3_isGeneralTrait)) {
        bool _4_isDowncast;
        _4_isDowncast = (toTyp).Extends(fromTyp);
        if (_4_isDowncast) {
          DAST._IType _5_underlyingType;
          if (_2_isDatatype) {
            _5_underlyingType = (toTyp).GetDatatypeType();
          } else {
            _5_underlyingType = (toTyp).GetGeneralTraitType();
          }
          RAST._IType _6_toTpeRaw;
          RAST._IType _out2;
          _out2 = (this).GenType(_5_underlyingType, Defs.GenTypeContext.@default());
          _6_toTpeRaw = _out2;
          Std.Wrappers._IOption<RAST._IExpr> _7_toTpeRawDowncastOpt;
          _7_toTpeRawDowncastOpt = (_6_toTpeRaw).ToDowncastExpr();
          if ((_7_toTpeRawDowncastOpt).is_Some) {
            RAST._IExpr _8_newExpr;
            _8_newExpr = expr;
            if ((exprOwnership).is_OwnershipOwned) {
              RAST._IExpr _source0 = _8_newExpr;
              {
                if (_source0.is_Call) {
                  RAST._IExpr obj0 = _source0.dtor_obj;
                  if (obj0.is_Select) {
                    RAST._IExpr obj1 = obj0.dtor_obj;
                    if (obj1.is_Identifier) {
                      Dafny.ISequence<Dafny.Rune> _9_name = obj1.dtor_name;
                      Dafny.ISequence<Dafny.Rune> name0 = obj0.dtor_name;
                      if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        Dafny.ISequence<RAST._IExpr> _10_arguments = _source0.dtor_arguments;
                        if ((new BigInteger((_10_arguments).Count)).Sign == 0) {
                          _8_newExpr = RAST.Expr.create_Identifier(_9_name);
                          if (!((env).IsBorrowed(_9_name))) {
                            _8_newExpr = RAST.__default.Borrow(_8_newExpr);
                          }
                        } else {
                          RAST._IExpr _out3;
                          Defs._IOwnership _out4;
                          (this).FromOwnership(_8_newExpr, Defs.Ownership.create_OwnershipOwned(), Defs.Ownership.create_OwnershipBorrowed(), out _out3, out _out4);
                          _8_newExpr = _out3;
                          resultingOwnership = _out4;
                        }
                        goto after_match0;
                      }
                    }
                  }
                }
              }
              {
                {
                  RAST._IExpr _out5;
                  Defs._IOwnership _out6;
                  (this).FromOwnership(_8_newExpr, Defs.Ownership.create_OwnershipOwned(), Defs.Ownership.create_OwnershipBorrowed(), out _out5, out _out6);
                  _8_newExpr = _out5;
                  resultingOwnership = _out6;
                }
              }
            after_match0: ;
            }
            _8_newExpr = (this).FromGeneralBorrowToSelfBorrow(_8_newExpr, Defs.Ownership.create_OwnershipBorrowed(), env);
            if (_2_isDatatype) {
              _8_newExpr = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AnyRef"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_any_ref"))).Apply1(_8_newExpr);
            }
            r = (((_7_toTpeRawDowncastOpt).dtor_value).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as"))).Apply1(_8_newExpr);
            RAST._IExpr _out7;
            Defs._IOwnership _out8;
            (this).FromOwnership(r, Defs.Ownership.create_OwnershipOwned(), expectedOwnership, out _out7, out _out8);
            r = _out7;
            resultingOwnership = _out8;
            return ;
          } else {
            RAST._IExpr _out9;
            _out9 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not convert "), (_6_toTpeRaw)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to a Downcast trait")), (this).InitEmptyExpr());
            r = _out9;
            RAST._IExpr _out10;
            Defs._IOwnership _out11;
            (this).FromOwned(r, expectedOwnership, out _out10, out _out11);
            r = _out10;
            resultingOwnership = _out11;
            return ;
          }
        }
      }
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _11_upcastConverter;
      _11_upcastConverter = (this).UpcastConversionLambda(fromTyp, _0_fromTpeGen, toTyp, _1_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_11_upcastConverter).is_Success) {
        RAST._IExpr _12_conversionLambda;
        _12_conversionLambda = (_11_upcastConverter).dtor_value;
        if (object.Equals(resultingOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
          if (((fromTyp).IsGeneralTrait()) && (object.Equals(r, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
            RAST._IType _13_traitType;
            RAST._IType _out12;
            _out12 = (this).GenType(fromTyp, Defs.GenTypeContext.ForTraitParents());
            _13_traitType = _out12;
            Std.Wrappers._IOption<RAST._IExpr> _14_traitExpr;
            _14_traitExpr = (_13_traitType).ToExpr();
            if ((_14_traitExpr).is_None) {
              RAST._IExpr _out13;
              _out13 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not convert "), (_13_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to an expression")), (this).InitEmptyExpr());
              r = _out13;
            } else {
              r = (((_14_traitExpr).dtor_value).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_clone"))).Apply1(r);
            }
          } else {
            r = (this).BorrowedToOwned(r, env);
          }
          resultingOwnership = Defs.Ownership.create_OwnershipOwned();
        }
        r = (_12_conversionLambda).Apply1(r);
        RAST._IExpr _out14;
        Defs._IOwnership _out15;
        (this).FromOwnership(r, resultingOwnership, expectedOwnership, out _out14, out _out15);
        r = _out14;
        resultingOwnership = _out15;
      } else if ((this).IsDowncastConversion(_0_fromTpeGen, _1_toTpeGen)) {
        _1_toTpeGen = (_1_toTpeGen).ObjectOrPointerUnderlying();
        if (object.Equals(resultingOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
          r = (this).BorrowedToOwned(r, env);
          resultingOwnership = Defs.Ownership.create_OwnershipOwned();
        }
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r, RAST.Expr.create_ExprFromType(_1_toTpeGen)));
        RAST._IExpr _out16;
        Defs._IOwnership _out17;
        (this).FromOwnership(r, Defs.Ownership.create_OwnershipOwned(), expectedOwnership, out _out16, out _out17);
        r = _out16;
        resultingOwnership = _out17;
      } else {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs0 = _11_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs1 = _let_tmp_rhs0.dtor_error;
        DAST._IType _15_fromType = _let_tmp_rhs1.dtor__0;
        RAST._IType _16_fromTpeGen = _let_tmp_rhs1.dtor__1;
        DAST._IType _17_toType = _let_tmp_rhs1.dtor__2;
        RAST._IType _18_toTpeGen = _let_tmp_rhs1.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _19_m = _let_tmp_rhs1.dtor__4;
        RAST._IExpr _out18;
        _out18 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Coercion from "), (_16_fromTpeGen)._ToString(Defs.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_18_toTpeGen)._ToString(Defs.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented")), r);
        r = _out18;
        RAST._IExpr _out19;
        Defs._IOwnership _out20;
        (this).FromOwned(r, expectedOwnership, out _out19, out _out20);
        r = _out19;
        resultingOwnership = _out20;
      }
    }
    public void GenExprConvert(DAST._IExpression e, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs0 = e;
      DAST._IExpression _0_expr = _let_tmp_rhs0.dtor_value;
      DAST._IType _1_fromTpe = _let_tmp_rhs0.dtor_from;
      DAST._IType _2_toTpe = _let_tmp_rhs0.dtor_typ;
      Defs._IOwnership _3_argumentOwnership;
      _3_argumentOwnership = expectedOwnership;
      if (object.Equals(_3_argumentOwnership, Defs.Ownership.create_OwnershipAutoBorrowed())) {
        _3_argumentOwnership = Defs.Ownership.create_OwnershipBorrowed();
      }
      RAST._IExpr _4_recursiveGen;
      Defs._IOwnership _5_recOwned;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _6_recIdents;
      RAST._IExpr _out0;
      Defs._IOwnership _out1;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
      (this).GenExpr(_0_expr, selfIdent, env, _3_argumentOwnership, out _out0, out _out1, out _out2);
      _4_recursiveGen = _out0;
      _5_recOwned = _out1;
      _6_recIdents = _out2;
      r = _4_recursiveGen;
      readIdents = _6_recIdents;
      RAST._IExpr _out3;
      Defs._IOwnership _out4;
      (this).GenExprConvertTo(r, _5_recOwned, _1_fromTpe, _2_toTpe, env, expectedOwnership, out _out3, out _out4);
      r = _out3;
      resultingOwnership = _out4;
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _0_tpe;
      _0_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1_placeboOpt;
      if ((_0_tpe).is_Some) {
        _1_placeboOpt = ((_0_tpe).dtor_value).ExtractMaybePlacebo();
      } else {
        _1_placeboOpt = Std.Wrappers.Option<RAST._IType>.create_None();
      }
      bool _2_currentlyBorrowed;
      _2_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _3_noNeedOfClone;
      _3_noNeedOfClone = (env).CanReadWithoutClone(rName);
      bool _4_isSelf;
      _4_isSelf = (((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName));
      if ((_1_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply0();
        _2_currentlyBorrowed = false;
        _3_noNeedOfClone = true;
        _0_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipAutoBorrowed())) {
        if (_2_currentlyBorrowed) {
          resultingOwnership = Defs.Ownership.create_OwnershipBorrowed();
        } else {
          resultingOwnership = Defs.Ownership.create_OwnershipOwned();
        }
      } else if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = Defs.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_0_tpe).is_Some) && (((_0_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = Defs.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipOwned())) {
        bool _5_needsObjectFromRef;
        _5_needsObjectFromRef = (_4_isSelf) && ((selfIdent).IsClassOrObjectTrait());
        bool _6_needsRcWrapping;
        _6_needsRcWrapping = (_4_isSelf) && ((selfIdent).IsRcWrappedDatatype());
        if (_5_needsObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else if (_6_needsRcWrapping) {
          r = Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>((this).rcNew)((r).Clone());
        } else {
          if (!(_3_noNeedOfClone)) {
            bool _7_needUnderscoreClone;
            _7_needUnderscoreClone = (_4_isSelf) && ((selfIdent).IsGeneralTrait());
            if (_7_needUnderscoreClone) {
              RAST._IType _8_traitType;
              RAST._IType _out0;
              _out0 = (this).GenType((selfIdent).dtor_dafnyType, Defs.GenTypeContext.ForTraitParents());
              _8_traitType = _out0;
              Std.Wrappers._IOption<RAST._IExpr> _9_traitExpr;
              _9_traitExpr = (_8_traitType).ToExpr();
              if ((_9_traitExpr).is_None) {
                RAST._IExpr _out1;
                _out1 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not convert "), (_8_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to an expression")), (this).InitEmptyExpr());
                r = _out1;
              } else {
                r = (((_9_traitExpr).dtor_value).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_clone"))).Apply1(r);
              }
            } else {
              r = (r).Clone();
            }
          }
        }
        resultingOwnership = Defs.Ownership.create_OwnershipOwned();
      } else if (_2_currentlyBorrowed) {
        bool _10_needsRcWrapping;
        _10_needsRcWrapping = (_4_isSelf) && ((selfIdent).IsRcWrappedDatatype());
        if (_10_needsRcWrapping) {
          r = RAST.__default.Borrow(Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>((this).rcNew)((r).Clone()));
        }
        resultingOwnership = Defs.Ownership.create_OwnershipBorrowed();
      } else {
        bool _11_selfIsGeneralTrait;
        _11_selfIsGeneralTrait = (_4_isSelf) && (((System.Func<bool>)(() => {
          DAST._IType _source0 = (selfIdent).dtor_dafnyType;
          {
            if (_source0.is_UserDefined) {
              DAST._IResolvedType resolved0 = _source0.dtor_resolved;
              DAST._IResolvedTypeBase _12_base = resolved0.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _13_attributes = resolved0.dtor_attributes;
              return ((_12_base).is_Trait) && (((_12_base).dtor_traitType).is_GeneralTrait);
            }
          }
          {
            return false;
          }
        }))());
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_0_tpe).is_Some) && (((_0_tpe).dtor_value).IsPointer())) {
            r = ((this).read__macro).Apply1(r);
          } else {
            r = RAST.__default.Borrow(r);
          }
        }
        resultingOwnership = Defs.Ownership.create_OwnershipBorrowed();
      }
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(rName);
      return ;
    }
    public bool HasExternAttributeRenamingModule(Dafny.ISequence<DAST._IAttribute> attributes) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_0_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_0_attributes).UniqueElements, false, (((_exists_var_0) => {
        DAST._IAttribute _1_attribute = (DAST._IAttribute)_exists_var_0;
        return ((_0_attributes).Contains(_1_attribute)) && ((((_1_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1_attribute).dtor_args).Count)) == (new BigInteger(2))));
      }))))(attributes);
    }
    public void GenArgs(Defs._ISelfInfo selfIdent, DAST._ICallName name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, Defs._IEnvironment env, out Dafny.ISequence<RAST._IExpr> argExprs, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out Dafny.ISequence<RAST._IType> typeExprs, out Std.Wrappers._IOption<DAST._IResolvedType> fullNameQualifier)
    {
      argExprs = Dafny.Sequence<RAST._IExpr>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      typeExprs = Dafny.Sequence<RAST._IType>.Empty;
      fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.Default();
      argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.ISequence<DAST._IFormal> _0_borrowSignature = Dafny.Sequence<DAST._IFormal>.Empty;
      if ((name).is_CallName) {
        if ((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) {
          _0_borrowSignature = Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature).dtor_inheritedParams);
        } else {
          _0_borrowSignature = ((name).dtor_signature).dtor_inheritedParams;
        }
      } else {
        _0_borrowSignature = Dafny.Sequence<DAST._IFormal>.FromElements();
      }
      BigInteger _hi0 = new BigInteger((args).Count);
      for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
        Defs._IOwnership _2_argOwnership;
        _2_argOwnership = Defs.Ownership.create_OwnershipBorrowed();
        if ((_1_i) < (new BigInteger((_0_borrowSignature).Count))) {
          RAST._IType _3_tpe;
          RAST._IType _out0;
          _out0 = (this).GenType(((_0_borrowSignature).Select(_1_i)).dtor_typ, Defs.GenTypeContext.@default());
          _3_tpe = _out0;
          if ((_3_tpe).CanReadWithoutClone()) {
            _2_argOwnership = Defs.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _4_argExpr;
        Defs._IOwnership _5___v62;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _6_argIdents;
        RAST._IExpr _out1;
        Defs._IOwnership _out2;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out3;
        (this).GenExpr((args).Select(_1_i), selfIdent, env, _2_argOwnership, out _out1, out _out2, out _out3);
        _4_argExpr = _out1;
        _5___v62 = _out2;
        _6_argIdents = _out3;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_4_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _6_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi1 = new BigInteger((typeArgs).Count);
      for (BigInteger _7_typeI = BigInteger.Zero; _7_typeI < _hi1; _7_typeI++) {
        RAST._IType _8_typeExpr;
        RAST._IType _out4;
        _out4 = (this).GenType((typeArgs).Select(_7_typeI), Defs.GenTypeContext.@default());
        _8_typeExpr = _out4;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_8_typeExpr));
      }
      DAST._ICallName _source0 = name;
      {
        if (_source0.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _9_nameIdent = _source0.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType0 = _source0.dtor_onType;
          if (onType0.is_Some) {
            DAST._IType value0 = onType0.dtor_value;
            if (value0.is_UserDefined) {
              DAST._IResolvedType _10_resolvedType = value0.dtor_resolved;
              if (((((_10_resolvedType).dtor_kind).is_Trait) || ((Defs.__default.builtin__trait__preferred__methods).Contains((_9_nameIdent)))) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_11_resolvedType, _12_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_12_nameIdent), true, (((_forall_var_0) => {
                Dafny.ISequence<Dafny.Rune> _13_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_0;
                return !(((_11_resolvedType).dtor_properMethods).Contains(_13_m)) || (!object.Equals(_13_m, _12_nameIdent));
              }))))(_10_resolvedType, _9_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(Defs.__default.TraitTypeContainingMethod(_10_resolvedType, (_9_nameIdent)), _10_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
              goto after_match0;
            }
          }
        }
      }
      {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    after_match0: ;
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      DAST._ICallName _source0 = name;
      {
        if (_source0.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _0_ident = _source0.dtor_name;
          if ((@on).is_ExternCompanion) {
            return (_0_ident);
          } else {
            return Defs.__default.escapeName(_0_ident);
          }
        }
      }
      {
        bool disjunctiveMatch0 = false;
        if (_source0.is_MapBuilderAdd) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetBuilderAdd) {
          disjunctiveMatch0 = true;
        }
        if (disjunctiveMatch0) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
      }
    }
    public RAST._IExpr LambdaWrapRc(RAST._IExpr rInput)
    {
      RAST._IExpr r = RAST.Expr.Default();
      Dafny.ISequence<RAST._IType> _0_typeShapeArgs;
      _0_typeShapeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi0 = new BigInteger(((rInput).dtor_params).Count);
      for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
        RAST._IType _2_typeShapeArg;
        if (((((rInput).dtor_params).Select(_1_i)).dtor_tpe).is_Borrowed) {
          _2_typeShapeArg = RAST.Type.create_Borrowed(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")));
        } else {
          _2_typeShapeArg = RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        }
        _0_typeShapeArgs = Dafny.Sequence<RAST._IType>.Concat(_0_typeShapeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2_typeShapeArg));
      }
      RAST._IType _3_typeShape;
      _3_typeShape = RAST.Type.create_DynType(RAST.Type.create_FnType(_0_typeShapeArgs, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))));
      if (((this).syncType).is_Sync) {
        _3_typeShape = RAST.Type.create_IntersectionType(_3_typeShape, (this).SyncSendType);
      }
      r = RAST.Expr.create_TypeAscription(Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>((this).rcNew)(rInput), Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>((this).rc)(_3_typeShape));
      return r;
    }
    public void GenExpr(DAST._IExpression e, Defs._ISelfInfo selfIdent, Defs._IEnvironment env, Defs._IOwnership expectedOwnership, out RAST._IExpr r, out Defs._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = Defs.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source0 = e;
      {
        if (_source0.is_Literal) {
          RAST._IExpr _out0;
          Defs._IOwnership _out1;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out0, out _out1, out _out2);
          r = _out0;
          resultingOwnership = _out1;
          readIdents = _out2;
          goto after_match0;
        }
      }
      {
        if (_source0.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
          {
            RAST._IExpr _out3;
            Defs._IOwnership _out4;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out5;
            (this).GenIdent(Defs.__default.escapeVar(_0_name), selfIdent, env, expectedOwnership, out _out3, out _out4, out _out5);
            r = _out3;
            resultingOwnership = _out4;
            readIdents = _out5;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1_path = _source0.dtor_ExternCompanion_a0;
          {
            RAST._IExpr _out6;
            _out6 = (this).GenPathExpr(_1_path, false);
            r = _out6;
            if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = Defs.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipOwned())) {
              resultingOwnership = Defs.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out7;
              Defs._IOwnership _out8;
              (this).FromOwned(r, expectedOwnership, out _out7, out _out8);
              r = _out7;
              resultingOwnership = _out8;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2_path = _source0.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _3_typeArgs = _source0.dtor_typeArgs;
          {
            RAST._IExpr _out9;
            _out9 = (this).GenPathExpr(_2_path, true);
            r = _out9;
            if ((new BigInteger((_3_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _4_typeExprs;
              _4_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi0 = new BigInteger((_3_typeArgs).Count);
              for (BigInteger _5_i = BigInteger.Zero; _5_i < _hi0; _5_i++) {
                RAST._IType _6_typeExpr;
                RAST._IType _out10;
                _out10 = (this).GenType((_3_typeArgs).Select(_5_i), Defs.GenTypeContext.@default());
                _6_typeExpr = _out10;
                _4_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_4_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_6_typeExpr));
              }
              r = (r).ApplyType(_4_typeExprs);
            }
            if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = Defs.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipOwned())) {
              resultingOwnership = Defs.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out11;
              Defs._IOwnership _out12;
              (this).FromOwned(r, expectedOwnership, out _out11, out _out12);
              r = _out11;
              resultingOwnership = _out12;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_InitializationValue) {
          DAST._IType _7_typ = _source0.dtor_typ;
          {
            RAST._IType _8_typExpr;
            RAST._IType _out13;
            _out13 = (this).GenType(_7_typ, Defs.GenTypeContext.@default());
            _8_typExpr = _out13;
            r = ((RAST.Expr.create_TraitCast(_8_typExpr, RAST.__default.DefaultTrait)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).Apply0();
            RAST._IExpr _out14;
            Defs._IOwnership _out15;
            (this).FromOwned(r, expectedOwnership, out _out14, out _out15);
            r = _out14;
            resultingOwnership = _out15;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _9_values = _source0.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IExpr> _10_exprs;
            _10_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi1 = new BigInteger((_9_values).Count);
            for (BigInteger _11_i = BigInteger.Zero; _11_i < _hi1; _11_i++) {
              RAST._IExpr _12_recursiveGen;
              Defs._IOwnership _13___v72;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _14_recIdents;
              RAST._IExpr _out16;
              Defs._IOwnership _out17;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out18;
              (this).GenExpr((_9_values).Select(_11_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out16, out _out17, out _out18);
              _12_recursiveGen = _out16;
              _13___v72 = _out17;
              _14_recIdents = _out18;
              _10_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_10_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_12_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _14_recIdents);
            }
            if ((new BigInteger((_9_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              r = RAST.Expr.create_Tuple(_10_exprs);
            } else {
              r = RAST.__default.SystemTuple(_10_exprs);
            }
            RAST._IExpr _out19;
            Defs._IOwnership _out20;
            (this).FromOwned(r, expectedOwnership, out _out19, out _out20);
            r = _out19;
            resultingOwnership = _out20;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _15_path = _source0.dtor_path;
          Dafny.ISequence<DAST._IType> _16_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _17_args = _source0.dtor_args;
          {
            RAST._IExpr _out21;
            _out21 = (this).GenPathExpr(_15_path, true);
            r = _out21;
            if ((new BigInteger((_16_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _18_typeExprs;
              _18_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi2 = new BigInteger((_16_typeArgs).Count);
              for (BigInteger _19_i = BigInteger.Zero; _19_i < _hi2; _19_i++) {
                RAST._IType _20_typeExpr;
                RAST._IType _out22;
                _out22 = (this).GenType((_16_typeArgs).Select(_19_i), Defs.GenTypeContext.@default());
                _20_typeExpr = _out22;
                _18_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_18_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_20_typeExpr));
              }
              r = (r).ApplyType(_18_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _21_arguments;
            _21_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi3 = new BigInteger((_17_args).Count);
            for (BigInteger _22_i = BigInteger.Zero; _22_i < _hi3; _22_i++) {
              RAST._IExpr _23_recursiveGen;
              Defs._IOwnership _24___v73;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _25_recIdents;
              RAST._IExpr _out23;
              Defs._IOwnership _out24;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out25;
              (this).GenExpr((_17_args).Select(_22_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out23, out _out24, out _out25);
              _23_recursiveGen = _out23;
              _24___v73 = _out24;
              _25_recIdents = _out25;
              _21_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_21_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_23_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _25_recIdents);
            }
            r = (r).Apply(_21_arguments);
            RAST._IExpr _out26;
            Defs._IOwnership _out27;
            (this).FromOwned(r, expectedOwnership, out _out26, out _out27);
            r = _out26;
            resultingOwnership = _out27;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _26_dims = _source0.dtor_dims;
          DAST._IType _27_typ = _source0.dtor_typ;
          {
            if ((new BigInteger(16)) < (new BigInteger((_26_dims).Count))) {
              RAST._IExpr _out28;
              _out28 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions"), (this).InitEmptyExpr());
              r = _out28;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = (this).InitEmptyExpr();
              RAST._IType _28_typeGen;
              RAST._IType _out29;
              _out29 = (this).GenType(_27_typ, Defs.GenTypeContext.@default());
              _28_typeGen = _out29;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _29_dimExprs;
              _29_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi4 = new BigInteger((_26_dims).Count);
              for (BigInteger _30_i = BigInteger.Zero; _30_i < _hi4; _30_i++) {
                RAST._IExpr _31_recursiveGen;
                Defs._IOwnership _32___v74;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _33_recIdents;
                RAST._IExpr _out30;
                Defs._IOwnership _out31;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
                (this).GenExpr((_26_dims).Select(_30_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
                _31_recursiveGen = _out30;
                _32___v74 = _out31;
                _33_recIdents = _out32;
                _29_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_29_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_31_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _33_recIdents);
              }
              if ((new BigInteger((_26_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _34_class__name;
                _34_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_26_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_34_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_28_typeGen))).FSel((this).placebos__usize)).Apply(_29_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_28_typeGen))).Apply(_29_dimExprs);
              }
            }
            RAST._IExpr _out33;
            Defs._IOwnership _out34;
            (this).FromOwned(r, expectedOwnership, out _out33, out _out34);
            r = _out33;
            resultingOwnership = _out34;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ArrayIndexToInt) {
          DAST._IExpression _35_underlying = _source0.dtor_value;
          {
            RAST._IExpr _36_recursiveGen;
            Defs._IOwnership _37___v75;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _38_recIdents;
            RAST._IExpr _out35;
            Defs._IOwnership _out36;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out37;
            (this).GenExpr(_35_underlying, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out35, out _out36, out _out37);
            _36_recursiveGen = _out35;
            _37___v75 = _out36;
            _38_recIdents = _out37;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_36_recursiveGen);
            readIdents = _38_recIdents;
            RAST._IExpr _out38;
            Defs._IOwnership _out39;
            (this).FromOwned(r, expectedOwnership, out _out38, out _out39);
            r = _out38;
            resultingOwnership = _out39;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_FinalizeNewArray) {
          DAST._IExpression _39_underlying = _source0.dtor_value;
          DAST._IType _40_typ = _source0.dtor_typ;
          {
            RAST._IType _41_tpe;
            RAST._IType _out40;
            _out40 = (this).GenType(_40_typ, Defs.GenTypeContext.@default());
            _41_tpe = _out40;
            RAST._IExpr _42_recursiveGen;
            Defs._IOwnership _43___v76;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _44_recIdents;
            RAST._IExpr _out41;
            Defs._IOwnership _out42;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out43;
            (this).GenExpr(_39_underlying, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out41, out _out42, out _out43);
            _42_recursiveGen = _out41;
            _43___v76 = _out42;
            _44_recIdents = _out43;
            readIdents = _44_recIdents;
            if ((_41_tpe).IsObjectOrPointer()) {
              RAST._IType _45_t;
              _45_t = (_41_tpe).ObjectOrPointerUnderlying();
              if ((_45_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_42_recursiveGen);
              } else if ((_45_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _46_c;
                _46_c = (_45_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_46_c)).AsExpr()).FSel((this).array__construct)).Apply1(_42_recursiveGen);
              } else {
                RAST._IExpr _out44;
                _out44 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_41_tpe)._ToString(Defs.__default.IND)), (this).InitEmptyExpr());
                r = _out44;
              }
            } else {
              RAST._IExpr _out45;
              _out45 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_41_tpe)._ToString(Defs.__default.IND)), (this).InitEmptyExpr());
              r = _out45;
            }
            RAST._IExpr _out46;
            Defs._IOwnership _out47;
            (this).FromOwned(r, expectedOwnership, out _out46, out _out47);
            r = _out46;
            resultingOwnership = _out47;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_DatatypeValue) {
          DAST._IResolvedType _47_datatypeType = _source0.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _48_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _49_variant = _source0.dtor_variant;
          bool _50_isCo = _source0.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _51_values = _source0.dtor_contents;
          {
            RAST._IExpr _out48;
            _out48 = (this).GenPathExpr((_47_datatypeType).dtor_path, true);
            r = _out48;
            Dafny.ISequence<RAST._IType> _52_genTypeArgs;
            _52_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi5 = new BigInteger((_48_typeArgs).Count);
            for (BigInteger _53_i = BigInteger.Zero; _53_i < _hi5; _53_i++) {
              RAST._IType _54_typeExpr;
              RAST._IType _out49;
              _out49 = (this).GenType((_48_typeArgs).Select(_53_i), Defs.GenTypeContext.@default());
              _54_typeExpr = _out49;
              _52_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_52_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_54_typeExpr));
            }
            r = (r).FSel(Defs.__default.escapeName(_49_variant));
            if ((new BigInteger((_48_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_52_genTypeArgs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _55_assignments;
            _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi6 = new BigInteger((_51_values).Count);
            for (BigInteger _56_i = BigInteger.Zero; _56_i < _hi6; _56_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_51_values).Select(_56_i);
              Dafny.ISequence<Dafny.Rune> _57_name = _let_tmp_rhs0.dtor__0;
              DAST._IExpression _58_value = _let_tmp_rhs0.dtor__1;
              if (_50_isCo) {
                RAST._IExpr _59_recursiveGen;
                Defs._IOwnership _60___v77;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _61_recIdents;
                RAST._IExpr _out50;
                Defs._IOwnership _out51;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out52;
                (this).GenExpr(_58_value, selfIdent, Defs.Environment.Empty(), Defs.Ownership.create_OwnershipOwned(), out _out50, out _out51, out _out52);
                _59_recursiveGen = _out50;
                _60___v77 = _out51;
                _61_recIdents = _out52;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _61_recIdents);
                RAST._IExpr _62_allReadCloned;
                _62_allReadCloned = (this).InitEmptyExpr();
                while (!(_61_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _63_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_61_recIdents).Elements) {
                    _63_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                    if ((_61_recIdents).Contains(_63_next)) {
                      goto after__ASSIGN_SUCH_THAT_0;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value");
                after__ASSIGN_SUCH_THAT_0: ;
                  _62_allReadCloned = (_62_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _63_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some((RAST.Expr.create_Identifier(_63_next)).Clone())));
                  _61_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_61_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_63_next));
                }
                RAST._IExpr _64_wasAssigned;
                _64_wasAssigned = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsExpr()).Apply1(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Lazy"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply1((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("boxed"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Box"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply1((_62_allReadCloned).Then(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_None(), _59_recursiveGen)))));
                _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_55_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Defs.__default.escapeVar(_57_name), _64_wasAssigned)));
              } else {
                RAST._IExpr _65_recursiveGen;
                Defs._IOwnership _66___v78;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _67_recIdents;
                RAST._IExpr _out53;
                Defs._IOwnership _out54;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
                (this).GenExpr(_58_value, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out53, out _out54, out _out55);
                _65_recursiveGen = _out53;
                _66___v78 = _out54;
                _67_recIdents = _out55;
                _55_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_55_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Defs.__default.escapeVar(_57_name), _65_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _67_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _55_assignments);
            if (Defs.__default.IsRcWrapped((_47_datatypeType).dtor_attributes)) {
              r = Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>((this).rcNew)(r);
            }
            RAST._IExpr _out56;
            Defs._IOwnership _out57;
            (this).FromOwned(r, expectedOwnership, out _out56, out _out57);
            r = _out56;
            resultingOwnership = _out57;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Convert) {
          {
            RAST._IExpr _out58;
            Defs._IOwnership _out59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out58, out _out59, out _out60);
            r = _out58;
            resultingOwnership = _out59;
            readIdents = _out60;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqConstruct) {
          DAST._IExpression _68_length = _source0.dtor_length;
          DAST._IExpression _69_expr = _source0.dtor_elem;
          {
            RAST._IExpr _70_recursiveGen;
            Defs._IOwnership _71___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _72_recIdents;
            RAST._IExpr _out61;
            Defs._IOwnership _out62;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
            (this).GenExpr(_69_expr, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out61, out _out62, out _out63);
            _70_recursiveGen = _out61;
            _71___v82 = _out62;
            _72_recIdents = _out63;
            RAST._IExpr _73_lengthGen;
            Defs._IOwnership _74___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _75_lengthIdents;
            RAST._IExpr _out64;
            Defs._IOwnership _out65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
            (this).GenExpr(_68_length, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out64, out _out65, out _out66);
            _73_lengthGen = _out64;
            _74___v83 = _out65;
            _75_lengthIdents = _out66;
            r = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_initializer"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_70_recursiveGen));
            RAST._IExpr _76_range;
            _76_range = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr();
            _76_range = (_76_range).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Zero"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("zero"))).Apply0(), _73_lengthGen));
            _76_range = (_76_range).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map"));
            RAST._IExpr _77_rangeMap;
            _77_rangeMap = RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.ImplicitlyTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i"))), Std.Wrappers.Option<RAST._IType>.create_None(), (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_initializer"))).Apply1(RAST.__default.Borrow(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i")))));
            _76_range = (_76_range).Apply1(_77_rangeMap);
            _76_range = (((_76_range).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("collect"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))))).Apply0();
            r = RAST.Expr.create_Block((r).Then(_76_range));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_72_recIdents, _75_lengthIdents);
            RAST._IExpr _out67;
            Defs._IOwnership _out68;
            (this).FromOwned(r, expectedOwnership, out _out67, out _out68);
            r = _out67;
            resultingOwnership = _out68;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _78_exprs = _source0.dtor_elements;
          DAST._IType _79_typ = _source0.dtor_typ;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _80_genTpe;
            RAST._IType _out69;
            _out69 = (this).GenType(_79_typ, Defs.GenTypeContext.@default());
            _80_genTpe = _out69;
            BigInteger _81_i;
            _81_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _82_args;
            _82_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_81_i) < (new BigInteger((_78_exprs).Count))) {
              RAST._IExpr _83_recursiveGen;
              Defs._IOwnership _84___v84;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _85_recIdents;
              RAST._IExpr _out70;
              Defs._IOwnership _out71;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out72;
              (this).GenExpr((_78_exprs).Select(_81_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out70, out _out71, out _out72);
              _83_recursiveGen = _out70;
              _84___v84 = _out71;
              _85_recIdents = _out72;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _85_recIdents);
              _82_args = Dafny.Sequence<RAST._IExpr>.Concat(_82_args, Dafny.Sequence<RAST._IExpr>.FromElements(_83_recursiveGen));
              _81_i = (_81_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_82_args);
            if ((new BigInteger((_82_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_80_genTpe));
            }
            RAST._IExpr _out73;
            Defs._IOwnership _out74;
            (this).FromOwned(r, expectedOwnership, out _out73, out _out74);
            r = _out73;
            resultingOwnership = _out74;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _86_exprs = _source0.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _87_generatedValues;
            _87_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _88_i;
            _88_i = BigInteger.Zero;
            while ((_88_i) < (new BigInteger((_86_exprs).Count))) {
              RAST._IExpr _89_recursiveGen;
              Defs._IOwnership _90___v85;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _91_recIdents;
              RAST._IExpr _out75;
              Defs._IOwnership _out76;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out77;
              (this).GenExpr((_86_exprs).Select(_88_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out75, out _out76, out _out77);
              _89_recursiveGen = _out75;
              _90___v85 = _out76;
              _91_recIdents = _out77;
              _87_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_87_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_89_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _91_recIdents);
              _88_i = (_88_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_87_generatedValues);
            RAST._IExpr _out78;
            Defs._IOwnership _out79;
            (this).FromOwned(r, expectedOwnership, out _out78, out _out79);
            r = _out78;
            resultingOwnership = _out79;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _92_exprs = _source0.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _93_generatedValues;
            _93_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _94_i;
            _94_i = BigInteger.Zero;
            while ((_94_i) < (new BigInteger((_92_exprs).Count))) {
              RAST._IExpr _95_recursiveGen;
              Defs._IOwnership _96___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _97_recIdents;
              RAST._IExpr _out80;
              Defs._IOwnership _out81;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out82;
              (this).GenExpr((_92_exprs).Select(_94_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out80, out _out81, out _out82);
              _95_recursiveGen = _out80;
              _96___v86 = _out81;
              _97_recIdents = _out82;
              _93_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_93_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_95_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _97_recIdents);
              _94_i = (_94_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_93_generatedValues);
            RAST._IExpr _out83;
            Defs._IOwnership _out84;
            (this).FromOwned(r, expectedOwnership, out _out83, out _out84);
            r = _out83;
            resultingOwnership = _out84;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ToMultiset) {
          DAST._IExpression _98_expr = _source0.dtor_ToMultiset_a0;
          {
            RAST._IExpr _99_recursiveGen;
            Defs._IOwnership _100___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _101_recIdents;
            RAST._IExpr _out85;
            Defs._IOwnership _out86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out87;
            (this).GenExpr(_98_expr, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out85, out _out86, out _out87);
            _99_recursiveGen = _out85;
            _100___v87 = _out86;
            _101_recIdents = _out87;
            r = ((_99_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply0();
            readIdents = _101_recIdents;
            RAST._IExpr _out88;
            Defs._IOwnership _out89;
            (this).FromOwned(r, expectedOwnership, out _out88, out _out89);
            r = _out88;
            resultingOwnership = _out89;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _102_mapElems = _source0.dtor_mapElems;
          DAST._IType _103_rangeType = _source0.dtor_domainType;
          DAST._IType _104_domainType = _source0.dtor_rangeType;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _105_generatedValues;
            _105_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi7 = new BigInteger((_102_mapElems).Count);
            for (BigInteger _106_i = BigInteger.Zero; _106_i < _hi7; _106_i++) {
              RAST._IExpr _107_recursiveGenKey;
              Defs._IOwnership _108___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _109_recIdentsKey;
              RAST._IExpr _out90;
              Defs._IOwnership _out91;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out92;
              (this).GenExpr(((_102_mapElems).Select(_106_i)).dtor__0, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out90, out _out91, out _out92);
              _107_recursiveGenKey = _out90;
              _108___v88 = _out91;
              _109_recIdentsKey = _out92;
              RAST._IExpr _110_recursiveGenValue;
              Defs._IOwnership _111___v89;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _112_recIdentsValue;
              RAST._IExpr _out93;
              Defs._IOwnership _out94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out95;
              (this).GenExpr(((_102_mapElems).Select(_106_i)).dtor__1, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out93, out _out94, out _out95);
              _110_recursiveGenValue = _out93;
              _111___v89 = _out94;
              _112_recIdentsValue = _out95;
              _105_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_105_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_107_recursiveGenKey, _110_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _109_recIdentsKey), _112_recIdentsValue);
            }
            Dafny.ISequence<RAST._IExpr> _113_arguments;
            _113_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi8 = new BigInteger((_105_generatedValues).Count);
            for (BigInteger _114_i = BigInteger.Zero; _114_i < _hi8; _114_i++) {
              RAST._IExpr _115_genKey;
              _115_genKey = ((_105_generatedValues).Select(_114_i)).dtor__0;
              RAST._IExpr _116_genValue;
              _116_genValue = ((_105_generatedValues).Select(_114_i)).dtor__1;
              _113_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_113_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _115_genKey, _116_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_113_arguments);
            if ((new BigInteger((_105_generatedValues).Count)).Sign == 0) {
              RAST._IType _117_rangeTpe;
              RAST._IType _out96;
              _out96 = (this).GenType(_103_rangeType, Defs.GenTypeContext.@default());
              _117_rangeTpe = _out96;
              RAST._IType _118_domainTpe;
              RAST._IType _out97;
              _out97 = (this).GenType(_104_domainType, Defs.GenTypeContext.@default());
              _118_domainTpe = _out97;
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_117_rangeTpe, _118_domainTpe)));
            }
            RAST._IExpr _out98;
            Defs._IOwnership _out99;
            (this).FromOwned(r, expectedOwnership, out _out98, out _out99);
            r = _out98;
            resultingOwnership = _out99;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqUpdate) {
          DAST._IExpression _119_expr = _source0.dtor_expr;
          DAST._IExpression _120_index = _source0.dtor_indexExpr;
          DAST._IExpression _121_value = _source0.dtor_value;
          DAST._IType _122_collectionType = _source0.dtor_collectionType;
          DAST._IType _123_exprType = _source0.dtor_exprType;
          {
            RAST._IExpr _124_exprR;
            Defs._IOwnership _125___v90;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _126_exprIdents;
            RAST._IExpr _out100;
            Defs._IOwnership _out101;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
            (this).GenExpr(_119_expr, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out100, out _out101, out _out102);
            _124_exprR = _out100;
            _125___v90 = _out101;
            _126_exprIdents = _out102;
            RAST._IExpr _127_indexR;
            Defs._IOwnership _128_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _129_indexIdents;
            RAST._IExpr _out103;
            Defs._IOwnership _out104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out105;
            (this).GenExpr(_120_index, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out103, out _out104, out _out105);
            _127_indexR = _out103;
            _128_indexOwnership = _out104;
            _129_indexIdents = _out105;
            RAST._IExpr _130_valueR;
            Defs._IOwnership _131_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _132_valueIdents;
            RAST._IExpr _out106;
            Defs._IOwnership _out107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
            (this).GenExpr(_121_value, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out106, out _out107, out _out108);
            _130_valueR = _out106;
            _131_valueOwnership = _out107;
            _132_valueIdents = _out108;
            r = ((_124_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_127_indexR, _130_valueR));
            RAST._IExpr _out109;
            Defs._IOwnership _out110;
            (this).GenExprConvertTo(r, Defs.Ownership.create_OwnershipOwned(), _122_collectionType, _123_exprType, env, expectedOwnership, out _out109, out _out110);
            r = _out109;
            resultingOwnership = _out110;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_126_exprIdents, _129_indexIdents), _132_valueIdents);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapUpdate) {
          DAST._IExpression _133_expr = _source0.dtor_expr;
          DAST._IExpression _134_index = _source0.dtor_indexExpr;
          DAST._IExpression _135_value = _source0.dtor_value;
          DAST._IType _136_collectionType = _source0.dtor_collectionType;
          DAST._IType _137_exprType = _source0.dtor_exprType;
          {
            RAST._IExpr _138_exprR;
            Defs._IOwnership _139___v91;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _140_exprIdents;
            RAST._IExpr _out111;
            Defs._IOwnership _out112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
            (this).GenExpr(_133_expr, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out111, out _out112, out _out113);
            _138_exprR = _out111;
            _139___v91 = _out112;
            _140_exprIdents = _out113;
            RAST._IExpr _141_indexR;
            Defs._IOwnership _142_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _143_indexIdents;
            RAST._IExpr _out114;
            Defs._IOwnership _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenExpr(_134_index, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out114, out _out115, out _out116);
            _141_indexR = _out114;
            _142_indexOwnership = _out115;
            _143_indexIdents = _out116;
            RAST._IExpr _144_valueR;
            Defs._IOwnership _145_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _146_valueIdents;
            RAST._IExpr _out117;
            Defs._IOwnership _out118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
            (this).GenExpr(_135_value, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out117, out _out118, out _out119);
            _144_valueR = _out117;
            _145_valueOwnership = _out118;
            _146_valueIdents = _out119;
            r = ((_138_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_141_indexR, _144_valueR));
            RAST._IExpr _out120;
            Defs._IOwnership _out121;
            (this).GenExprConvertTo(r, Defs.Ownership.create_OwnershipOwned(), _136_collectionType, _137_exprType, env, expectedOwnership, out _out120, out _out121);
            r = _out120;
            resultingOwnership = _out121;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_140_exprIdents, _143_indexIdents), _146_valueIdents);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_This) {
          {
            Defs._ISelfInfo _source1 = selfIdent;
            {
              if (_source1.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _147_id = _source1.dtor_rSelfName;
                DAST._IType _148_dafnyType = _source1.dtor_dafnyType;
                {
                  RAST._IExpr _out122;
                  Defs._IOwnership _out123;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
                  (this).GenIdent(_147_id, selfIdent, env, expectedOwnership, out _out122, out _out123, out _out124);
                  r = _out122;
                  resultingOwnership = _out123;
                  readIdents = _out124;
                  return ;
                }
                goto after_match1;
              }
            }
            {
              Defs._ISelfInfo _149_None = _source1;
              {
                RAST._IExpr _out125;
                _out125 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this outside of a method"), (this).InitEmptyExpr());
                r = _out125;
                RAST._IExpr _out126;
                Defs._IOwnership _out127;
                (this).FromOwned(r, expectedOwnership, out _out126, out _out127);
                r = _out126;
                resultingOwnership = _out127;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
          after_match1: ;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Ite) {
          DAST._IExpression _150_cond = _source0.dtor_cond;
          DAST._IExpression _151_t = _source0.dtor_thn;
          DAST._IExpression _152_f = _source0.dtor_els;
          {
            RAST._IExpr _153_cond;
            Defs._IOwnership _154___v92;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _155_recIdentsCond;
            RAST._IExpr _out128;
            Defs._IOwnership _out129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
            (this).GenExpr(_150_cond, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
            _153_cond = _out128;
            _154___v92 = _out129;
            _155_recIdentsCond = _out130;
            RAST._IExpr _156_fExpr;
            Defs._IOwnership _157_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _158_recIdentsF;
            RAST._IExpr _out131;
            Defs._IOwnership _out132;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out133;
            (this).GenExpr(_152_f, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out131, out _out132, out _out133);
            _156_fExpr = _out131;
            _157_fOwned = _out132;
            _158_recIdentsF = _out133;
            RAST._IExpr _159_tExpr;
            Defs._IOwnership _160___v93;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _161_recIdentsT;
            RAST._IExpr _out134;
            Defs._IOwnership _out135;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
            (this).GenExpr(_151_t, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out134, out _out135, out _out136);
            _159_tExpr = _out134;
            _160___v93 = _out135;
            _161_recIdentsT = _out136;
            r = RAST.Expr.create_IfExpr(_153_cond, _159_tExpr, _156_fExpr);
            RAST._IExpr _out137;
            Defs._IOwnership _out138;
            (this).FromOwnership(r, Defs.Ownership.create_OwnershipOwned(), expectedOwnership, out _out137, out _out138);
            r = _out137;
            resultingOwnership = _out138;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_155_recIdentsCond, _161_recIdentsT), _158_recIdentsF);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source0.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _162_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _163_format = _source0.dtor_format1;
            {
              RAST._IExpr _164_recursiveGen;
              Defs._IOwnership _165___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _166_recIdents;
              RAST._IExpr _out139;
              Defs._IOwnership _out140;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
              (this).GenExpr(_162_e, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
              _164_recursiveGen = _out139;
              _165___v94 = _out140;
              _166_recIdents = _out141;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _164_recursiveGen, _163_format);
              RAST._IExpr _out142;
              Defs._IOwnership _out143;
              (this).FromOwned(r, expectedOwnership, out _out142, out _out143);
              r = _out142;
              resultingOwnership = _out143;
              readIdents = _166_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source0.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _167_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _168_format = _source0.dtor_format1;
            {
              RAST._IExpr _169_recursiveGen;
              Defs._IOwnership _170___v95;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _171_recIdents;
              RAST._IExpr _out144;
              Defs._IOwnership _out145;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out146;
              (this).GenExpr(_167_e, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out144, out _out145, out _out146);
              _169_recursiveGen = _out144;
              _170___v95 = _out145;
              _171_recIdents = _out146;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _169_recursiveGen, _168_format);
              RAST._IExpr _out147;
              Defs._IOwnership _out148;
              (this).FromOwned(r, expectedOwnership, out _out147, out _out148);
              r = _out147;
              resultingOwnership = _out148;
              readIdents = _171_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source0.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _172_e = _source0.dtor_expr;
            DAST.Format._IUnaryOpFormat _173_format = _source0.dtor_format1;
            {
              RAST._IExpr _174_recursiveGen;
              Defs._IOwnership _175_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _176_recIdents;
              RAST._IExpr _out149;
              Defs._IOwnership _out150;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out151;
              (this).GenExpr(_172_e, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out149, out _out150, out _out151);
              _174_recursiveGen = _out149;
              _175_recOwned = _out150;
              _176_recIdents = _out151;
              r = ((_174_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply0();
              RAST._IExpr _out152;
              Defs._IOwnership _out153;
              (this).FromOwned(r, expectedOwnership, out _out152, out _out153);
              r = _out152;
              resultingOwnership = _out153;
              readIdents = _176_recIdents;
              return ;
            }
            goto after_match0;
          }
        }
      }
      {
        if (_source0.is_BinOp) {
          RAST._IExpr _out154;
          Defs._IOwnership _out155;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out154, out _out155, out _out156);
          r = _out154;
          resultingOwnership = _out155;
          readIdents = _out156;
          goto after_match0;
        }
      }
      {
        if (_source0.is_ArrayLen) {
          DAST._IExpression _177_expr = _source0.dtor_expr;
          DAST._IType _178_exprType = _source0.dtor_exprType;
          BigInteger _179_dim = _source0.dtor_dim;
          bool _180_native = _source0.dtor_native;
          {
            RAST._IExpr _181_recursiveGen;
            Defs._IOwnership _182___v100;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _183_recIdents;
            RAST._IExpr _out157;
            Defs._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr(_177_expr, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _181_recursiveGen = _out157;
            _182___v100 = _out158;
            _183_recIdents = _out159;
            RAST._IType _184_arrayType;
            RAST._IType _out160;
            _out160 = (this).GenType(_178_exprType, Defs.GenTypeContext.@default());
            _184_arrayType = _out160;
            if (!((_184_arrayType).IsObjectOrPointer())) {
              RAST._IExpr _out161;
              _out161 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_184_arrayType)._ToString(Defs.__default.IND)), (this).InitEmptyExpr());
              r = _out161;
            } else {
              RAST._IType _185_underlying;
              _185_underlying = (_184_arrayType).ObjectOrPointerUnderlying();
              if (((_179_dim).Sign == 0) && ((_185_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_181_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0();
              } else {
                if ((_179_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_181_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply0();
                } else {
                  r = ((((this).read__macro).Apply1(_181_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_179_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply0();
                }
              }
              if (!(_180_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out162;
            Defs._IOwnership _out163;
            (this).FromOwned(r, expectedOwnership, out _out162, out _out163);
            r = _out162;
            resultingOwnership = _out163;
            readIdents = _183_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapKeys) {
          DAST._IExpression _186_expr = _source0.dtor_expr;
          {
            RAST._IExpr _187_recursiveGen;
            Defs._IOwnership _188___v101;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _189_recIdents;
            RAST._IExpr _out164;
            Defs._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_186_expr, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out164, out _out165, out _out166);
            _187_recursiveGen = _out164;
            _188___v101 = _out165;
            _189_recIdents = _out166;
            readIdents = _189_recIdents;
            r = ((_187_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply0();
            RAST._IExpr _out167;
            Defs._IOwnership _out168;
            (this).FromOwned(r, expectedOwnership, out _out167, out _out168);
            r = _out167;
            resultingOwnership = _out168;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapValues) {
          DAST._IExpression _190_expr = _source0.dtor_expr;
          {
            RAST._IExpr _191_recursiveGen;
            Defs._IOwnership _192___v102;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _193_recIdents;
            RAST._IExpr _out169;
            Defs._IOwnership _out170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
            (this).GenExpr(_190_expr, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out169, out _out170, out _out171);
            _191_recursiveGen = _out169;
            _192___v102 = _out170;
            _193_recIdents = _out171;
            readIdents = _193_recIdents;
            r = ((_191_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply0();
            RAST._IExpr _out172;
            Defs._IOwnership _out173;
            (this).FromOwned(r, expectedOwnership, out _out172, out _out173);
            r = _out172;
            resultingOwnership = _out173;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapItems) {
          DAST._IExpression _194_expr = _source0.dtor_expr;
          {
            RAST._IExpr _195_recursiveGen;
            Defs._IOwnership _196___v103;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _197_recIdents;
            RAST._IExpr _out174;
            Defs._IOwnership _out175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
            (this).GenExpr(_194_expr, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out174, out _out175, out _out176);
            _195_recursiveGen = _out174;
            _196___v103 = _out175;
            _197_recIdents = _out176;
            readIdents = _197_recIdents;
            r = ((_195_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply0();
            RAST._IExpr _out177;
            Defs._IOwnership _out178;
            (this).FromOwned(r, expectedOwnership, out _out177, out _out178);
            r = _out177;
            resultingOwnership = _out178;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SelectFn) {
          DAST._IExpression _198_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _199_field = _source0.dtor_field;
          bool _200_isDatatype = _source0.dtor_onDatatype;
          bool _201_isStatic = _source0.dtor_isStatic;
          bool _202_isConstant = _source0.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _203_arguments = _source0.dtor_arguments;
          {
            RAST._IExpr _204_onExpr;
            Defs._IOwnership _205_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _206_recIdents;
            RAST._IExpr _out179;
            Defs._IOwnership _out180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
            (this).GenExpr(_198_on, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out179, out _out180, out _out181);
            _204_onExpr = _out179;
            _205_onOwned = _out180;
            _206_recIdents = _out181;
            Defs._IEnvironment _207_lEnv;
            _207_lEnv = env;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _208_args;
            _208_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _209_parameters;
            _209_parameters = Dafny.Sequence<RAST._IFormal>.FromElements();
            BigInteger _hi9 = new BigInteger((_203_arguments).Count);
            for (BigInteger _210_i = BigInteger.Zero; _210_i < _hi9; _210_i++) {
              RAST._IType _211_ty;
              RAST._IType _out182;
              _out182 = (this).GenType((_203_arguments).Select(_210_i), Defs.GenTypeContext.@default());
              _211_ty = _out182;
              RAST._IType _212_bTy;
              _212_bTy = RAST.Type.create_Borrowed(_211_ty);
              Dafny.ISequence<Dafny.Rune> _213_name;
              _213_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_210_i));
              _207_lEnv = (_207_lEnv).AddAssigned(_213_name, _212_bTy);
              _209_parameters = Dafny.Sequence<RAST._IFormal>.Concat(_209_parameters, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_213_name, _212_bTy)));
              _208_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_208_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_213_name, _211_ty)));
            }
            RAST._IExpr _214_body = RAST.Expr.Default();
            if (_201_isStatic) {
              _214_body = (_204_onExpr).FSel(Defs.__default.escapeVar(_199_field));
            } else {
              _214_body = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget"));
              if (!(_200_isDatatype)) {
                _214_body = ((this).read__macro).Apply1(_214_body);
              }
              _214_body = (_214_body).Sel(Defs.__default.escapeVar(_199_field));
            }
            if (_202_isConstant) {
              _214_body = (_214_body).Apply0();
            }
            Dafny.ISequence<RAST._IExpr> _215_onExprArgs;
            _215_onExprArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi10 = new BigInteger((_208_args).Count);
            for (BigInteger _216_i = BigInteger.Zero; _216_i < _hi10; _216_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs1 = (_208_args).Select(_216_i);
              Dafny.ISequence<Dafny.Rune> _217_name = _let_tmp_rhs1.dtor__0;
              RAST._IType _218_ty = _let_tmp_rhs1.dtor__1;
              RAST._IExpr _219_rIdent;
              Defs._IOwnership _220___v104;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _221___v105;
              RAST._IExpr _out183;
              Defs._IOwnership _out184;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
              (this).GenIdent(_217_name, selfIdent, _207_lEnv, (((!(_202_isConstant)) && ((_218_ty).CanReadWithoutClone())) ? (Defs.Ownership.create_OwnershipOwned()) : (Defs.Ownership.create_OwnershipBorrowed())), out _out183, out _out184, out _out185);
              _219_rIdent = _out183;
              _220___v104 = _out184;
              _221___v105 = _out185;
              _215_onExprArgs = Dafny.Sequence<RAST._IExpr>.Concat(_215_onExprArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_219_rIdent));
            }
            _214_body = (_214_body).Apply(_215_onExprArgs);
            r = RAST.Expr.create_Lambda(_209_parameters, Std.Wrappers.Option<RAST._IType>.create_None(), _214_body);
            RAST._IExpr _out186;
            _out186 = (this).LambdaWrapRc(r);
            r = _out186;
            if (_201_isStatic) {
            } else {
              RAST._IExpr _222_target;
              if (object.Equals(_205_onOwned, Defs.Ownership.create_OwnershipOwned())) {
                _222_target = _204_onExpr;
              } else {
                _222_target = (_204_onExpr).Clone();
              }
              r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_222_target))).Then(r));
            }
            RAST._IExpr _out187;
            Defs._IOwnership _out188;
            (this).FromOwned(r, expectedOwnership, out _out187, out _out188);
            r = _out187;
            resultingOwnership = _out188;
            readIdents = _206_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Select) {
          DAST._IExpression _223_on = _source0.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _224_field = _source0.dtor_field;
          DAST._IFieldMutability _225_fieldMutability = _source0.dtor_fieldMutability;
          DAST._ISelectContext _226_selectContext = _source0.dtor_selectContext;
          DAST._IType _227_fieldType = _source0.dtor_isfieldType;
          {
            if (((_223_on).is_Companion) || ((_223_on).is_ExternCompanion)) {
              RAST._IExpr _228_onExpr;
              Defs._IOwnership _229_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _230_recIdents;
              RAST._IExpr _out189;
              Defs._IOwnership _out190;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
              (this).GenExpr(_223_on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out189, out _out190, out _out191);
              _228_onExpr = _out189;
              _229_onOwned = _out190;
              _230_recIdents = _out191;
              r = ((_228_onExpr).FSel(Defs.__default.escapeVar(_224_field))).Apply0();
              RAST._IExpr _out192;
              Defs._IOwnership _out193;
              (this).FromOwned(r, expectedOwnership, out _out192, out _out193);
              r = _out192;
              resultingOwnership = _out193;
              readIdents = _230_recIdents;
              return ;
            } else if ((_226_selectContext).is_SelectContextDatatype) {
              RAST._IExpr _231_onExpr;
              Defs._IOwnership _232_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _233_recIdents;
              RAST._IExpr _out194;
              Defs._IOwnership _out195;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out196;
              (this).GenExpr(_223_on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out194, out _out195, out _out196);
              _231_onExpr = _out194;
              _232_onOwned = _out195;
              _233_recIdents = _out196;
              r = ((_231_onExpr).Sel(Defs.__default.escapeVar(_224_field))).Apply0();
              Defs._IOwnership _234_originalMutability;
              _234_originalMutability = Defs.Ownership.create_OwnershipOwned();
              DAST._IFieldMutability _source2 = _225_fieldMutability;
              {
                if (_source2.is_ConstantField) {
                  goto after_match2;
                }
              }
              {
                if (_source2.is_InternalClassConstantFieldOrDatatypeDestructor) {
                  _234_originalMutability = Defs.Ownership.create_OwnershipBorrowed();
                  goto after_match2;
                }
              }
              {
                RAST._IExpr _out197;
                _out197 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("datatypes don't have mutable fields"), (this).InitEmptyExpr());
                r = _out197;
              }
            after_match2: ;
              RAST._IType _235_typ;
              RAST._IType _out198;
              _out198 = (this).GenType(_227_fieldType, Defs.GenTypeContext.@default());
              _235_typ = _out198;
              RAST._IExpr _out199;
              Defs._IOwnership _out200;
              (this).FromOwnership(r, _234_originalMutability, expectedOwnership, out _out199, out _out200);
              r = _out199;
              resultingOwnership = _out200;
              readIdents = _233_recIdents;
            } else if ((_226_selectContext).is_SelectContextGeneralTrait) {
              Defs._IOwnership _236_onOwned = Defs.Ownership.Default();
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _237_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              if ((_223_on).IsThisUpcast()) {
                r = RAST.__default.self;
                _237_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"));
              } else {
                RAST._IExpr _out201;
                Defs._IOwnership _out202;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out203;
                (this).GenExpr(_223_on, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out201, out _out202, out _out203);
                r = _out201;
                _236_onOwned = _out202;
                _237_recIdents = _out203;
                if (!object.Equals(r, RAST.__default.self)) {
                  r = (((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply1(r);
                }
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _237_recIdents);
              r = ((r).Sel(Defs.__default.escapeVar(_224_field))).Apply0();
              RAST._IExpr _out204;
              Defs._IOwnership _out205;
              (this).FromOwned(r, expectedOwnership, out _out204, out _out205);
              r = _out204;
              resultingOwnership = _out205;
              readIdents = _237_recIdents;
            } else {
              RAST._IExpr _238_onExpr;
              Defs._IOwnership _239_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _240_recIdents;
              RAST._IExpr _out206;
              Defs._IOwnership _out207;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out208;
              (this).GenExpr(_223_on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out206, out _out207, out _out208);
              _238_onExpr = _out206;
              _239_onOwned = _out207;
              _240_recIdents = _out208;
              r = _238_onExpr;
              if (!object.Equals(_238_onExpr, RAST.__default.self)) {
                RAST._IExpr _source3 = _238_onExpr;
                {
                  if (_source3.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op10 = _source3.dtor_op1;
                    if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying0 = _source3.dtor_underlying;
                      if (underlying0.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name0 = underlying0.dtor_name;
                        if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                          goto after_match3;
                        }
                      }
                    }
                  }
                }
                {
                }
              after_match3: ;
                if (((this).pointerType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(Defs.__default.escapeVar(_224_field));
              DAST._IFieldMutability _source4 = _225_fieldMutability;
              {
                if (_source4.is_ConstantField) {
                  r = (r).Apply0();
                  r = (r).Clone();
                  goto after_match4;
                }
              }
              {
                if (_source4.is_InternalClassConstantFieldOrDatatypeDestructor) {
                  r = (r).Clone();
                  goto after_match4;
                }
              }
              {
                r = ((this).read__mutable__field__macro).Apply1(r);
              }
            after_match4: ;
              RAST._IExpr _out209;
              Defs._IOwnership _out210;
              (this).FromOwned(r, expectedOwnership, out _out209, out _out210);
              r = _out209;
              resultingOwnership = _out210;
              readIdents = _240_recIdents;
            }
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Index) {
          DAST._IExpression _241_on = _source0.dtor_expr;
          DAST._ICollKind _242_collKind = _source0.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _243_indices = _source0.dtor_indices;
          {
            RAST._IExpr _244_onExpr;
            Defs._IOwnership _245_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _246_recIdents;
            RAST._IExpr _out211;
            Defs._IOwnership _out212;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
            (this).GenExpr(_241_on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out211, out _out212, out _out213);
            _244_onExpr = _out211;
            _245_onOwned = _out212;
            _246_recIdents = _out213;
            readIdents = _246_recIdents;
            r = _244_onExpr;
            bool _247_hadArray;
            _247_hadArray = false;
            if (object.Equals(_242_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _247_hadArray = true;
              if ((new BigInteger((_243_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi11 = new BigInteger((_243_indices).Count);
            for (BigInteger _248_i = BigInteger.Zero; _248_i < _hi11; _248_i++) {
              if (object.Equals(_242_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _249_idx;
                Defs._IOwnership _250_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _251_recIdentsIdx;
                RAST._IExpr _out214;
                Defs._IOwnership _out215;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out216;
                (this).GenExpr((_243_indices).Select(_248_i), selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out214, out _out215, out _out216);
                _249_idx = _out214;
                _250_idxOwned = _out215;
                _251_recIdentsIdx = _out216;
                _249_idx = RAST.__default.IntoUsize(_249_idx);
                r = RAST.Expr.create_SelectIndex(r, _249_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _251_recIdentsIdx);
              } else {
                RAST._IExpr _252_idx;
                Defs._IOwnership _253_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _254_recIdentsIdx;
                RAST._IExpr _out217;
                Defs._IOwnership _out218;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out219;
                (this).GenExpr((_243_indices).Select(_248_i), selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out217, out _out218, out _out219);
                _252_idx = _out217;
                _253_idxOwned = _out218;
                _254_recIdentsIdx = _out219;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_252_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _254_recIdentsIdx);
              }
            }
            if (_247_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out220;
            Defs._IOwnership _out221;
            (this).FromOwned(r, expectedOwnership, out _out220, out _out221);
            r = _out220;
            resultingOwnership = _out221;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IndexRange) {
          DAST._IExpression _255_on = _source0.dtor_expr;
          bool _256_isArray = _source0.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _257_low = _source0.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _258_high = _source0.dtor_high;
          {
            Defs._IOwnership _259_onExpectedOwnership;
            if (_256_isArray) {
              if (((this).pointerType).is_Raw) {
                _259_onExpectedOwnership = Defs.Ownership.create_OwnershipOwned();
              } else {
                _259_onExpectedOwnership = Defs.Ownership.create_OwnershipBorrowed();
              }
            } else {
              _259_onExpectedOwnership = Defs.Ownership.create_OwnershipAutoBorrowed();
            }
            RAST._IExpr _260_onExpr;
            Defs._IOwnership _261_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _262_recIdents;
            RAST._IExpr _out222;
            Defs._IOwnership _out223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
            (this).GenExpr(_255_on, selfIdent, env, _259_onExpectedOwnership, out _out222, out _out223, out _out224);
            _260_onExpr = _out222;
            _261_onOwned = _out223;
            _262_recIdents = _out224;
            readIdents = _262_recIdents;
            Dafny.ISequence<Dafny.Rune> _263_methodName;
            if ((_257_low).is_Some) {
              if ((_258_high).is_Some) {
                _263_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
              } else {
                _263_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
              }
            } else if ((_258_high).is_Some) {
              _263_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
            } else {
              _263_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
            Dafny.ISequence<RAST._IExpr> _264_arguments;
            _264_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source5 = _257_low;
            {
              if (_source5.is_Some) {
                DAST._IExpression _265_l = _source5.dtor_value;
                {
                  RAST._IExpr _266_lExpr;
                  Defs._IOwnership _267___v108;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _268_recIdentsL;
                  RAST._IExpr _out225;
                  Defs._IOwnership _out226;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
                  (this).GenExpr(_265_l, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out225, out _out226, out _out227);
                  _266_lExpr = _out225;
                  _267___v108 = _out226;
                  _268_recIdentsL = _out227;
                  _264_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_264_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_266_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _268_recIdentsL);
                }
                goto after_match5;
              }
            }
            {
            }
          after_match5: ;
            Std.Wrappers._IOption<DAST._IExpression> _source6 = _258_high;
            {
              if (_source6.is_Some) {
                DAST._IExpression _269_h = _source6.dtor_value;
                {
                  RAST._IExpr _270_hExpr;
                  Defs._IOwnership _271___v109;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _272_recIdentsH;
                  RAST._IExpr _out228;
                  Defs._IOwnership _out229;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
                  (this).GenExpr(_269_h, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out228, out _out229, out _out230);
                  _270_hExpr = _out228;
                  _271___v109 = _out229;
                  _272_recIdentsH = _out230;
                  _264_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_264_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_270_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _272_recIdentsH);
                }
                goto after_match6;
              }
            }
            {
            }
          after_match6: ;
            r = _260_onExpr;
            if (_256_isArray) {
              if (!(_263_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _263_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _263_methodName);
              }
              Dafny.ISequence<Dafny.Rune> _273_object__suffix;
              if (((this).pointerType).is_Raw) {
                _273_object__suffix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              } else {
                _273_object__suffix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_object");
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _263_methodName), _273_object__suffix))).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_260_onExpr), _264_arguments));
            } else {
              if (!(_263_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_263_methodName)).Apply(_264_arguments);
              } else {
                r = (r).Clone();
              }
            }
            RAST._IExpr _out231;
            Defs._IOwnership _out232;
            (this).FromOwned(r, expectedOwnership, out _out231, out _out232);
            r = _out231;
            resultingOwnership = _out232;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TupleSelect) {
          DAST._IExpression _274_on = _source0.dtor_expr;
          BigInteger _275_idx = _source0.dtor_index;
          DAST._IType _276_fieldType = _source0.dtor_fieldType;
          {
            RAST._IExpr _277_onExpr;
            Defs._IOwnership _278_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _279_recIdents;
            RAST._IExpr _out233;
            Defs._IOwnership _out234;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out235;
            (this).GenExpr(_274_on, selfIdent, env, Defs.Ownership.create_OwnershipAutoBorrowed(), out _out233, out _out234, out _out235);
            _277_onExpr = _out233;
            _278_onOwnership = _out234;
            _279_recIdents = _out235;
            Dafny.ISequence<Dafny.Rune> _280_selName;
            _280_selName = Std.Strings.__default.OfNat(_275_idx);
            DAST._IType _source7 = _276_fieldType;
            {
              if (_source7.is_Tuple) {
                Dafny.ISequence<DAST._IType> _281_tps = _source7.dtor_Tuple_a0;
                if (((_276_fieldType).is_Tuple) && ((new BigInteger((_281_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _280_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _280_selName);
                }
                goto after_match7;
              }
            }
            {
            }
          after_match7: ;
            r = ((_277_onExpr).Sel(_280_selName)).Clone();
            RAST._IExpr _out236;
            Defs._IOwnership _out237;
            (this).FromOwnership(r, Defs.Ownership.create_OwnershipOwned(), expectedOwnership, out _out236, out _out237);
            r = _out236;
            resultingOwnership = _out237;
            readIdents = _279_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Call) {
          DAST._IExpression _282_on = _source0.dtor_on;
          DAST._ICallName _283_name = _source0.dtor_callName;
          Dafny.ISequence<DAST._IType> _284_typeArgs = _source0.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _285_args = _source0.dtor_args;
          {
            RAST._IExpr _out238;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
            (this).GenCall(_282_on, selfIdent, _283_name, _284_typeArgs, _285_args, env, out _out238, out _out239);
            r = _out238;
            readIdents = _out239;
            RAST._IExpr _out240;
            Defs._IOwnership _out241;
            (this).FromOwned(r, expectedOwnership, out _out240, out _out241);
            r = _out240;
            resultingOwnership = _out241;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _286_paramsDafny = _source0.dtor_params;
          DAST._IType _287_retType = _source0.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _288_body = _source0.dtor_body;
          {
            Dafny.ISequence<RAST._IFormal> _289_params;
            Dafny.ISequence<RAST._IFormal> _out242;
            _out242 = (this).GenParams(_286_paramsDafny, _286_paramsDafny, true);
            _289_params = _out242;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _290_paramNames;
            _290_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _291_paramTypesMap;
            _291_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi12 = new BigInteger((_289_params).Count);
            for (BigInteger _292_i = BigInteger.Zero; _292_i < _hi12; _292_i++) {
              Dafny.ISequence<Dafny.Rune> _293_name;
              _293_name = ((_289_params).Select(_292_i)).dtor_name;
              _290_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_290_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_293_name));
              _291_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_291_paramTypesMap, _293_name, ((_289_params).Select(_292_i)).dtor_tpe);
            }
            Defs._IEnvironment _294_subEnv;
            _294_subEnv = ((env).ToOwned()).Merge(Defs.Environment.create(_290_paramNames, _291_paramTypesMap, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements()));
            RAST._IExpr _295_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _296_recIdents;
            Defs._IEnvironment _297___v111;
            RAST._IExpr _out243;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
            Defs._IEnvironment _out245;
            (this).GenStmts(_288_body, ((!object.Equals(selfIdent, Defs.SelfInfo.create_NoSelf())) ? (Defs.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (Defs.SelfInfo.create_NoSelf())), _294_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out243, out _out244, out _out245);
            _295_recursiveGen = _out243;
            _296_recIdents = _out244;
            _297___v111 = _out245;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _296_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_296_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_298_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll0 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in (_298_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _299_name = (Dafny.ISequence<Dafny.Rune>)_compr_0;
                if ((_298_paramNames).Contains(_299_name)) {
                  _coll0.Add(_299_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll0);
            }))())(_290_paramNames));
            RAST._IExpr _300_allReadCloned;
            _300_allReadCloned = (this).InitEmptyExpr();
            while (!(_296_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _301_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_296_recIdents).Elements) {
                _301_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
                if ((_296_recIdents).Contains(_301_next)) {
                  goto after__ASSIGN_SUCH_THAT_1;
                }
              }
              throw new System.Exception("assign-such-that search produced no value");
            after__ASSIGN_SUCH_THAT_1: ;
              if ((!object.Equals(selfIdent, Defs.SelfInfo.create_NoSelf())) && ((_301_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _302_selfCloned;
                Defs._IOwnership _303___v112;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _304___v113;
                RAST._IExpr _out246;
                Defs._IOwnership _out247;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out248;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, Defs.Environment.Empty(), Defs.Ownership.create_OwnershipOwned(), out _out246, out _out247, out _out248);
                _302_selfCloned = _out246;
                _303___v112 = _out247;
                _304___v113 = _out248;
                _300_allReadCloned = (_300_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_302_selfCloned)));
              } else if (!((_290_paramNames).Contains(_301_next))) {
                RAST._IExpr _305_copy;
                _305_copy = (RAST.Expr.create_Identifier(_301_next)).Clone();
                _300_allReadCloned = (_300_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _301_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_305_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_301_next));
              }
              _296_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_296_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_301_next));
            }
            RAST._IType _306_retTypeGen;
            RAST._IType _out249;
            _out249 = (this).GenType(_287_retType, Defs.GenTypeContext.@default());
            _306_retTypeGen = _out249;
            RAST._IExpr _out250;
            _out250 = (this).LambdaWrapRc(RAST.Expr.create_Lambda(_289_params, Std.Wrappers.Option<RAST._IType>.create_Some(_306_retTypeGen), RAST.Expr.create_Block(_295_recursiveGen)));
            r = _out250;
            r = RAST.Expr.create_Block((_300_allReadCloned).Then(r));
            RAST._IExpr _out251;
            Defs._IOwnership _out252;
            (this).FromOwned(r, expectedOwnership, out _out251, out _out252);
            r = _out251;
            resultingOwnership = _out252;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _307_values = _source0.dtor_values;
          DAST._IType _308_retType = _source0.dtor_retType;
          DAST._IExpression _309_expr = _source0.dtor_expr;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _310_paramNames;
            _310_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _311_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out253;
            _out253 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_312_value) => {
              return (_312_value).dtor__0;
            })), _307_values), Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_312_value) => {
              return (_312_value).dtor__0;
            })), _307_values), false);
            _311_paramFormals = _out253;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _313_paramTypes;
            _313_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _314_paramNamesSet;
            _314_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi13 = new BigInteger((_307_values).Count);
            for (BigInteger _315_i = BigInteger.Zero; _315_i < _hi13; _315_i++) {
              Dafny.ISequence<Dafny.Rune> _316_name;
              _316_name = (((_307_values).Select(_315_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _317_rName;
              _317_rName = Defs.__default.escapeVar(_316_name);
              _310_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_310_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_317_rName));
              _313_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_313_paramTypes, _317_rName, ((_311_paramFormals).Select(_315_i)).dtor_tpe);
              _314_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_314_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_317_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (this).InitEmptyExpr();
            BigInteger _hi14 = new BigInteger((_307_values).Count);
            for (BigInteger _318_i = BigInteger.Zero; _318_i < _hi14; _318_i++) {
              RAST._IType _319_typeGen;
              RAST._IType _out254;
              _out254 = (this).GenType((((_307_values).Select(_318_i)).dtor__0).dtor_typ, Defs.GenTypeContext.@default());
              _319_typeGen = _out254;
              RAST._IExpr _320_valueGen;
              Defs._IOwnership _321___v114;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _322_recIdents;
              RAST._IExpr _out255;
              Defs._IOwnership _out256;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
              (this).GenExpr(((_307_values).Select(_318_i)).dtor__1, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out255, out _out256, out _out257);
              _320_valueGen = _out255;
              _321___v114 = _out256;
              _322_recIdents = _out257;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), Defs.__default.escapeVar((((_307_values).Select(_318_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_319_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_320_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _322_recIdents);
            }
            Defs._IEnvironment _323_newEnv;
            _323_newEnv = Defs.Environment.create(_310_paramNames, _313_paramTypes, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements());
            RAST._IExpr _324_recGen;
            Defs._IOwnership _325_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _326_recIdents;
            RAST._IExpr _out258;
            Defs._IOwnership _out259;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out260;
            (this).GenExpr(_309_expr, selfIdent, _323_newEnv, expectedOwnership, out _out258, out _out259, out _out260);
            _324_recGen = _out258;
            _325_recOwned = _out259;
            _326_recIdents = _out260;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_326_recIdents, _314_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_324_recGen));
            RAST._IExpr _out261;
            Defs._IOwnership _out262;
            (this).FromOwnership(r, _325_recOwned, expectedOwnership, out _out261, out _out262);
            r = _out261;
            resultingOwnership = _out262;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _327_name = _source0.dtor_ident;
          DAST._IType _328_tpe = _source0.dtor_typ;
          DAST._IExpression _329_value = _source0.dtor_value;
          DAST._IExpression _330_iifeBody = _source0.dtor_iifeBody;
          {
            RAST._IExpr _331_valueGen;
            Defs._IOwnership _332___v115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _333_recIdents;
            RAST._IExpr _out263;
            Defs._IOwnership _out264;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
            (this).GenExpr(_329_value, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out263, out _out264, out _out265);
            _331_valueGen = _out263;
            _332___v115 = _out264;
            _333_recIdents = _out265;
            readIdents = _333_recIdents;
            RAST._IType _334_valueTypeGen;
            RAST._IType _out266;
            _out266 = (this).GenType(_328_tpe, Defs.GenTypeContext.@default());
            _334_valueTypeGen = _out266;
            Dafny.ISequence<Dafny.Rune> _335_iifeVar;
            _335_iifeVar = Defs.__default.escapeVar(_327_name);
            RAST._IExpr _336_bodyGen;
            Defs._IOwnership _337___v116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _338_bodyIdents;
            RAST._IExpr _out267;
            Defs._IOwnership _out268;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out269;
            (this).GenExpr(_330_iifeBody, selfIdent, (env).AddAssigned(_335_iifeVar, _334_valueTypeGen), Defs.Ownership.create_OwnershipOwned(), out _out267, out _out268, out _out269);
            _336_bodyGen = _out267;
            _337___v116 = _out268;
            _338_bodyIdents = _out269;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_338_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_335_iifeVar)));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _335_iifeVar, Std.Wrappers.Option<RAST._IType>.create_Some(_334_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_331_valueGen))).Then(_336_bodyGen));
            RAST._IExpr _out270;
            Defs._IOwnership _out271;
            (this).FromOwned(r, expectedOwnership, out _out270, out _out271);
            r = _out270;
            resultingOwnership = _out271;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Apply) {
          DAST._IExpression _339_func = _source0.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _340_args = _source0.dtor_args;
          {
            RAST._IExpr _341_funcExpr;
            Defs._IOwnership _342___v117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _343_recIdents;
            RAST._IExpr _out272;
            Defs._IOwnership _out273;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
            (this).GenExpr(_339_func, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out272, out _out273, out _out274);
            _341_funcExpr = _out272;
            _342___v117 = _out273;
            _343_recIdents = _out274;
            readIdents = _343_recIdents;
            Dafny.ISequence<RAST._IExpr> _344_rArgs;
            _344_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi15 = new BigInteger((_340_args).Count);
            for (BigInteger _345_i = BigInteger.Zero; _345_i < _hi15; _345_i++) {
              RAST._IExpr _346_argExpr;
              Defs._IOwnership _347_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _348_argIdents;
              RAST._IExpr _out275;
              Defs._IOwnership _out276;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
              (this).GenExpr((_340_args).Select(_345_i), selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out275, out _out276, out _out277);
              _346_argExpr = _out275;
              _347_argOwned = _out276;
              _348_argIdents = _out277;
              _344_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_344_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_346_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _348_argIdents);
            }
            r = (_341_funcExpr).Apply(_344_rArgs);
            RAST._IExpr _out278;
            Defs._IOwnership _out279;
            (this).FromOwned(r, expectedOwnership, out _out278, out _out279);
            r = _out278;
            resultingOwnership = _out279;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_TypeTest) {
          DAST._IExpression _349_on = _source0.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _350_dType = _source0.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _351_variant = _source0.dtor_variant;
          {
            RAST._IExpr _352_exprGen;
            Defs._IOwnership _353___v118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _354_recIdents;
            RAST._IExpr _out280;
            Defs._IOwnership _out281;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
            (this).GenExpr(_349_on, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out280, out _out281, out _out282);
            _352_exprGen = _out280;
            _353___v118 = _out281;
            _354_recIdents = _out282;
            RAST._IExpr _355_variantExprPath;
            RAST._IExpr _out283;
            _out283 = (this).GenPathExpr(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_350_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_351_variant)), true);
            _355_variantExprPath = _out283;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_352_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0(), RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }"), _355_variantExprPath, DAST.Format.UnaryOpFormat.create_NoFormat())));
            RAST._IExpr _out284;
            Defs._IOwnership _out285;
            (this).FromOwned(r, expectedOwnership, out _out284, out _out285);
            r = _out284;
            resultingOwnership = _out285;
            readIdents = _354_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_Is) {
          DAST._IExpression _356_expr = _source0.dtor_expr;
          DAST._IType _357_fromTyp = _source0.dtor_fromType;
          DAST._IType _358_toTyp = _source0.dtor_toType;
          {
            RAST._IType _359_fromTpe;
            RAST._IType _out286;
            _out286 = (this).GenType(_357_fromTyp, Defs.GenTypeContext.@default());
            _359_fromTpe = _out286;
            RAST._IType _360_toTpe;
            RAST._IType _out287;
            _out287 = (this).GenType(_358_toTyp, Defs.GenTypeContext.@default());
            _360_toTpe = _out287;
            if (((_359_fromTpe).IsObjectOrPointer()) && ((_360_toTpe).IsObjectOrPointer())) {
              RAST._IExpr _361_expr;
              Defs._IOwnership _362_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _363_recIdents;
              RAST._IExpr _out288;
              Defs._IOwnership _out289;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
              (this).GenExpr(_356_expr, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out288, out _out289, out _out290);
              _361_expr = _out288;
              _362_recOwned = _out289;
              _363_recIdents = _out290;
              r = (((_361_expr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_360_toTpe).ObjectOrPointerUnderlying()))).Apply0();
              RAST._IExpr _out291;
              Defs._IOwnership _out292;
              (this).FromOwnership(r, _362_recOwned, expectedOwnership, out _out291, out _out292);
              r = _out291;
              resultingOwnership = _out292;
              readIdents = _363_recIdents;
            } else {
              RAST._IExpr _364_expr;
              Defs._IOwnership _365_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _366_recIdents;
              RAST._IExpr _out293;
              Defs._IOwnership _out294;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
              (this).GenExpr(_356_expr, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out293, out _out294, out _out295);
              _364_expr = _out293;
              _365_recOwned = _out294;
              _366_recIdents = _out295;
              bool _367_isDatatype;
              _367_isDatatype = (_358_toTyp).IsDatatype();
              bool _368_isGeneralTrait;
              _368_isGeneralTrait = (!(_367_isDatatype)) && ((_358_toTyp).IsGeneralTrait());
              if ((_367_isDatatype) || (_368_isGeneralTrait)) {
                bool _369_isDowncast;
                _369_isDowncast = (_358_toTyp).Extends(_357_fromTyp);
                if (_369_isDowncast) {
                  DAST._IType _370_underlyingType;
                  if (_367_isDatatype) {
                    _370_underlyingType = (_358_toTyp).GetDatatypeType();
                  } else {
                    _370_underlyingType = (_358_toTyp).GetGeneralTraitType();
                  }
                  RAST._IType _371_toTpeRaw;
                  RAST._IType _out296;
                  _out296 = (this).GenType(_370_underlyingType, Defs.GenTypeContext.@default());
                  _371_toTpeRaw = _out296;
                  Std.Wrappers._IOption<RAST._IExpr> _372_toTpeRawDowncastOpt;
                  _372_toTpeRawDowncastOpt = (_371_toTpeRaw).ToDowncastExpr();
                  if ((_372_toTpeRawDowncastOpt).is_Some) {
                    _364_expr = (this).FromGeneralBorrowToSelfBorrow(_364_expr, Defs.Ownership.create_OwnershipBorrowed(), env);
                    if (_367_isDatatype) {
                      _364_expr = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AnyRef"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_any_ref"))).Apply1(_364_expr);
                    }
                    r = (((_372_toTpeRawDowncastOpt).dtor_value).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_is"))).Apply1(_364_expr);
                    _365_recOwned = Defs.Ownership.create_OwnershipOwned();
                  } else {
                    RAST._IExpr _out297;
                    _out297 = (this).Error(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not convert "), (_371_toTpeRaw)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to a Downcast trait")), (this).InitEmptyExpr());
                    r = _out297;
                  }
                } else {
                  RAST._IExpr _out298;
                  _out298 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Needs support for upcasting general traits"), (this).InitEmptyExpr());
                  r = _out298;
                }
              } else {
                RAST._IExpr _out299;
                _out299 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object, Ptr, General trait or Datatype"), (this).InitEmptyExpr());
                r = _out299;
              }
              RAST._IExpr _out300;
              Defs._IOwnership _out301;
              (this).FromOwnership(r, _365_recOwned, expectedOwnership, out _out300, out _out301);
              r = _out300;
              resultingOwnership = _out301;
              readIdents = _366_recIdents;
            }
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_BoolBoundedPool) {
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out302;
            Defs._IOwnership _out303;
            (this).FromOwned(r, expectedOwnership, out _out302, out _out303);
            r = _out302;
            resultingOwnership = _out303;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBoundedPool) {
          DAST._IExpression _373_of = _source0.dtor_of;
          {
            RAST._IExpr _374_exprGen;
            Defs._IOwnership _375___v119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _376_recIdents;
            RAST._IExpr _out304;
            Defs._IOwnership _out305;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
            (this).GenExpr(_373_of, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out304, out _out305, out _out306);
            _374_exprGen = _out304;
            _375___v119 = _out305;
            _376_recIdents = _out306;
            r = ((_374_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0();
            RAST._IExpr _out307;
            Defs._IOwnership _out308;
            (this).FromOwned(r, expectedOwnership, out _out307, out _out308);
            r = _out307;
            resultingOwnership = _out308;
            readIdents = _376_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SeqBoundedPool) {
          DAST._IExpression _377_of = _source0.dtor_of;
          bool _378_includeDuplicates = _source0.dtor_includeDuplicates;
          {
            RAST._IExpr _379_exprGen;
            Defs._IOwnership _380___v120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _381_recIdents;
            RAST._IExpr _out309;
            Defs._IOwnership _out310;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
            (this).GenExpr(_377_of, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out309, out _out310, out _out311);
            _379_exprGen = _out309;
            _380___v120 = _out310;
            _381_recIdents = _out311;
            r = ((_379_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0();
            if (!(_378_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out312;
            Defs._IOwnership _out313;
            (this).FromOwned(r, expectedOwnership, out _out312, out _out313);
            r = _out312;
            resultingOwnership = _out313;
            readIdents = _381_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MultisetBoundedPool) {
          DAST._IExpression _382_of = _source0.dtor_of;
          bool _383_includeDuplicates = _source0.dtor_includeDuplicates;
          {
            RAST._IExpr _384_exprGen;
            Defs._IOwnership _385___v121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _386_recIdents;
            RAST._IExpr _out314;
            Defs._IOwnership _out315;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
            (this).GenExpr(_382_of, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out314, out _out315, out _out316);
            _384_exprGen = _out314;
            _385___v121 = _out315;
            _386_recIdents = _out316;
            r = ((_384_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0();
            if (!(_383_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out317;
            Defs._IOwnership _out318;
            (this).FromOwned(r, expectedOwnership, out _out317, out _out318);
            r = _out317;
            resultingOwnership = _out318;
            readIdents = _386_recIdents;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBoundedPool) {
          DAST._IExpression _387_of = _source0.dtor_of;
          {
            RAST._IExpr _388_exprGen;
            Defs._IOwnership _389___v122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _390_recIdents;
            RAST._IExpr _out319;
            Defs._IOwnership _out320;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out321;
            (this).GenExpr(_387_of, selfIdent, env, Defs.Ownership.create_OwnershipBorrowed(), out _out319, out _out320, out _out321);
            _388_exprGen = _out319;
            _389___v122 = _out320;
            _390_recIdents = _out321;
            r = ((((_388_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0();
            readIdents = _390_recIdents;
            RAST._IExpr _out322;
            Defs._IOwnership _out323;
            (this).FromOwned(r, expectedOwnership, out _out322, out _out323);
            r = _out322;
            resultingOwnership = _out323;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_ExactBoundedPool) {
          DAST._IExpression _391_of = _source0.dtor_of;
          {
            RAST._IExpr _392_exprGen;
            Defs._IOwnership _393___v123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _394_recIdents;
            RAST._IExpr _out324;
            Defs._IOwnership _out325;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
            (this).GenExpr(_391_of, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
            _392_exprGen = _out324;
            _393___v123 = _out325;
            _394_recIdents = _out326;
            r = ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("once"))).Apply1(_392_exprGen);
            readIdents = _394_recIdents;
            RAST._IExpr _out327;
            Defs._IOwnership _out328;
            (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
            r = _out327;
            resultingOwnership = _out328;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_IntRange) {
          DAST._IType _395_typ = _source0.dtor_elemType;
          DAST._IExpression _396_lo = _source0.dtor_lo;
          DAST._IExpression _397_hi = _source0.dtor_hi;
          bool _398_up = _source0.dtor_up;
          {
            RAST._IExpr _399_lo;
            Defs._IOwnership _400___v124;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _401_recIdentsLo;
            RAST._IExpr _out329;
            Defs._IOwnership _out330;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
            (this).GenExpr(_396_lo, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
            _399_lo = _out329;
            _400___v124 = _out330;
            _401_recIdentsLo = _out331;
            RAST._IExpr _402_hi;
            Defs._IOwnership _403___v125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _404_recIdentsHi;
            RAST._IExpr _out332;
            Defs._IOwnership _out333;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
            (this).GenExpr(_397_hi, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out332, out _out333, out _out334);
            _402_hi = _out332;
            _403___v125 = _out333;
            _404_recIdentsHi = _out334;
            if (_398_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_399_lo, _402_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_402_hi, _399_lo));
            }
            if (!((_395_typ).is_Primitive)) {
              RAST._IType _405_tpe;
              RAST._IType _out335;
              _out335 = (this).GenType(_395_typ, Defs.GenTypeContext.@default());
              _405_tpe = _out335;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map"))).Apply1((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_405_tpe))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into")));
            }
            RAST._IExpr _out336;
            Defs._IOwnership _out337;
            (this).FromOwned(r, expectedOwnership, out _out336, out _out337);
            r = _out336;
            resultingOwnership = _out337;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_401_recIdentsLo, _404_recIdentsHi);
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_UnboundedIntRange) {
          DAST._IExpression _406_start = _source0.dtor_start;
          bool _407_up = _source0.dtor_up;
          {
            RAST._IExpr _408_start;
            Defs._IOwnership _409___v126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _410_recIdentStart;
            RAST._IExpr _out338;
            Defs._IOwnership _out339;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out340;
            (this).GenExpr(_406_start, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out338, out _out339, out _out340);
            _408_start = _out338;
            _409___v126 = _out339;
            _410_recIdentStart = _out340;
            if (_407_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_408_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_408_start);
            }
            RAST._IExpr _out341;
            Defs._IOwnership _out342;
            (this).FromOwned(r, expectedOwnership, out _out341, out _out342);
            r = _out341;
            resultingOwnership = _out342;
            readIdents = _410_recIdentStart;
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_MapBuilder) {
          DAST._IType _411_keyType = _source0.dtor_keyType;
          DAST._IType _412_valueType = _source0.dtor_valueType;
          {
            RAST._IType _413_kType;
            RAST._IType _out343;
            _out343 = (this).GenType(_411_keyType, Defs.GenTypeContext.@default());
            _413_kType = _out343;
            RAST._IType _414_vType;
            RAST._IType _out344;
            _out344 = (this).GenType(_412_valueType, Defs.GenTypeContext.@default());
            _414_vType = _out344;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_413_kType, _414_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply0();
            RAST._IExpr _out345;
            Defs._IOwnership _out346;
            (this).FromOwned(r, expectedOwnership, out _out345, out _out346);
            r = _out345;
            resultingOwnership = _out346;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_SetBuilder) {
          DAST._IType _415_elemType = _source0.dtor_elemType;
          {
            RAST._IType _416_eType;
            RAST._IType _out347;
            _out347 = (this).GenType(_415_elemType, Defs.GenTypeContext.@default());
            _416_eType = _out347;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_416_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply0();
            RAST._IExpr _out348;
            Defs._IOwnership _out349;
            (this).FromOwned(r, expectedOwnership, out _out348, out _out349);
            r = _out348;
            resultingOwnership = _out349;
            return ;
          }
          goto after_match0;
        }
      }
      {
        DAST._IType _417_elemType = _source0.dtor_elemType;
        DAST._IExpression _418_collection = _source0.dtor_collection;
        bool _419_is__forall = _source0.dtor_is__forall;
        DAST._IExpression _420_lambda = _source0.dtor_lambda;
        {
          RAST._IType _421_tpe;
          RAST._IType _out350;
          _out350 = (this).GenType(_417_elemType, Defs.GenTypeContext.@default());
          _421_tpe = _out350;
          RAST._IExpr _422_collectionGen;
          Defs._IOwnership _423___v127;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _424_recIdents;
          RAST._IExpr _out351;
          Defs._IOwnership _out352;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out353;
          (this).GenExpr(_418_collection, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out351, out _out352, out _out353);
          _422_collectionGen = _out351;
          _423___v127 = _out352;
          _424_recIdents = _out353;
          Dafny.ISequence<DAST._IAttribute> _425_extraAttributes;
          _425_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((((_418_collection).is_IntRange) || ((_418_collection).is_UnboundedIntRange)) || ((_418_collection).is_SeqBoundedPool)) || ((_418_collection).is_ExactBoundedPool)) || ((_418_collection).is_MultisetBoundedPool)) {
            _425_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(Defs.__default.AttributeOwned);
          }
          if ((_420_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _426_formals;
            _426_formals = (_420_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _427_newFormals;
            _427_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi16 = new BigInteger((_426_formals).Count);
            for (BigInteger _428_i = BigInteger.Zero; _428_i < _hi16; _428_i++) {
              var _pat_let_tv0 = _425_extraAttributes;
              var _pat_let_tv1 = _426_formals;
              _427_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_427_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_426_formals).Select(_428_i), _pat_let75_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let75_0, _429_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv0, ((_pat_let_tv1).Select(_428_i)).dtor_attributes), _pat_let76_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let76_0, _430_dt__update_hattributes_h0 => DAST.Formal.create((_429_dt__update__tmp_h0).dtor_name, (_429_dt__update__tmp_h0).dtor_typ, _430_dt__update_hattributes_h0)))))));
            }
            DAST._IExpression _431_newLambda;
            DAST._IExpression _432_dt__update__tmp_h1 = _420_lambda;
            Dafny.ISequence<DAST._IFormal> _433_dt__update_hparams_h0 = _427_newFormals;
            _431_newLambda = DAST.Expression.create_Lambda(_433_dt__update_hparams_h0, (_432_dt__update__tmp_h1).dtor_retType, (_432_dt__update__tmp_h1).dtor_body);
            RAST._IExpr _434_lambdaGen;
            Defs._IOwnership _435___v128;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _436_recLambdaIdents;
            RAST._IExpr _out354;
            Defs._IOwnership _out355;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out356;
            (this).GenExpr(_431_newLambda, selfIdent, env, Defs.Ownership.create_OwnershipOwned(), out _out354, out _out355, out _out356);
            _434_lambdaGen = _out354;
            _435___v128 = _out355;
            _436_recLambdaIdents = _out356;
            Dafny.ISequence<Dafny.Rune> _437_fn;
            if (_419_is__forall) {
              _437_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all");
            } else {
              _437_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any");
            }
            r = ((_422_collectionGen).Sel(_437_fn)).Apply1(((_434_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0());
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_424_recIdents, _436_recLambdaIdents);
          } else {
            RAST._IExpr _out357;
            _out357 = (this).Error(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"), (this).InitEmptyExpr());
            r = _out357;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out358;
          Defs._IOwnership _out359;
          (this).FromOwned(r, expectedOwnership, out _out358, out _out359);
          r = _out358;
          resultingOwnership = _out359;
        }
      }
    after_match0: ;
    }
    public RAST._IExpr InitEmptyExpr() {
      return RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    }
    public RAST._IExpr Error(Dafny.ISequence<Dafny.Rune> message, RAST._IExpr defaultExpr)
    {
      RAST._IExpr r = RAST.Expr.Default();
      if ((this.error).is_None) {
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(message);
      }
      r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*"), message), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*/")), defaultExpr, DAST.Format.UnaryOpFormat.create_NoFormat());
      return r;
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![cfg_attr(any(), rustfmt::skip)]\n"));
      Dafny.ISequence<RAST._IModDecl> _0_externUseDecls;
      _0_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi0 = new BigInteger((externalFiles).Count);
      for (BigInteger _1_i = BigInteger.Zero; _1_i < _hi0; _1_i++) {
        Dafny.ISequence<Dafny.Rune> _2_externalFile;
        _2_externalFile = (externalFiles).Select(_1_i);
        Dafny.ISequence<Dafny.Rune> _3_externalMod;
        _3_externalMod = _2_externalFile;
        if (((new BigInteger((_2_externalFile).Count)) > (new BigInteger(3))) && (((_2_externalFile).Drop((new BigInteger((_2_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _3_externalMod = (_2_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        if (((this).rootType).is_RootCrate) {
          RAST._IMod _4_externMod;
          _4_externMod = RAST.Mod.create_ExternMod(_3_externalMod);
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_4_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        _0_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_0_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_3_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_0_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Flattens all imported externs so that they can be accessed from this module"), Dafny.Sequence<RAST._IAttribute>.FromElements(), Defs.__default.DAFNY__EXTERN__MODULE, _0_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _5_allModules;
      _5_allModules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi1 = new BigInteger((p).Count);
      for (BigInteger _6_i = BigInteger.Zero; _6_i < _hi1; _6_i++) {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _7_m;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out0;
        _out0 = (this).GenModule((p).Select(_6_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _7_m = _out0;
        _5_allModules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(_5_allModules, _7_m);
      }
      BigInteger _hi2 = new BigInteger(((_5_allModules).dtor_keys).Count);
      for (BigInteger _8_i = BigInteger.Zero; _8_i < _hi2; _8_i++) {
        if (!((_5_allModules).dtor_values).Contains(((_5_allModules).dtor_keys).Select(_8_i))) {
          goto continue_0;
        }
        RAST._IMod _9_m;
        _9_m = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_5_allModules).dtor_values,((_5_allModules).dtor_keys).Select(_8_i))).ToRust();
        BigInteger _hi3 = new BigInteger((this.optimizations).Count);
        for (BigInteger _10_j = BigInteger.Zero; _10_j < _hi3; _10_j++) {
          _9_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_10_j))(_9_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_9_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public Dafny.ISequence<Dafny.Rune> EmitCallToMain(DAST._IExpression companion, Dafny.ISequence<Dafny.Rune> mainMethodName, bool hasArgs)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {");
      if (hasArgs) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"
  let args: Vec<String> = ::std::env::args().collect();
  let dafny_args =
    ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(
    &args, |s| 
  ::dafny_runtime::dafny_runtime_conversions::")), (this).conversions), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@"::string_to_dafny_string(s));
  "));
      }
      RAST._IExpr _0_call;
      Defs._IOwnership _1___v129;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2___v130;
      RAST._IExpr _out0;
      Defs._IOwnership _out1;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out2;
      (this).GenExpr(companion, Defs.SelfInfo.create_NoSelf(), Defs.Environment.Empty(), Defs.Ownership.create_OwnershipOwned(), out _out0, out _out1, out _out2);
      _0_call = _out0;
      _1___v129 = _out1;
      _2___v130 = _out2;
      _0_call = (_0_call).FSel(mainMethodName);
      if (hasArgs) {
        _0_call = (_0_call).Apply1(RAST.__default.Borrow(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_args"))));
      } else {
        _0_call = (_0_call).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_0_call)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}"));
      return s;
    }
    public Defs._IRootType _rootType {get; set;}
    public Defs._IRootType rootType { get {
      return this._rootType;
    } }
    public RAST._IPath thisFile { get {
      if (((this).rootType).is_RootCrate) {
        return RAST.__default.crate;
      } else {
        return (RAST.__default.crate).MSel(((this).rootType).dtor_moduleName);
      }
    } }
    public Defs._ICharType _charType {get; set;}
    public Defs._ICharType charType { get {
      return this._charType;
    } }
    public Dafny.ISequence<Dafny.Rune> DafnyChar { get {
      if (((this).charType).is_UTF32) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyChar");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyCharUTF16");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> conversions { get {
      if (((this).charType).is_UTF32) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unicode_chars_true");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unicode_chars_false");
      }
    } }
    public RAST._IType DafnyCharUnderlying { get {
      if (((this).charType).is_UTF32) {
        return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"));
      } else {
        return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"));
      }
    } }
    public Dafny.ISequence<Dafny.Rune> string__of { get {
      if (((this).charType).is_UTF32) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_of");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_utf16_of");
      }
    } }
    public Defs._IPointerType _pointerType {get; set;}
    public Defs._IPointerType pointerType { get {
      return this._pointerType;
    } }
    public Dafny.ISequence<Dafny.Rune> allocate { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("allocate");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("allocate_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> allocate__fn { get {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), (this).allocate);
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__uninit__macro { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit_object!");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__mut__uninit__macro { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_mut_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_mut_uninit_object!");
      }
    } }
    public RAST._IExpr thisInConstructor { get {
      if (((this).pointerType).is_Raw) {
        return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
      } else {
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))).Clone();
      }
    } }
    public Dafny.ISequence<Dafny.Rune> array__construct { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct_object");
      }
    } }
    public RAST._IExpr modify__macro { get {
      return ((RAST.__default.dafny__runtime).MSel(((((this).pointerType).is_Raw) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("md!"))))).AsExpr();
    } }
    public RAST._IExpr read__macro { get {
      return ((RAST.__default.dafny__runtime).MSel(((((this).pointerType).is_Raw) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rd!"))))).AsExpr();
    } }
    public Dafny.ISequence<Dafny.Rune> placebos__usize { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("placebos_usize");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("placebos_usize_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__if__uninit__macro { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit_object!");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__mut__if__uninit__macro { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_mut_if_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_mut_if_uninit_object!");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> Upcast { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Upcast");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> UpcastFnMacro { get {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).Upcast, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Fn!"));
    } }
    public Dafny.ISequence<Dafny.Rune> upcast { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> downcast { get {
      if (((this).pointerType).is_Raw) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cast!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cast_object!");
      }
    } }
    public Defs._ISyncType _syncType {get; set;}
    public Defs._ISyncType syncType { get {
      return this._syncType;
    } }
    public RAST._IPath rcPath { get {
      if (((this).syncType).is_NoSync) {
        return RAST.__default.RcPath;
      } else {
        return RAST.__default.ArcPath;
      }
    } }
    public RAST._IType rcType { get {
      return ((this).rcPath).AsType();
    } }
    public RAST._IExpr rcExpr { get {
      return ((this).rcPath).AsExpr();
    } }
    public Func<RAST._IType, RAST._IType> rc { get {
      return ((System.Func<RAST._IType, RAST._IType>)((_0_underlying) => {
        return ((this).rcType).Apply(Dafny.Sequence<RAST._IType>.FromElements(_0_underlying));
      }));
    } }
    public Func<RAST._IExpr, RAST._IExpr> rcNew { get {
      return ((System.Func<RAST._IExpr, RAST._IExpr>)((_0_underlying) => {
        return (((this).rcExpr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_0_underlying));
      }));
    } }
    public RAST._IType SyncSendType { get {
      return RAST.Type.create_IntersectionType(RAST.__default.SyncType, RAST.__default.SendType);
    } }
    public RAST._IType AnyTrait { get {
      if (((this).syncType).is_NoSync) {
        return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))).AsType();
      } else {
        return RAST.Type.create_IntersectionType(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))).AsType(), (this).SyncSendType);
      }
    } }
    public RAST._IExpr _rcDatatypeThis {get; set;}
    public RAST._IExpr rcDatatypeThis { get {
      return this._rcDatatypeThis;
    } }
    public RAST._IExpr _borrowedRcDatatypeThis {get; set;}
    public RAST._IExpr borrowedRcDatatypeThis { get {
      return this._borrowedRcDatatypeThis;
    } }
    public RAST._IExpr read__mutable__field__macro { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read_field!"))).AsExpr();
    } }
    public RAST._IExpr modify__mutable__field__macro { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify_field!"))).AsExpr();
    } }
    public RAST._IType DynAny { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DynAny"))).AsType();
    } }
  }
} // end of namespace DCOMP