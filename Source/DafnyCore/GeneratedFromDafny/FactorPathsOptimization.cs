// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace FactorPathsOptimization {

  public partial class __default {
    public static Func<RAST._IMod, RAST._IMod> apply(RAST._IPath thisFile) {
      return Dafny.Helpers.Id<Func<RAST._IPath, Func<RAST._IMod, RAST._IMod>>>((_0_thisFile) => ((System.Func<RAST._IMod, RAST._IMod>)((_1_mod) => {
        return FactorPathsOptimization.__default.applyPrefix(_1_mod, (_0_thisFile).MSel((_1_mod).dtor_name));
      })))(thisFile);
    }
    public static RAST._IMod applyPrefix(RAST._IMod mod, RAST._IPath SelfPath)
    {
      if ((mod).is_ExternMod) {
        return mod;
      } else {
        FactorPathsOptimization._IMapping _0_initialMapping = FactorPathsOptimization.Mapping.create(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.FromElements(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        FactorPathsOptimization._IMapping _1_mappings = (mod).Fold<FactorPathsOptimization._IMapping>(_0_initialMapping, Dafny.Helpers.Id<Func<RAST._IPath, Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>>>((_2_SelfPath) => ((System.Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>)((_3_current, _4_modDecl) => {
          return FactorPathsOptimization.__default.GatherModMapping(_2_SelfPath, _4_modDecl, _3_current);
        })))(SelfPath));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> _5_pathsToRemove = (_1_mappings).ToFinalReplacement();
        Dafny.ISequence<RAST._IModDecl> _6_imports = (_1_mappings).ToUseStatements(_5_pathsToRemove, SelfPath);
        Dafny.ISequence<RAST._IModDecl> _7_rewrittenDeclarations = (mod).Fold<Dafny.ISequence<RAST._IModDecl>>(Dafny.Sequence<RAST._IModDecl>.FromElements(), Dafny.Helpers.Id<Func<RAST._IPath, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IMod, Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>>>((_8_SelfPath, _9_pathsToRemove, _10_mod) => ((System.Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>)((_11_current, _12_modDecl) => {
          return Dafny.Sequence<RAST._IModDecl>.Concat(_11_current, Dafny.Sequence<RAST._IModDecl>.FromElements(FactorPathsOptimization.__default.ReplaceModDecl(_12_modDecl, _8_SelfPath, _9_pathsToRemove)));
        })))(SelfPath, _5_pathsToRemove, mod));
        RAST._IMod _13_dt__update__tmp_h0 = mod;
        Dafny.ISequence<RAST._IModDecl> _14_dt__update_hbody_h0 = Dafny.Sequence<RAST._IModDecl>.Concat(_6_imports, _7_rewrittenDeclarations);
        return RAST.Mod.create_Mod((_13_dt__update__tmp_h0).dtor_name, _14_dt__update_hbody_h0);
      }
    }
    public static __T UniqueElementOf<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_9 =>  {
        __T _0_e = default(__T);
        foreach (__T _assign_such_that_0 in (s).Elements) {
          _0_e = (__T)_assign_such_that_0;
          if ((s).Contains(_0_e)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value");
      after__ASSIGN_SUCH_THAT_0: ;
        return _0_e;
      }
      );
    }
    public static FactorPathsOptimization._IMapping GatherTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, FactorPathsOptimization._IMapping current)
    {
      return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._ITypeParamDecl>(((System.Func<FactorPathsOptimization._IMapping, RAST._ITypeParamDecl, FactorPathsOptimization._IMapping>)((_0_current, _1_t) => {
        return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._IType>(((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_2_current, _3_t) => {
          return FactorPathsOptimization.__default.GatherTypeMapping(_3_t, _2_current);
        })), _0_current, (_1_t).dtor_constraints);
      })), current, typeParams);
    }
    public static FactorPathsOptimization._IMapping GatherFields(RAST._IFields fields, FactorPathsOptimization._IMapping current)
    {
      RAST._IFields _source0 = fields;
      {
        if (_source0.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _0_sFields = _source0.dtor_fields;
          return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._IField>(((System.Func<FactorPathsOptimization._IMapping, RAST._IField, FactorPathsOptimization._IMapping>)((_1_current, _2_f) => {
            return FactorPathsOptimization.__default.GatherTypeMapping(((_2_f).dtor_formal).dtor_tpe, _1_current);
          })), current, _0_sFields);
        }
      }
      {
        Dafny.ISequence<RAST._INamelessField> _3_sFields = _source0.dtor_types;
        return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._INamelessField>(((System.Func<FactorPathsOptimization._IMapping, RAST._INamelessField, FactorPathsOptimization._IMapping>)((_4_current, _5_f) => {
          return FactorPathsOptimization.__default.GatherTypeMapping((_5_f).dtor_tpe, _4_current);
        })), current, _3_sFields);
      }
    }
    public static FactorPathsOptimization._IMapping GatherModMapping(RAST._IPath prefix, RAST._IModDecl modDecl, FactorPathsOptimization._IMapping current)
    {
      RAST._IModDecl _source0 = modDecl;
      {
        if (_source0.is_ModDecl) {
          RAST._IMod _0_mod = _source0.dtor_mod;
          return (current).Add((_0_mod).dtor_name, prefix);
        }
      }
      {
        if (_source0.is_StructDecl) {
          RAST._IStruct _1_struct = _source0.dtor_struct;
          return FactorPathsOptimization.__default.GatherStructMapping(_1_struct, (current).Add((_1_struct).dtor_name, prefix));
        }
      }
      {
        if (_source0.is_TypeDecl) {
          RAST._ITypeSynonym _2_tpe = _source0.dtor_tpe;
          return (current).Add((_2_tpe).dtor_name, prefix);
        }
      }
      {
        if (_source0.is_ConstDecl) {
          RAST._IConstant _3_c = _source0.dtor_c;
          return (current).Add((_3_c).dtor_name, prefix);
        }
      }
      {
        if (_source0.is_EnumDecl) {
          RAST._IEnum _4_enum = _source0.dtor_enum;
          return (current).Add((_4_enum).dtor_name, prefix);
        }
      }
      {
        if (_source0.is_ImplDecl) {
          RAST._IImpl _5_impl = _source0.dtor_impl;
          return FactorPathsOptimization.__default.GatherImplMapping(_5_impl, current);
        }
      }
      {
        if (_source0.is_TraitDecl) {
          RAST._ITrait _6_tr = _source0.dtor_tr;
          return current;
        }
      }
      {
        if (_source0.is_TopFnDecl) {
          RAST._ITopFnDecl _7_fn = _source0.dtor_fn;
          return (current).Add(((_7_fn).dtor_fn).dtor_name, prefix);
        }
      }
      {
        RAST._IUse _8_use = _source0.dtor_use;
        return current;
      }
    }
    public static FactorPathsOptimization._IMapping GatherStructMapping(RAST._IStruct @struct, FactorPathsOptimization._IMapping current)
    {
      return FactorPathsOptimization.__default.GatherTypeParams((@struct).dtor_typeParams, current);
    }
    public static FactorPathsOptimization._IMapping GatherTypeMapping(RAST._IType tpe, FactorPathsOptimization._IMapping current)
    {
      return (tpe).Fold<FactorPathsOptimization._IMapping>(current, ((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_0_current, _1_t) => {
        return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
          RAST._IType _source0 = _1_t;
          {
            if (_source0.is_TypeFromPath) {
              RAST._IPath path0 = _source0.dtor_path;
              if (path0.is_PMemberSelect) {
                RAST._IPath _2_base = path0.dtor_base;
                Dafny.ISequence<Dafny.Rune> _3_name = path0.dtor_name;
                return (_0_current).Add(_3_name, _2_base);
              }
            }
          }
          {
            return _0_current;
          }
        }))();
      })));
    }
    public static FactorPathsOptimization._IMapping GatherImplMapping(RAST._IImpl impl, FactorPathsOptimization._IMapping current)
    {
      RAST._IImpl _source0 = impl;
      {
        if (_source0.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _0_typeParams = _source0.dtor_typeParams;
          RAST._IType _1_tpe = _source0.dtor_tpe;
          RAST._IType _2_forType = _source0.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _3_where = _source0.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _4_body = _source0.dtor_body;
          FactorPathsOptimization._IMapping _5_current = FactorPathsOptimization.__default.GatherTypeParams(_0_typeParams, current);
          FactorPathsOptimization._IMapping _6_current = FactorPathsOptimization.__default.GatherTypeMapping(_1_tpe, _5_current);
          return FactorPathsOptimization.__default.GatherTypeMapping(_2_forType, _6_current);
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _7_typeParams = _source0.dtor_typeParams;
        RAST._IType _8_tpe = _source0.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _9_where = _source0.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _10_body = _source0.dtor_body;
        return FactorPathsOptimization.__default.GatherTypeMapping(_8_tpe, current);
      }
    }
    public static RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, RAST._IPath SelfPath, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IModDecl _source0 = modDecl;
      {
        if (_source0.is_ModDecl) {
          RAST._IMod _0_mod = _source0.dtor_mod;
          return RAST.ModDecl.create_ModDecl(FactorPathsOptimization.__default.applyPrefix(_0_mod, (SelfPath).MSel((_0_mod).dtor_name)));
        }
      }
      {
        if (_source0.is_StructDecl) {
          RAST._IStruct _1_struct = _source0.dtor_struct;
          return RAST.ModDecl.create_StructDecl(FactorPathsOptimization.__default.ReplaceStruct(_1_struct, replacement));
        }
      }
      {
        if (_source0.is_TypeDecl) {
          RAST._ITypeSynonym _2_tpe = _source0.dtor_tpe;
          return modDecl;
        }
      }
      {
        if (_source0.is_ConstDecl) {
          RAST._IConstant _3_c = _source0.dtor_c;
          return modDecl;
        }
      }
      {
        if (_source0.is_EnumDecl) {
          RAST._IEnum _4_enum = _source0.dtor_enum;
          return modDecl;
        }
      }
      {
        if (_source0.is_ImplDecl) {
          RAST._IImpl _5_impl = _source0.dtor_impl;
          return RAST.ModDecl.create_ImplDecl(FactorPathsOptimization.__default.ReplaceImplDecl(_5_impl, replacement));
        }
      }
      {
        if (_source0.is_TraitDecl) {
          RAST._ITrait _6_tr = _source0.dtor_tr;
          return modDecl;
        }
      }
      {
        if (_source0.is_TopFnDecl) {
          RAST._ITopFnDecl _7_fn = _source0.dtor_fn;
          return modDecl;
        }
      }
      {
        RAST._IUse _8_use = _source0.dtor_use;
        return modDecl;
      }
    }
    public static RAST._IType ReplaceType(RAST._IType t, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IType _source0 = t;
      {
        if (_source0.is_TypeFromPath) {
          RAST._IPath path0 = _source0.dtor_path;
          if (path0.is_PMemberSelect) {
            RAST._IPath _0_base = path0.dtor_base;
            Dafny.ISequence<Dafny.Rune> _1_id = path0.dtor_name;
            if (((replacement).Contains(_1_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(replacement,_1_id), _0_base))) {
              return RAST.Type.create_TSynonym(RAST.Type.create_TIdentifier(_1_id), t);
            } else {
              return t;
            }
          }
        }
      }
      {
        return t;
      }
    }
    public static Dafny.ISequence<RAST._ITypeParamDecl> ReplaceTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      return Std.Collections.Seq.__default.Map<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>>>((_0_replacement) => ((System.Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>)((_1_t) => {
        return Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1_t, _pat_let10_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let10_0, _2_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_3_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_4_constraint) => {
          return FactorPathsOptimization.__default.ReplaceType(_4_constraint, _3_replacement);
        })))(_0_replacement), (_1_t).dtor_constraints), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let11_0, _5_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_2_dt__update__tmp_h0).dtor_name, _5_dt__update_hconstraints_h0)))));
      })))(replacement), typeParams);
    }
    public static RAST._IImpl ReplaceImplDecl(RAST._IImpl impl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IImpl _source0 = impl;
      {
        if (_source0.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _0_typeParams = _source0.dtor_typeParams;
          RAST._IType _1_tpe = _source0.dtor_tpe;
          RAST._IType _2_forType = _source0.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _3_where = _source0.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _4_body = _source0.dtor_body;
          return RAST.Impl.create_ImplFor(FactorPathsOptimization.__default.ReplaceTypeParams(_0_typeParams, replacement), (_1_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), (_2_forType).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), _3_where, _4_body);
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _5_typeParams = _source0.dtor_typeParams;
        RAST._IType _6_tpe = _source0.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _7_where = _source0.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _8_body = _source0.dtor_body;
        return RAST.Impl.create_Impl(FactorPathsOptimization.__default.ReplaceTypeParams(_5_typeParams, replacement), (_6_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), _7_where, _8_body);
      }
    }
    public static RAST._IStruct ReplaceStruct(RAST._IStruct @struct, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IStruct _source0 = @struct;
      {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_attributes = _source0.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _1_name = _source0.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _2_typeParams = _source0.dtor_typeParams;
        RAST._IFields _3_fields = _source0.dtor_fields;
        return RAST.Struct.create(_0_attributes, _1_name, FactorPathsOptimization.__default.ReplaceTypeParams(_2_typeParams, replacement), FactorPathsOptimization.__default.ReplaceFields(_3_fields, replacement));
      }
    }
    public static RAST._IFields ReplaceFields(RAST._IFields fields, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IFields _source0 = fields;
      {
        if (_source0.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _0_sFields = _source0.dtor_fields;
          return RAST.Fields.create_NamedFields(Std.Collections.Seq.__default.Map<RAST._IField, RAST._IField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IField, RAST._IField>>>((_1_replacement) => ((System.Func<RAST._IField, RAST._IField>)((_2_f) => {
  return Dafny.Helpers.Let<RAST._IField, RAST._IField>(_2_f, _pat_let12_0 => Dafny.Helpers.Let<RAST._IField, RAST._IField>(_pat_let12_0, _3_dt__update__tmp_h0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>((_2_f).dtor_formal, _pat_let14_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>(_pat_let14_0, _4_dt__update__tmp_h1 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(FactorPathsOptimization.__default.ReplaceType(((_2_f).dtor_formal).dtor_tpe, _1_replacement), _pat_let15_0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(_pat_let15_0, _5_dt__update_htpe_h0 => RAST.Formal.create((_4_dt__update__tmp_h1).dtor_name, _5_dt__update_htpe_h0))))), _pat_let13_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(_pat_let13_0, _6_dt__update_hformal_h0 => RAST.Field.create((_3_dt__update__tmp_h0).dtor_visibility, _6_dt__update_hformal_h0)))));
})))(replacement), _0_sFields));
        }
      }
      {
        Dafny.ISequence<RAST._INamelessField> _7_sFields = _source0.dtor_types;
        return RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._INamelessField, RAST._INamelessField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._INamelessField, RAST._INamelessField>>>((_8_replacement) => ((System.Func<RAST._INamelessField, RAST._INamelessField>)((_9_f) => {
  return Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_9_f, _pat_let16_0 => Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_pat_let16_0, _10_dt__update__tmp_h2 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(FactorPathsOptimization.__default.ReplaceType((_9_f).dtor_tpe, _8_replacement), _pat_let17_0 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(_pat_let17_0, _11_dt__update_htpe_h1 => RAST.NamelessField.create((_10_dt__update__tmp_h2).dtor_visibility, _11_dt__update_htpe_h1)))));
})))(replacement), _7_sFields));
      }
    }
    public static Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>> typeReplacer { get {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>)((_0_replacement) => {
        return Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_2_t) => {
          return FactorPathsOptimization.__default.ReplaceType(_2_t, _1_replacement);
        })))(_0_replacement);
      }));
    } }
  }

  public interface _IMapping {
    bool is_Mapping { get; }
    Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> dtor_provenance { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_keys { get; }
    _IMapping DowncastClone();
    FactorPathsOptimization._IMapping Add(Dafny.ISequence<Dafny.Rune> k, RAST._IPath path);
    Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement();
    Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath);
  }
  public class Mapping : _IMapping {
    public readonly Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _provenance;
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _keys;
    public Mapping(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> provenance, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> keys) {
      this._provenance = provenance;
      this._keys = keys;
    }
    public _IMapping DowncastClone() {
      if (this is _IMapping dt) { return dt; }
      return new Mapping(_provenance, _keys);
    }
    public override bool Equals(object other) {
      var oth = other as FactorPathsOptimization.Mapping;
      return oth != null && object.Equals(this._provenance, oth._provenance) && object.Equals(this._keys, oth._keys);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._provenance));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keys));
      return (int) hash;
    }
    public override string ToString() {
      string s = "FactorPathsOptimization.Mapping.Mapping";
      s += "(";
      s += Dafny.Helpers.ToString(this._provenance);
      s += ", ";
      s += Dafny.Helpers.ToString(this._keys);
      s += ")";
      return s;
    }
    private static readonly FactorPathsOptimization._IMapping theDefault = create(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Empty, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty);
    public static FactorPathsOptimization._IMapping Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<FactorPathsOptimization._IMapping> _TYPE = new Dafny.TypeDescriptor<FactorPathsOptimization._IMapping>(FactorPathsOptimization.Mapping.Default());
    public static Dafny.TypeDescriptor<FactorPathsOptimization._IMapping> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMapping create(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> provenance, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> keys) {
      return new Mapping(provenance, keys);
    }
    public static _IMapping create_Mapping(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> provenance, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> keys) {
      return create(provenance, keys);
    }
    public bool is_Mapping { get { return true; } }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> dtor_provenance {
      get {
        return this._provenance;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_keys {
      get {
        return this._keys;
      }
    }
    public FactorPathsOptimization._IMapping Add(Dafny.ISequence<Dafny.Rune> k, RAST._IPath path)
    {
      if (((this).dtor_provenance).Contains(k)) {
        FactorPathsOptimization._IMapping _0_dt__update__tmp_h0 = this;
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1_dt__update_hprovenance_h0 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.Union(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,k), Dafny.Set<RAST._IPath>.FromElements(path)));
        return FactorPathsOptimization.Mapping.create(_1_dt__update_hprovenance_h0, (_0_dt__update__tmp_h0).dtor_keys);
      } else {
        FactorPathsOptimization._IMapping _2_dt__update__tmp_h1 = this;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _3_dt__update_hkeys_h0 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_keys, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(k));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _4_dt__update_hprovenance_h1 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.FromElements(path));
        return FactorPathsOptimization.Mapping.create(_4_dt__update_hprovenance_h1, _3_dt__update_hkeys_h0);
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement() {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in ((this).dtor_provenance).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _0_identifier = (Dafny.ISequence<Dafny.Rune>)_compr_0;
          if (((this).dtor_provenance).Contains(_0_identifier)) {
            foreach (Dafny.ISet<RAST._IPath> _compr_1 in Dafny.Helpers.SingleValue<Dafny.ISet<RAST._IPath>>(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_0_identifier))) {
              Dafny.ISet<RAST._IPath> _1_paths = (Dafny.ISet<RAST._IPath>)_compr_1;
              if (((_1_paths).Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_0_identifier))) && (((new BigInteger((_1_paths).Count)) == (BigInteger.One)) || (Dafny.Helpers.Id<Func<Dafny.ISet<RAST._IPath>, bool>>((_2_paths) => Dafny.Helpers.Quantifier<RAST._IPath>(Dafny.Helpers.SingleValue<RAST._IPath>(RAST.__default.dafny__runtime), false, (((_exists_var_0) => {
                RAST._IPath _3_p = (RAST._IPath)_exists_var_0;
                return ((_2_paths).Contains(_3_p)) && (object.Equals(_3_p, RAST.__default.dafny__runtime));
              }))))(_1_paths)))) {
                _coll0.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>(_0_identifier, (((new BigInteger((_1_paths).Count)) == (BigInteger.One)) ? (FactorPathsOptimization.__default.UniqueElementOf<RAST._IPath>(_1_paths)) : (RAST.__default.dafny__runtime))));
              }
            }
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IPath>.FromCollection(_coll0);
      }))();
    }
    public Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_toUse = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IPath, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1_finalReplacement, _2_SelfPath) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_3_key) => {
        return ((_1_finalReplacement).Contains(_3_key)) && (!object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_1_finalReplacement,_3_key), _2_SelfPath));
      })))(finalReplacement, SelfPath), (this).dtor_keys);
      return ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
        BigInteger dim12 = new BigInteger((_0_toUse).Count);
        var arr12 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
        for (int i12 = 0; i12 < dim12; i12++) {
          var _4_i = (BigInteger) i12;
          arr12[(int)(_4_i)] = RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(finalReplacement,(_0_toUse).Select(_4_i))).MSel((_0_toUse).Select(_4_i))));
        }
        return Dafny.Sequence<RAST._IModDecl>.FromArray(arr12);
      }))();
    }
  }
} // end of namespace FactorPathsOptimization