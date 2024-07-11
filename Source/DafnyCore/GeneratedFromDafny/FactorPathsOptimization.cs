// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace FactorPathsOptimization {

  public partial class __default {
    public static RAST._IMod apply(RAST._IMod mod) {
      return FactorPathsOptimization.__default.applyPrefix(mod, (RAST.__default.crate).MSel((mod).dtor_name));
    }
    public static RAST._IMod applyPrefix(RAST._IMod mod, RAST._IPath SelfPath)
    {
      if ((mod).is_ExternMod) {
        return mod;
      } else {
        FactorPathsOptimization._IMapping _1148_initialMapping = FactorPathsOptimization.Mapping.create(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.FromElements(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        FactorPathsOptimization._IMapping _1149_mappings = (mod).Fold<FactorPathsOptimization._IMapping>(_1148_initialMapping, Dafny.Helpers.Id<Func<RAST._IPath, Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>>>((_1150_SelfPath) => ((System.Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>)((_1151_current, _1152_modDecl) => {
          return FactorPathsOptimization.__default.GatherModMapping(_1150_SelfPath, _1152_modDecl, _1151_current);
        })))(SelfPath));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> _1153_pathsToRemove = (_1149_mappings).ToFinalReplacement();
        Dafny.ISequence<RAST._IModDecl> _1154_imports = (_1149_mappings).ToUseStatements(_1153_pathsToRemove, SelfPath);
        Dafny.ISequence<RAST._IModDecl> _1155_rewrittenDeclarations = (mod).Fold<Dafny.ISequence<RAST._IModDecl>>(Dafny.Sequence<RAST._IModDecl>.FromElements(), Dafny.Helpers.Id<Func<RAST._IPath, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IMod, Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>>>((_1156_SelfPath, _1157_pathsToRemove, _1158_mod) => ((System.Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>)((_1159_current, _1160_modDecl) => {
          return Dafny.Sequence<RAST._IModDecl>.Concat(_1159_current, Dafny.Sequence<RAST._IModDecl>.FromElements(FactorPathsOptimization.__default.ReplaceModDecl(_1160_modDecl, _1156_SelfPath, _1157_pathsToRemove)));
        })))(SelfPath, _1153_pathsToRemove, mod));
        RAST._IMod _1161_dt__update__tmp_h0 = mod;
        Dafny.ISequence<RAST._IModDecl> _1162_dt__update_hbody_h0 = Dafny.Sequence<RAST._IModDecl>.Concat(_1154_imports, _1155_rewrittenDeclarations);
        return RAST.Mod.create_Mod((_1161_dt__update__tmp_h0).dtor_name, _1162_dt__update_hbody_h0);
      }
    }
    public static __T UniqueElementOf<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_9 =>  {
        __T _1163_e = default(__T);
        foreach (__T _assign_such_that_2 in (s).Elements) {
          _1163_e = (__T)_assign_such_that_2;
          if ((s).Contains(_1163_e)) {
            goto after__ASSIGN_SUCH_THAT_2;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 105)");
      after__ASSIGN_SUCH_THAT_2: ;
        return _1163_e;
      }
      );
    }
    public static FactorPathsOptimization._IMapping GatherTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, FactorPathsOptimization._IMapping current)
    {
      return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._ITypeParamDecl>(((System.Func<FactorPathsOptimization._IMapping, RAST._ITypeParamDecl, FactorPathsOptimization._IMapping>)((_1164_current, _1165_t) => {
        return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._IType>(((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_1166_current, _1167_t) => {
          return FactorPathsOptimization.__default.GatherTypeMapping(_1167_t, _1166_current);
        })), _1164_current, (_1165_t).dtor_constraints);
      })), current, typeParams);
    }
    public static FactorPathsOptimization._IMapping GatherFields(RAST._IFields fields, FactorPathsOptimization._IMapping current)
    {
      RAST._IFields _source57 = fields;
      {
        if (_source57.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _1168_sFields = _source57.dtor_fields;
          return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._IField>(((System.Func<FactorPathsOptimization._IMapping, RAST._IField, FactorPathsOptimization._IMapping>)((_1169_current, _1170_f) => {
            return FactorPathsOptimization.__default.GatherTypeMapping(((_1170_f).dtor_formal).dtor_tpe, _1169_current);
          })), current, _1168_sFields);
        }
      }
      {
        Dafny.ISequence<RAST._INamelessField> _1171_sFields = _source57.dtor_types;
        return RAST.__default.FoldLeft<FactorPathsOptimization._IMapping, RAST._INamelessField>(((System.Func<FactorPathsOptimization._IMapping, RAST._INamelessField, FactorPathsOptimization._IMapping>)((_1172_current, _1173_f) => {
          return FactorPathsOptimization.__default.GatherTypeMapping((_1173_f).dtor_tpe, _1172_current);
        })), current, _1171_sFields);
      }
    }
    public static FactorPathsOptimization._IMapping GatherModMapping(RAST._IPath prefix, RAST._IModDecl modDecl, FactorPathsOptimization._IMapping current)
    {
      RAST._IModDecl _source58 = modDecl;
      {
        if (_source58.is_ModDecl) {
          RAST._IMod _1174_mod = _source58.dtor_mod;
          return (current).Add((_1174_mod).dtor_name, prefix);
        }
      }
      {
        if (_source58.is_StructDecl) {
          RAST._IStruct _1175_struct = _source58.dtor_struct;
          return FactorPathsOptimization.__default.GatherStructMapping(_1175_struct, (current).Add((_1175_struct).dtor_name, prefix));
        }
      }
      {
        if (_source58.is_TypeDecl) {
          RAST._ITypeSynonym _1176_tpe = _source58.dtor_tpe;
          return (current).Add((_1176_tpe).dtor_name, prefix);
        }
      }
      {
        if (_source58.is_ConstDecl) {
          RAST._IConstant _1177_c = _source58.dtor_c;
          return (current).Add((_1177_c).dtor_name, prefix);
        }
      }
      {
        if (_source58.is_EnumDecl) {
          RAST._IEnum _1178_enum = _source58.dtor_enum;
          return (current).Add((_1178_enum).dtor_name, prefix);
        }
      }
      {
        if (_source58.is_ImplDecl) {
          RAST._IImpl _1179_impl = _source58.dtor_impl;
          return FactorPathsOptimization.__default.GatherImplMapping(_1179_impl, current);
        }
      }
      {
        if (_source58.is_TraitDecl) {
          RAST._ITrait _1180_tr = _source58.dtor_tr;
          return current;
        }
      }
      {
        if (_source58.is_TopFnDecl) {
          RAST._ITopFnDecl _1181_fn = _source58.dtor_fn;
          return (current).Add(((_1181_fn).dtor_fn).dtor_name, prefix);
        }
      }
      {
        RAST._IUse _1182_use = _source58.dtor_use;
        return current;
      }
    }
    public static FactorPathsOptimization._IMapping GatherStructMapping(RAST._IStruct @struct, FactorPathsOptimization._IMapping current)
    {
      return FactorPathsOptimization.__default.GatherTypeParams((@struct).dtor_typeParams, current);
    }
    public static FactorPathsOptimization._IMapping GatherTypeMapping(RAST._IType tpe, FactorPathsOptimization._IMapping current)
    {
      return (tpe).Fold<FactorPathsOptimization._IMapping>(current, ((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_1183_current, _1184_t) => {
        return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
          RAST._IType _source59 = _1184_t;
          {
            if (_source59.is_TypeFromPath) {
              RAST._IPath path4 = _source59.dtor_path;
              if (path4.is_PMemberSelect) {
                RAST._IPath _1185_base = path4.dtor_base;
                Dafny.ISequence<Dafny.Rune> _1186_name = path4.dtor_name;
                return (_1183_current).Add(_1186_name, _1185_base);
              }
            }
          }
          {
            return _1183_current;
          }
        }))();
      })));
    }
    public static FactorPathsOptimization._IMapping GatherImplMapping(RAST._IImpl impl, FactorPathsOptimization._IMapping current)
    {
      RAST._IImpl _source60 = impl;
      {
        if (_source60.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1187_typeParams = _source60.dtor_typeParams;
          RAST._IType _1188_tpe = _source60.dtor_tpe;
          RAST._IType _1189_forType = _source60.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1190_where = _source60.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1191_body = _source60.dtor_body;
          FactorPathsOptimization._IMapping _1192_current = FactorPathsOptimization.__default.GatherTypeParams(_1187_typeParams, current);
          FactorPathsOptimization._IMapping _1193_current = FactorPathsOptimization.__default.GatherTypeMapping(_1188_tpe, _1192_current);
          return FactorPathsOptimization.__default.GatherTypeMapping(_1189_forType, _1193_current);
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _1194_typeParams = _source60.dtor_typeParams;
        RAST._IType _1195_tpe = _source60.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1196_where = _source60.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1197_body = _source60.dtor_body;
        return FactorPathsOptimization.__default.GatherTypeMapping(_1195_tpe, current);
      }
    }
    public static RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, RAST._IPath SelfPath, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IModDecl _source61 = modDecl;
      {
        if (_source61.is_ModDecl) {
          RAST._IMod _1198_mod = _source61.dtor_mod;
          return RAST.ModDecl.create_ModDecl(FactorPathsOptimization.__default.applyPrefix(_1198_mod, (SelfPath).MSel((_1198_mod).dtor_name)));
        }
      }
      {
        if (_source61.is_StructDecl) {
          RAST._IStruct _1199_struct = _source61.dtor_struct;
          return RAST.ModDecl.create_StructDecl(FactorPathsOptimization.__default.ReplaceStruct(_1199_struct, replacement));
        }
      }
      {
        if (_source61.is_TypeDecl) {
          RAST._ITypeSynonym _1200_tpe = _source61.dtor_tpe;
          return modDecl;
        }
      }
      {
        if (_source61.is_ConstDecl) {
          RAST._IConstant _1201_c = _source61.dtor_c;
          return modDecl;
        }
      }
      {
        if (_source61.is_EnumDecl) {
          RAST._IEnum _1202_enum = _source61.dtor_enum;
          return modDecl;
        }
      }
      {
        if (_source61.is_ImplDecl) {
          RAST._IImpl _1203_impl = _source61.dtor_impl;
          return RAST.ModDecl.create_ImplDecl(FactorPathsOptimization.__default.ReplaceImplDecl(_1203_impl, replacement));
        }
      }
      {
        if (_source61.is_TraitDecl) {
          RAST._ITrait _1204_tr = _source61.dtor_tr;
          return modDecl;
        }
      }
      {
        if (_source61.is_TopFnDecl) {
          RAST._ITopFnDecl _1205_fn = _source61.dtor_fn;
          return modDecl;
        }
      }
      {
        RAST._IUse _1206_use = _source61.dtor_use;
        return modDecl;
      }
    }
    public static RAST._IType ReplaceType(RAST._IType t, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IType _source62 = t;
      {
        if (_source62.is_TypeFromPath) {
          RAST._IPath path5 = _source62.dtor_path;
          if (path5.is_PMemberSelect) {
            RAST._IPath _1207_base = path5.dtor_base;
            Dafny.ISequence<Dafny.Rune> _1208_id = path5.dtor_name;
            if (((replacement).Contains(_1208_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(replacement,_1208_id), _1207_base))) {
              return RAST.Type.create_TSynonym(RAST.Type.create_TIdentifier(_1208_id), t);
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
      return Std.Collections.Seq.__default.Map<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>>>((_1209_replacement) => ((System.Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>)((_1210_t) => {
        return Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1210_t, _pat_let10_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let10_0, _1211_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1212_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1213_constraint) => {
          return FactorPathsOptimization.__default.ReplaceType(_1213_constraint, _1212_replacement);
        })))(_1209_replacement), (_1210_t).dtor_constraints), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let11_0, _1214_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1211_dt__update__tmp_h0).dtor_name, _1214_dt__update_hconstraints_h0)))));
      })))(replacement), typeParams);
    }
    public static RAST._IImpl ReplaceImplDecl(RAST._IImpl impl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IImpl _source63 = impl;
      {
        if (_source63.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1215_typeParams = _source63.dtor_typeParams;
          RAST._IType _1216_tpe = _source63.dtor_tpe;
          RAST._IType _1217_forType = _source63.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1218_where = _source63.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1219_body = _source63.dtor_body;
          return RAST.Impl.create_ImplFor(FactorPathsOptimization.__default.ReplaceTypeParams(_1215_typeParams, replacement), (_1216_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), (_1217_forType).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), _1218_where, _1219_body);
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _1220_typeParams = _source63.dtor_typeParams;
        RAST._IType _1221_tpe = _source63.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1222_where = _source63.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1223_body = _source63.dtor_body;
        return RAST.Impl.create_Impl(FactorPathsOptimization.__default.ReplaceTypeParams(_1220_typeParams, replacement), (_1221_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), _1222_where, _1223_body);
      }
    }
    public static RAST._IStruct ReplaceStruct(RAST._IStruct @struct, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IStruct _source64 = @struct;
      {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1224_attributes = _source64.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _1225_name = _source64.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _1226_typeParams = _source64.dtor_typeParams;
        RAST._IFields _1227_fields = _source64.dtor_fields;
        return RAST.Struct.create(_1224_attributes, _1225_name, FactorPathsOptimization.__default.ReplaceTypeParams(_1226_typeParams, replacement), FactorPathsOptimization.__default.ReplaceFields(_1227_fields, replacement));
      }
    }
    public static RAST._IFields ReplaceFields(RAST._IFields fields, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IFields _source65 = fields;
      {
        if (_source65.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _1228_sFields = _source65.dtor_fields;
          return RAST.Fields.create_NamedFields(Std.Collections.Seq.__default.Map<RAST._IField, RAST._IField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IField, RAST._IField>>>((_1229_replacement) => ((System.Func<RAST._IField, RAST._IField>)((_1230_f) => {
  return Dafny.Helpers.Let<RAST._IField, RAST._IField>(_1230_f, _pat_let12_0 => Dafny.Helpers.Let<RAST._IField, RAST._IField>(_pat_let12_0, _1231_dt__update__tmp_h0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>((_1230_f).dtor_formal, _pat_let14_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>(_pat_let14_0, _1232_dt__update__tmp_h1 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(FactorPathsOptimization.__default.ReplaceType(((_1230_f).dtor_formal).dtor_tpe, _1229_replacement), _pat_let15_0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(_pat_let15_0, _1233_dt__update_htpe_h0 => RAST.Formal.create((_1232_dt__update__tmp_h1).dtor_name, _1233_dt__update_htpe_h0))))), _pat_let13_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(_pat_let13_0, _1234_dt__update_hformal_h0 => RAST.Field.create((_1231_dt__update__tmp_h0).dtor_visibility, _1234_dt__update_hformal_h0)))));
})))(replacement), _1228_sFields));
        }
      }
      {
        Dafny.ISequence<RAST._INamelessField> _1235_sFields = _source65.dtor_types;
        return RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._INamelessField, RAST._INamelessField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._INamelessField, RAST._INamelessField>>>((_1236_replacement) => ((System.Func<RAST._INamelessField, RAST._INamelessField>)((_1237_f) => {
  return Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_1237_f, _pat_let16_0 => Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_pat_let16_0, _1238_dt__update__tmp_h2 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(FactorPathsOptimization.__default.ReplaceType((_1237_f).dtor_tpe, _1236_replacement), _pat_let17_0 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(_pat_let17_0, _1239_dt__update_htpe_h1 => RAST.NamelessField.create((_1238_dt__update__tmp_h2).dtor_visibility, _1239_dt__update_htpe_h1)))));
})))(replacement), _1235_sFields));
      }
    }
    public static Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>> typeReplacer { get {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>)((_1240_replacement) => {
        return Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1241_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1242_t) => {
          return FactorPathsOptimization.__default.ReplaceType(_1242_t, _1241_replacement);
        })))(_1240_replacement);
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
        FactorPathsOptimization._IMapping _1243_dt__update__tmp_h0 = this;
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1244_dt__update_hprovenance_h0 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.Union(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,k), Dafny.Set<RAST._IPath>.FromElements(path)));
        return FactorPathsOptimization.Mapping.create(_1244_dt__update_hprovenance_h0, (_1243_dt__update__tmp_h0).dtor_keys);
      } else {
        FactorPathsOptimization._IMapping _1245_dt__update__tmp_h1 = this;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1246_dt__update_hkeys_h0 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_keys, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(k));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1247_dt__update_hprovenance_h1 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.FromElements(path));
        return FactorPathsOptimization.Mapping.create(_1247_dt__update_hprovenance_h1, _1246_dt__update_hkeys_h0);
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement() {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_provenance).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1248_identifier = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_provenance).Contains(_1248_identifier)) {
            foreach (Dafny.ISet<RAST._IPath> _compr_7 in Dafny.Helpers.SingleValue<Dafny.ISet<RAST._IPath>>(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1248_identifier))) {
              Dafny.ISet<RAST._IPath> _1249_paths = (Dafny.ISet<RAST._IPath>)_compr_7;
              if (((_1249_paths).Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1248_identifier))) && (((new BigInteger((_1249_paths).Count)) == (BigInteger.One)) || (Dafny.Helpers.Id<Func<Dafny.ISet<RAST._IPath>, bool>>((_1250_paths) => Dafny.Helpers.Quantifier<RAST._IPath>(Dafny.Helpers.SingleValue<RAST._IPath>(RAST.__default.dafny__runtime), false, (((_exists_var_1) => {
                RAST._IPath _1251_p = (RAST._IPath)_exists_var_1;
                return ((_1250_paths).Contains(_1251_p)) && (object.Equals(_1251_p, RAST.__default.dafny__runtime));
              }))))(_1249_paths)))) {
                _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>(_1248_identifier, (((new BigInteger((_1249_paths).Count)) == (BigInteger.One)) ? (FactorPathsOptimization.__default.UniqueElementOf<RAST._IPath>(_1249_paths)) : (RAST.__default.dafny__runtime))));
              }
            }
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IPath>.FromCollection(_coll6);
      }))();
    }
    public Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1252_toUse = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IPath, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1253_finalReplacement, _1254_SelfPath) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_1255_key) => {
        return ((_1253_finalReplacement).Contains(_1255_key)) && (!object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_1253_finalReplacement,_1255_key), _1254_SelfPath));
      })))(finalReplacement, SelfPath), (this).dtor_keys);
      return ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
        BigInteger dim12 = new BigInteger((_1252_toUse).Count);
        var arr12 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
        for (int i12 = 0; i12 < dim12; i12++) {
          var _1256_i = (BigInteger) i12;
          arr12[(int)(_1256_i)] = RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(finalReplacement,(_1252_toUse).Select(_1256_i))).MSel((_1252_toUse).Select(_1256_i))));
        }
        return Dafny.Sequence<RAST._IModDecl>.FromArray(arr12);
      }))();
    }
  }
} // end of namespace FactorPathsOptimization