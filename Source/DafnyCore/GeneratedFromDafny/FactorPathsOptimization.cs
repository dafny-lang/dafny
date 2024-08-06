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
      if ((mod).is_ExternMod) {
        return mod;
      } else {
        RAST._IPath _1149_SelfPath = (RAST.__default.crate).MSel((mod).dtor_name);
        FactorPathsOptimization._IMapping _1150_initialMapping = FactorPathsOptimization.Mapping.create(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.FromElements(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        FactorPathsOptimization._IMapping _1151_mappings = (mod).Fold<FactorPathsOptimization._IMapping>(_1150_initialMapping, Dafny.Helpers.Id<Func<RAST._IPath, Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>>>((_1152_SelfPath) => ((System.Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>)((_1153_current, _1154_modDecl) => {
          return FactorPathsOptimization.__default.GatherModMapping(_1152_SelfPath, _1154_modDecl, _1153_current);
        })))(_1149_SelfPath));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> _1155_pathsToRemove = (_1151_mappings).ToFinalReplacement();
        Dafny.ISequence<RAST._IModDecl> _1156_imports = (_1151_mappings).ToUseStatements(_1155_pathsToRemove, _1149_SelfPath);
        Dafny.ISequence<RAST._IModDecl> _1157_rewrittenDeclarations = (mod).Fold<Dafny.ISequence<RAST._IModDecl>>(Dafny.Sequence<RAST._IModDecl>.FromElements(), Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IMod, Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>>>((_1158_pathsToRemove, _1159_mod) => ((System.Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>)((_1160_current, _1161_modDecl) => {
          return Dafny.Sequence<RAST._IModDecl>.Concat(_1160_current, Dafny.Sequence<RAST._IModDecl>.FromElements(FactorPathsOptimization.__default.ReplaceModDecl(_1161_modDecl, _1158_pathsToRemove)));
        })))(_1155_pathsToRemove, mod));
        Dafny.ISequence<RAST._IModDecl> _1162_newBody = Dafny.Sequence<RAST._IModDecl>.Concat(_1156_imports, _1157_rewrittenDeclarations);
        RAST._IMod _1163_dt__update__tmp_h0 = mod;
        Dafny.ISequence<RAST._IModDecl> _1164_dt__update_hbody_h0 = _1162_newBody;
        return RAST.Mod.create_Mod((_1163_dt__update__tmp_h0).dtor_name, (_1163_dt__update__tmp_h0).dtor_attributes, _1164_dt__update_hbody_h0);
      }
    }
    public static __T UniqueElementOf<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_9 =>  {
        __T _1165_e = default(__T);
        foreach (__T _assign_such_that_2 in (s).Elements) {
          _1165_e = (__T)_assign_such_that_2;
          if ((s).Contains(_1165_e)) {
            goto after__ASSIGN_SUCH_THAT_2;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 89)");
      after__ASSIGN_SUCH_THAT_2: ;
        return _1165_e;
      }
      );
    }
    public static FactorPathsOptimization._IMapping GatherModMapping(RAST._IPath prefix, RAST._IModDecl modDecl, FactorPathsOptimization._IMapping current)
    {
      var _pat_let_tv149 = current;
      var _pat_let_tv150 = prefix;
      var _pat_let_tv151 = current;
      var _pat_let_tv152 = prefix;
      var _pat_let_tv153 = current;
      var _pat_let_tv154 = prefix;
      var _pat_let_tv155 = current;
      var _pat_let_tv156 = prefix;
      var _pat_let_tv157 = current;
      var _pat_let_tv158 = prefix;
      var _pat_let_tv159 = current;
      var _pat_let_tv160 = current;
      var _pat_let_tv161 = current;
      var _pat_let_tv162 = prefix;
      var _pat_let_tv163 = current;
      RAST._IModDecl _source57 = modDecl;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_ModDecl) {
          RAST._IMod _1166_mod = _source57.dtor_mod;
          unmatched57 = false;
          return (_pat_let_tv149).Add((_1166_mod).dtor_name, _pat_let_tv150);
        }
      }
      if (unmatched57) {
        if (_source57.is_StructDecl) {
          RAST._IStruct _1167_struct = _source57.dtor_struct;
          unmatched57 = false;
          return (_pat_let_tv151).Add((_1167_struct).dtor_name, _pat_let_tv152);
        }
      }
      if (unmatched57) {
        if (_source57.is_TypeDecl) {
          RAST._ITypeSynonym _1168_tpe = _source57.dtor_tpe;
          unmatched57 = false;
          return (_pat_let_tv153).Add((_1168_tpe).dtor_name, _pat_let_tv154);
        }
      }
      if (unmatched57) {
        if (_source57.is_ConstDecl) {
          RAST._IConstant _1169_c = _source57.dtor_c;
          unmatched57 = false;
          return (_pat_let_tv155).Add((_1169_c).dtor_name, _pat_let_tv156);
        }
      }
      if (unmatched57) {
        if (_source57.is_EnumDecl) {
          RAST._IEnum _1170_enum = _source57.dtor_enum;
          unmatched57 = false;
          return (_pat_let_tv157).Add((_1170_enum).dtor_name, _pat_let_tv158);
        }
      }
      if (unmatched57) {
        if (_source57.is_ImplDecl) {
          RAST._IImpl _1171_impl = _source57.dtor_impl;
          unmatched57 = false;
          return FactorPathsOptimization.__default.GatherImplMapping(_1171_impl, _pat_let_tv159);
        }
      }
      if (unmatched57) {
        if (_source57.is_TraitDecl) {
          RAST._ITrait _1172_tr = _source57.dtor_tr;
          unmatched57 = false;
          return _pat_let_tv160;
        }
      }
      if (unmatched57) {
        if (_source57.is_TopFnDecl) {
          RAST._ITopFnDecl _1173_fn = _source57.dtor_fn;
          unmatched57 = false;
          return (_pat_let_tv161).Add(((_1173_fn).dtor_fn).dtor_name, _pat_let_tv162);
        }
      }
      if (unmatched57) {
        RAST._IUse _1174_use = _source57.dtor_use;
        unmatched57 = false;
        return _pat_let_tv163;
      }
      throw new System.Exception("unexpected control point");
    }
    public static FactorPathsOptimization._IMapping GatherTypeMapping(RAST._IType tpe, FactorPathsOptimization._IMapping current)
    {
      return (tpe).Fold<FactorPathsOptimization._IMapping>(current, ((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_1175_current, _1176_t) => {
        return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
          RAST._IType _source58 = _1176_t;
          bool unmatched58 = true;
          if (unmatched58) {
            if (_source58.is_TypeFromPath) {
              RAST._IPath path4 = _source58.dtor_path;
              if (path4.is_PMemberSelect) {
                RAST._IPath _1177_base = path4.dtor_base;
                Dafny.ISequence<Dafny.Rune> _1178_name = path4.dtor_name;
                unmatched58 = false;
                return (_1175_current).Add(_1178_name, _1177_base);
              }
            }
          }
          if (unmatched58) {
            unmatched58 = false;
            return _1175_current;
          }
          throw new System.Exception("unexpected control point");
        }))();
      })));
    }
    public static FactorPathsOptimization._IMapping GatherImplMapping(RAST._IImpl impl, FactorPathsOptimization._IMapping current)
    {
      var _pat_let_tv164 = current;
      var _pat_let_tv165 = current;
      RAST._IImpl _source59 = impl;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1179_typeParams = _source59.dtor_typeParams;
          RAST._IType _1180_tpe = _source59.dtor_tpe;
          RAST._IType _1181_forType = _source59.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1182_where = _source59.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1183_body = _source59.dtor_body;
          unmatched59 = false;
          return FactorPathsOptimization.__default.GatherTypeMapping(_1181_forType, FactorPathsOptimization.__default.GatherTypeMapping(_1180_tpe, _pat_let_tv164));
        }
      }
      if (unmatched59) {
        Dafny.ISequence<RAST._ITypeParamDecl> _1184_typeParams = _source59.dtor_typeParams;
        RAST._IType _1185_tpe = _source59.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1186_where = _source59.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1187_body = _source59.dtor_body;
        unmatched59 = false;
        return FactorPathsOptimization.__default.GatherTypeMapping(_1185_tpe, _pat_let_tv165);
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv166 = replacement;
      var _pat_let_tv167 = modDecl;
      var _pat_let_tv168 = modDecl;
      var _pat_let_tv169 = modDecl;
      var _pat_let_tv170 = replacement;
      var _pat_let_tv171 = modDecl;
      var _pat_let_tv172 = modDecl;
      var _pat_let_tv173 = modDecl;
      RAST._IModDecl _source60 = modDecl;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_ModDecl) {
          RAST._IMod _1188_mod = _source60.dtor_mod;
          unmatched60 = false;
          return RAST.ModDecl.create_ModDecl(FactorPathsOptimization.__default.apply(_1188_mod));
        }
      }
      if (unmatched60) {
        if (_source60.is_StructDecl) {
          RAST._IStruct _1189_struct = _source60.dtor_struct;
          unmatched60 = false;
          return RAST.ModDecl.create_StructDecl(FactorPathsOptimization.__default.ReplaceStruct(_1189_struct, _pat_let_tv166));
        }
      }
      if (unmatched60) {
        if (_source60.is_TypeDecl) {
          RAST._ITypeSynonym _1190_tpe = _source60.dtor_tpe;
          unmatched60 = false;
          return _pat_let_tv167;
        }
      }
      if (unmatched60) {
        if (_source60.is_ConstDecl) {
          RAST._IConstant _1191_c = _source60.dtor_c;
          unmatched60 = false;
          return _pat_let_tv168;
        }
      }
      if (unmatched60) {
        if (_source60.is_EnumDecl) {
          RAST._IEnum _1192_enum = _source60.dtor_enum;
          unmatched60 = false;
          return _pat_let_tv169;
        }
      }
      if (unmatched60) {
        if (_source60.is_ImplDecl) {
          RAST._IImpl _1193_impl = _source60.dtor_impl;
          unmatched60 = false;
          return RAST.ModDecl.create_ImplDecl(FactorPathsOptimization.__default.ReplaceImplDecl(_1193_impl, _pat_let_tv170));
        }
      }
      if (unmatched60) {
        if (_source60.is_TraitDecl) {
          RAST._ITrait _1194_tr = _source60.dtor_tr;
          unmatched60 = false;
          return _pat_let_tv171;
        }
      }
      if (unmatched60) {
        if (_source60.is_TopFnDecl) {
          RAST._ITopFnDecl _1195_fn = _source60.dtor_fn;
          unmatched60 = false;
          return _pat_let_tv172;
        }
      }
      if (unmatched60) {
        RAST._IUse _1196_use = _source60.dtor_use;
        unmatched60 = false;
        return _pat_let_tv173;
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IType ReplaceType(RAST._IType t, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv174 = replacement;
      var _pat_let_tv175 = replacement;
      var _pat_let_tv176 = t;
      var _pat_let_tv177 = t;
      var _pat_let_tv178 = t;
      RAST._IType _source61 = t;
      bool unmatched61 = true;
      if (unmatched61) {
        if (_source61.is_TypeFromPath) {
          RAST._IPath path5 = _source61.dtor_path;
          if (path5.is_PMemberSelect) {
            RAST._IPath _1197_base = path5.dtor_base;
            Dafny.ISequence<Dafny.Rune> _1198_id = path5.dtor_name;
            unmatched61 = false;
            if (((_pat_let_tv174).Contains(_1198_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_pat_let_tv175,_1198_id), _1197_base))) {
              return RAST.Type.create_TSynonym(RAST.Type.create_TIdentifier(_1198_id), _pat_let_tv176);
            } else {
              return _pat_let_tv177;
            }
          }
        }
      }
      if (unmatched61) {
        unmatched61 = false;
        return _pat_let_tv178;
      }
      throw new System.Exception("unexpected control point");
    }
    public static Dafny.ISequence<RAST._ITypeParamDecl> ReplaceTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      return Std.Collections.Seq.__default.Map<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>>>((_1199_replacement) => ((System.Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>)((_1200_t) => {
        return Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1200_t, _pat_let10_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let10_0, _1201_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1202_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1203_constraint) => {
          return FactorPathsOptimization.__default.ReplaceType(_1203_constraint, _1202_replacement);
        })))(_1199_replacement), (_1200_t).dtor_constraints), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let11_0, _1204_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1201_dt__update__tmp_h0).dtor_name, _1204_dt__update_hconstraints_h0)))));
      })))(replacement), typeParams);
    }
    public static RAST._IImpl ReplaceImplDecl(RAST._IImpl impl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv179 = replacement;
      var _pat_let_tv180 = replacement;
      var _pat_let_tv181 = replacement;
      var _pat_let_tv182 = replacement;
      var _pat_let_tv183 = replacement;
      RAST._IImpl _source62 = impl;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1205_typeParams = _source62.dtor_typeParams;
          RAST._IType _1206_tpe = _source62.dtor_tpe;
          RAST._IType _1207_forType = _source62.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1208_where = _source62.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1209_body = _source62.dtor_body;
          unmatched62 = false;
          return RAST.Impl.create_ImplFor(FactorPathsOptimization.__default.ReplaceTypeParams(_1205_typeParams, _pat_let_tv179), (_1206_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv180)), (_1207_forType).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv181)), _1208_where, _1209_body);
        }
      }
      if (unmatched62) {
        Dafny.ISequence<RAST._ITypeParamDecl> _1210_typeParams = _source62.dtor_typeParams;
        RAST._IType _1211_tpe = _source62.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1212_where = _source62.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1213_body = _source62.dtor_body;
        unmatched62 = false;
        return RAST.Impl.create_Impl(FactorPathsOptimization.__default.ReplaceTypeParams(_1210_typeParams, _pat_let_tv182), (_1211_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv183)), _1212_where, _1213_body);
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IStruct ReplaceStruct(RAST._IStruct @struct, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv184 = replacement;
      var _pat_let_tv185 = replacement;
      RAST._IStruct _source63 = @struct;
      bool unmatched63 = true;
      if (unmatched63) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1214_attributes = _source63.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _1215_name = _source63.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _1216_typeParams = _source63.dtor_typeParams;
        RAST._IFields _1217_fields = _source63.dtor_fields;
        unmatched63 = false;
        return RAST.Struct.create(_1214_attributes, _1215_name, FactorPathsOptimization.__default.ReplaceTypeParams(_1216_typeParams, _pat_let_tv184), FactorPathsOptimization.__default.ReplaceFields(_1217_fields, _pat_let_tv185));
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IFields ReplaceFields(RAST._IFields fields, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv186 = replacement;
      var _pat_let_tv187 = replacement;
      RAST._IFields _source64 = fields;
      bool unmatched64 = true;
      if (unmatched64) {
        if (_source64.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _1218_sFields = _source64.dtor_fields;
          unmatched64 = false;
          return RAST.Fields.create_NamedFields(Std.Collections.Seq.__default.Map<RAST._IField, RAST._IField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IField, RAST._IField>>>((_1219_replacement) => ((System.Func<RAST._IField, RAST._IField>)((_1220_f) => {
  return Dafny.Helpers.Let<RAST._IField, RAST._IField>(_1220_f, _pat_let12_0 => Dafny.Helpers.Let<RAST._IField, RAST._IField>(_pat_let12_0, _1221_dt__update__tmp_h0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>((_1220_f).dtor_formal, _pat_let14_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>(_pat_let14_0, _1222_dt__update__tmp_h1 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(FactorPathsOptimization.__default.ReplaceType(((_1220_f).dtor_formal).dtor_tpe, _1219_replacement), _pat_let15_0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(_pat_let15_0, _1223_dt__update_htpe_h0 => RAST.Formal.create((_1222_dt__update__tmp_h1).dtor_name, _1223_dt__update_htpe_h0))))), _pat_let13_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(_pat_let13_0, _1224_dt__update_hformal_h0 => RAST.Field.create((_1221_dt__update__tmp_h0).dtor_visibility, _1224_dt__update_hformal_h0)))));
})))(_pat_let_tv186), _1218_sFields));
        }
      }
      if (unmatched64) {
        Dafny.ISequence<RAST._INamelessField> _1225_sFields = _source64.dtor_types;
        unmatched64 = false;
        return RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._INamelessField, RAST._INamelessField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._INamelessField, RAST._INamelessField>>>((_1226_replacement) => ((System.Func<RAST._INamelessField, RAST._INamelessField>)((_1227_f) => {
  return Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_1227_f, _pat_let16_0 => Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_pat_let16_0, _1228_dt__update__tmp_h2 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(FactorPathsOptimization.__default.ReplaceType((_1227_f).dtor_tpe, _1226_replacement), _pat_let17_0 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(_pat_let17_0, _1229_dt__update_htpe_h1 => RAST.NamelessField.create((_1228_dt__update__tmp_h2).dtor_visibility, _1229_dt__update_htpe_h1)))));
})))(_pat_let_tv187), _1225_sFields));
      }
      throw new System.Exception("unexpected control point");
    }
    public static Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>> typeReplacer { get {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>)((_1230_replacement) => {
        return Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1231_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1232_t) => {
          return FactorPathsOptimization.__default.ReplaceType(_1232_t, _1231_replacement);
        })))(_1230_replacement);
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
        FactorPathsOptimization._IMapping _1233_dt__update__tmp_h0 = this;
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1234_dt__update_hprovenance_h0 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.Union(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,k), Dafny.Set<RAST._IPath>.FromElements(path)));
        return FactorPathsOptimization.Mapping.create(_1234_dt__update_hprovenance_h0, (_1233_dt__update__tmp_h0).dtor_keys);
      } else {
        FactorPathsOptimization._IMapping _1235_dt__update__tmp_h1 = this;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1236_dt__update_hkeys_h0 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_keys, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(k));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1237_dt__update_hprovenance_h1 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.FromElements(path));
        return FactorPathsOptimization.Mapping.create(_1237_dt__update_hprovenance_h1, _1236_dt__update_hkeys_h0);
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement() {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_provenance).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1238_identifier = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_provenance).Contains(_1238_identifier)) {
            foreach (Dafny.ISet<RAST._IPath> _compr_7 in Dafny.Helpers.SingleValue<Dafny.ISet<RAST._IPath>>(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1238_identifier))) {
              Dafny.ISet<RAST._IPath> _1239_paths = (Dafny.ISet<RAST._IPath>)_compr_7;
              if (((_1239_paths).Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1238_identifier))) && (((new BigInteger((_1239_paths).Count)) == (BigInteger.One)) || (Dafny.Helpers.Id<Func<Dafny.ISet<RAST._IPath>, bool>>((_1240_paths) => Dafny.Helpers.Quantifier<RAST._IPath>(Dafny.Helpers.SingleValue<RAST._IPath>(RAST.__default.dafny__runtime), false, (((_exists_var_1) => {
                RAST._IPath _1241_p = (RAST._IPath)_exists_var_1;
                return ((_1240_paths).Contains(_1241_p)) && (object.Equals(_1241_p, RAST.__default.dafny__runtime));
              }))))(_1239_paths)))) {
                _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>(_1238_identifier, (((new BigInteger((_1239_paths).Count)) == (BigInteger.One)) ? (FactorPathsOptimization.__default.UniqueElementOf<RAST._IPath>(_1239_paths)) : (RAST.__default.dafny__runtime))));
              }
            }
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IPath>.FromCollection(_coll6);
      }))();
    }
    public Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1242_toUse = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IPath, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1243_finalReplacement, _1244_SelfPath) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_1245_key) => {
        return ((_1243_finalReplacement).Contains(_1245_key)) && (!object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_1243_finalReplacement,_1245_key), _1244_SelfPath));
      })))(finalReplacement, SelfPath), (this).dtor_keys);
      return ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
        BigInteger dim12 = new BigInteger((_1242_toUse).Count);
        var arr12 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
        for (int i12 = 0; i12 < dim12; i12++) {
          var _1246_i = (BigInteger) i12;
          arr12[(int)(_1246_i)] = RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(finalReplacement,(_1242_toUse).Select(_1246_i))).MSel((_1242_toUse).Select(_1246_i))));
        }
        return Dafny.Sequence<RAST._IModDecl>.FromArray(arr12);
      }))();
    }
  }
} // end of namespace FactorPathsOptimization