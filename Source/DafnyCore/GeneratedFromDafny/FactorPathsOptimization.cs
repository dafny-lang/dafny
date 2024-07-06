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
        RAST._IPath _1158_SelfPath = (RAST.__default.crate).MSel((mod).dtor_name);
        FactorPathsOptimization._IMapping _1159_initialMapping = FactorPathsOptimization.Mapping.create(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.FromElements(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        FactorPathsOptimization._IMapping _1160_mappings = (mod).Fold<FactorPathsOptimization._IMapping>(_1159_initialMapping, Dafny.Helpers.Id<Func<RAST._IPath, Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>>>((_1161_SelfPath) => ((System.Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>)((_1162_current, _1163_modDecl) => {
          return FactorPathsOptimization.__default.GatherModMapping(_1161_SelfPath, _1163_modDecl, _1162_current);
        })))(_1158_SelfPath));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> _1164_pathsToRemove = (_1160_mappings).ToFinalReplacement();
        Dafny.ISequence<RAST._IModDecl> _1165_imports = (_1160_mappings).ToUseStatements(_1164_pathsToRemove, _1158_SelfPath);
        Dafny.ISequence<RAST._IModDecl> _1166_rewrittenDeclarations = (mod).Fold<Dafny.ISequence<RAST._IModDecl>>(Dafny.Sequence<RAST._IModDecl>.FromElements(), Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>>>((_1167_pathsToRemove) => ((System.Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>)((_1168_current, _1169_modDecl) => {
          return Dafny.Sequence<RAST._IModDecl>.Concat(_1168_current, Dafny.Sequence<RAST._IModDecl>.FromElements(FactorPathsOptimization.__default.ReplaceModDecl(_1169_modDecl, _1167_pathsToRemove)));
        })))(_1164_pathsToRemove));
        Dafny.ISequence<RAST._IModDecl> _1170_newBody = Dafny.Sequence<RAST._IModDecl>.Concat(_1165_imports, _1166_rewrittenDeclarations);
        RAST._IMod _1171_dt__update__tmp_h0 = mod;
        Dafny.ISequence<RAST._IModDecl> _1172_dt__update_hbody_h0 = _1170_newBody;
        return RAST.Mod.create_Mod((_1171_dt__update__tmp_h0).dtor_name, _1172_dt__update_hbody_h0);
      }
    }
    public static __T UniqueElementOf<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_9 =>  {
        __T _1173_e = default(__T);
        foreach (__T _assign_such_that_2 in (s).Elements) {
          _1173_e = (__T)_assign_such_that_2;
          if ((s).Contains(_1173_e)) {
            goto after__ASSIGN_SUCH_THAT_2;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 89)");
      after__ASSIGN_SUCH_THAT_2: ;
        return _1173_e;
      }
      );
    }
    public static FactorPathsOptimization._IMapping GatherModMapping(RAST._IPath prefix, RAST._IModDecl modDecl, FactorPathsOptimization._IMapping current)
    {
      var _pat_let_tv154 = current;
      var _pat_let_tv155 = prefix;
      var _pat_let_tv156 = current;
      var _pat_let_tv157 = prefix;
      var _pat_let_tv158 = current;
      var _pat_let_tv159 = prefix;
      var _pat_let_tv160 = current;
      var _pat_let_tv161 = prefix;
      var _pat_let_tv162 = current;
      var _pat_let_tv163 = prefix;
      var _pat_let_tv164 = current;
      var _pat_let_tv165 = current;
      var _pat_let_tv166 = current;
      var _pat_let_tv167 = prefix;
      var _pat_let_tv168 = current;
      RAST._IModDecl _source55 = modDecl;
      bool unmatched55 = true;
      if (unmatched55) {
        if (_source55.is_ModDecl) {
          RAST._IMod _1174_mod = _source55.dtor_mod;
          unmatched55 = false;
          return (_pat_let_tv154).Add((_1174_mod).dtor_name, _pat_let_tv155);
        }
      }
      if (unmatched55) {
        if (_source55.is_StructDecl) {
          RAST._IStruct _1175_struct = _source55.dtor_struct;
          unmatched55 = false;
          return (_pat_let_tv156).Add((_1175_struct).dtor_name, _pat_let_tv157);
        }
      }
      if (unmatched55) {
        if (_source55.is_TypeDecl) {
          RAST._ITypeSynonym _1176_tpe = _source55.dtor_tpe;
          unmatched55 = false;
          return (_pat_let_tv158).Add((_1176_tpe).dtor_name, _pat_let_tv159);
        }
      }
      if (unmatched55) {
        if (_source55.is_ConstDecl) {
          RAST._IConstant _1177_c = _source55.dtor_c;
          unmatched55 = false;
          return (_pat_let_tv160).Add((_1177_c).dtor_name, _pat_let_tv161);
        }
      }
      if (unmatched55) {
        if (_source55.is_EnumDecl) {
          RAST._IEnum _1178_enum = _source55.dtor_enum;
          unmatched55 = false;
          return (_pat_let_tv162).Add((_1178_enum).dtor_name, _pat_let_tv163);
        }
      }
      if (unmatched55) {
        if (_source55.is_ImplDecl) {
          RAST._IImpl _1179_impl = _source55.dtor_impl;
          unmatched55 = false;
          return FactorPathsOptimization.__default.GatherImplMapping(_1179_impl, _pat_let_tv164);
        }
      }
      if (unmatched55) {
        if (_source55.is_TraitDecl) {
          RAST._ITrait _1180_tr = _source55.dtor_tr;
          unmatched55 = false;
          return _pat_let_tv165;
        }
      }
      if (unmatched55) {
        if (_source55.is_TopFnDecl) {
          RAST._ITopFnDecl _1181_fn = _source55.dtor_fn;
          unmatched55 = false;
          return (_pat_let_tv166).Add(((_1181_fn).dtor_fn).dtor_name, _pat_let_tv167);
        }
      }
      if (unmatched55) {
        RAST._IUse _1182_use = _source55.dtor_use;
        unmatched55 = false;
        return _pat_let_tv168;
      }
      throw new System.Exception("unexpected control point");
    }
    public static FactorPathsOptimization._IMapping GatherTypeMapping(RAST._IType tpe, FactorPathsOptimization._IMapping current)
    {
      return (tpe).Fold<FactorPathsOptimization._IMapping>(current, ((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_1183_current, _1184_t) => {
        return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
          RAST._IType _source56 = _1184_t;
          bool unmatched56 = true;
          if (unmatched56) {
            if (_source56.is_TypeFromPath) {
              RAST._IPath path4 = _source56.dtor_path;
              if (path4.is_PMemberSelect) {
                RAST._IPath _1185_base = path4.dtor_base;
                Dafny.ISequence<Dafny.Rune> _1186_name = path4.dtor_name;
                unmatched56 = false;
                return (_1183_current).Add(_1186_name, _1185_base);
              }
            }
          }
          if (unmatched56) {
            unmatched56 = false;
            return _1183_current;
          }
          throw new System.Exception("unexpected control point");
        }))();
      })));
    }
    public static FactorPathsOptimization._IMapping GatherImplMapping(RAST._IImpl impl, FactorPathsOptimization._IMapping current)
    {
      var _pat_let_tv169 = current;
      var _pat_let_tv170 = current;
      RAST._IImpl _source57 = impl;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1187_typeParams = _source57.dtor_typeParams;
          RAST._IType _1188_tpe = _source57.dtor_tpe;
          RAST._IType _1189_forType = _source57.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1190_where = _source57.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1191_body = _source57.dtor_body;
          unmatched57 = false;
          return FactorPathsOptimization.__default.GatherTypeMapping(_1189_forType, FactorPathsOptimization.__default.GatherTypeMapping(_1188_tpe, _pat_let_tv169));
        }
      }
      if (unmatched57) {
        Dafny.ISequence<RAST._ITypeParamDecl> _1192_typeParams = _source57.dtor_typeParams;
        RAST._IType _1193_tpe = _source57.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1194_where = _source57.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1195_body = _source57.dtor_body;
        unmatched57 = false;
        return FactorPathsOptimization.__default.GatherTypeMapping(_1193_tpe, _pat_let_tv170);
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv171 = modDecl;
      var _pat_let_tv172 = replacement;
      var _pat_let_tv173 = modDecl;
      var _pat_let_tv174 = modDecl;
      var _pat_let_tv175 = modDecl;
      var _pat_let_tv176 = replacement;
      var _pat_let_tv177 = modDecl;
      var _pat_let_tv178 = modDecl;
      var _pat_let_tv179 = modDecl;
      RAST._IModDecl _source58 = modDecl;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_ModDecl) {
          RAST._IMod _1196_mod = _source58.dtor_mod;
          unmatched58 = false;
          return _pat_let_tv171;
        }
      }
      if (unmatched58) {
        if (_source58.is_StructDecl) {
          RAST._IStruct _1197_struct = _source58.dtor_struct;
          unmatched58 = false;
          return RAST.ModDecl.create_StructDecl(FactorPathsOptimization.__default.ReplaceStruct(_1197_struct, _pat_let_tv172));
        }
      }
      if (unmatched58) {
        if (_source58.is_TypeDecl) {
          RAST._ITypeSynonym _1198_tpe = _source58.dtor_tpe;
          unmatched58 = false;
          return _pat_let_tv173;
        }
      }
      if (unmatched58) {
        if (_source58.is_ConstDecl) {
          RAST._IConstant _1199_c = _source58.dtor_c;
          unmatched58 = false;
          return _pat_let_tv174;
        }
      }
      if (unmatched58) {
        if (_source58.is_EnumDecl) {
          RAST._IEnum _1200_enum = _source58.dtor_enum;
          unmatched58 = false;
          return _pat_let_tv175;
        }
      }
      if (unmatched58) {
        if (_source58.is_ImplDecl) {
          RAST._IImpl _1201_impl = _source58.dtor_impl;
          unmatched58 = false;
          return RAST.ModDecl.create_ImplDecl(FactorPathsOptimization.__default.ReplaceImplDecl(_1201_impl, _pat_let_tv176));
        }
      }
      if (unmatched58) {
        if (_source58.is_TraitDecl) {
          RAST._ITrait _1202_tr = _source58.dtor_tr;
          unmatched58 = false;
          return _pat_let_tv177;
        }
      }
      if (unmatched58) {
        if (_source58.is_TopFnDecl) {
          RAST._ITopFnDecl _1203_fn = _source58.dtor_fn;
          unmatched58 = false;
          return _pat_let_tv178;
        }
      }
      if (unmatched58) {
        RAST._IUse _1204_use = _source58.dtor_use;
        unmatched58 = false;
        return _pat_let_tv179;
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IType ReplaceType(RAST._IType t, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv180 = replacement;
      var _pat_let_tv181 = replacement;
      var _pat_let_tv182 = t;
      var _pat_let_tv183 = t;
      var _pat_let_tv184 = t;
      RAST._IType _source59 = t;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_TypeFromPath) {
          RAST._IPath path5 = _source59.dtor_path;
          if (path5.is_PMemberSelect) {
            RAST._IPath _1205_base = path5.dtor_base;
            Dafny.ISequence<Dafny.Rune> _1206_id = path5.dtor_name;
            unmatched59 = false;
            if (((_pat_let_tv180).Contains(_1206_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_pat_let_tv181,_1206_id), _1205_base))) {
              return RAST.Type.create_TSynonym(RAST.Type.create_TIdentifier(_1206_id), _pat_let_tv182);
            } else {
              return _pat_let_tv183;
            }
          }
        }
      }
      if (unmatched59) {
        unmatched59 = false;
        return _pat_let_tv184;
      }
      throw new System.Exception("unexpected control point");
    }
    public static Dafny.ISequence<RAST._ITypeParamDecl> ReplaceTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      return Std.Collections.Seq.__default.Map<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>>>((_1207_replacement) => ((System.Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>)((_1208_t) => {
        return Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1208_t, _pat_let10_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let10_0, _1209_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1210_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1211_constraint) => {
          return FactorPathsOptimization.__default.ReplaceType(_1211_constraint, _1210_replacement);
        })))(_1207_replacement), (_1208_t).dtor_constraints), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let11_0, _1212_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1209_dt__update__tmp_h0).dtor_content, _1212_dt__update_hconstraints_h0)))));
      })))(replacement), typeParams);
    }
    public static RAST._IImpl ReplaceImplDecl(RAST._IImpl impl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv185 = replacement;
      var _pat_let_tv186 = replacement;
      var _pat_let_tv187 = replacement;
      var _pat_let_tv188 = replacement;
      var _pat_let_tv189 = replacement;
      RAST._IImpl _source60 = impl;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1213_typeParams = _source60.dtor_typeParams;
          RAST._IType _1214_tpe = _source60.dtor_tpe;
          RAST._IType _1215_forType = _source60.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1216_where = _source60.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1217_body = _source60.dtor_body;
          unmatched60 = false;
          return RAST.Impl.create_ImplFor(FactorPathsOptimization.__default.ReplaceTypeParams(_1213_typeParams, _pat_let_tv185), (_1214_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv186)), (_1215_forType).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv187)), _1216_where, _1217_body);
        }
      }
      if (unmatched60) {
        Dafny.ISequence<RAST._ITypeParamDecl> _1218_typeParams = _source60.dtor_typeParams;
        RAST._IType _1219_tpe = _source60.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1220_where = _source60.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1221_body = _source60.dtor_body;
        unmatched60 = false;
        return RAST.Impl.create_Impl(FactorPathsOptimization.__default.ReplaceTypeParams(_1218_typeParams, _pat_let_tv188), (_1219_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv189)), _1220_where, _1221_body);
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IStruct ReplaceStruct(RAST._IStruct @struct, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv190 = replacement;
      var _pat_let_tv191 = replacement;
      RAST._IStruct _source61 = @struct;
      bool unmatched61 = true;
      if (unmatched61) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1222_attributes = _source61.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _1223_name = _source61.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _1224_typeParams = _source61.dtor_typeParams;
        RAST._IFields _1225_fields = _source61.dtor_fields;
        unmatched61 = false;
        return RAST.Struct.create(_1222_attributes, _1223_name, FactorPathsOptimization.__default.ReplaceTypeParams(_1224_typeParams, _pat_let_tv190), FactorPathsOptimization.__default.ReplaceFields(_1225_fields, _pat_let_tv191));
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IFields ReplaceFields(RAST._IFields fields, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv192 = replacement;
      var _pat_let_tv193 = replacement;
      RAST._IFields _source62 = fields;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _1226_sFields = _source62.dtor_fields;
          unmatched62 = false;
          return RAST.Fields.create_NamedFields(Std.Collections.Seq.__default.Map<RAST._IField, RAST._IField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IField, RAST._IField>>>((_1227_replacement) => ((System.Func<RAST._IField, RAST._IField>)((_1228_f) => {
  return Dafny.Helpers.Let<RAST._IField, RAST._IField>(_1228_f, _pat_let12_0 => Dafny.Helpers.Let<RAST._IField, RAST._IField>(_pat_let12_0, _1229_dt__update__tmp_h0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>((_1228_f).dtor_formal, _pat_let14_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>(_pat_let14_0, _1230_dt__update__tmp_h1 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(FactorPathsOptimization.__default.ReplaceType(((_1228_f).dtor_formal).dtor_tpe, _1227_replacement), _pat_let15_0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(_pat_let15_0, _1231_dt__update_htpe_h0 => RAST.Formal.create((_1230_dt__update__tmp_h1).dtor_name, _1231_dt__update_htpe_h0))))), _pat_let13_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(_pat_let13_0, _1232_dt__update_hformal_h0 => RAST.Field.create((_1229_dt__update__tmp_h0).dtor_visibility, _1232_dt__update_hformal_h0)))));
})))(_pat_let_tv192), _1226_sFields));
        }
      }
      if (unmatched62) {
        Dafny.ISequence<RAST._INamelessField> _1233_sFields = _source62.dtor_types;
        unmatched62 = false;
        return RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._INamelessField, RAST._INamelessField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._INamelessField, RAST._INamelessField>>>((_1234_replacement) => ((System.Func<RAST._INamelessField, RAST._INamelessField>)((_1235_f) => {
  return Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_1235_f, _pat_let16_0 => Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_pat_let16_0, _1236_dt__update__tmp_h2 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(FactorPathsOptimization.__default.ReplaceType((_1235_f).dtor_tpe, _1234_replacement), _pat_let17_0 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(_pat_let17_0, _1237_dt__update_htpe_h1 => RAST.NamelessField.create((_1236_dt__update__tmp_h2).dtor_visibility, _1237_dt__update_htpe_h1)))));
})))(_pat_let_tv193), _1233_sFields));
      }
      throw new System.Exception("unexpected control point");
    }
    public static Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>> typeReplacer { get {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>)((_1238_replacement) => {
        return Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1239_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1240_t) => {
          return FactorPathsOptimization.__default.ReplaceType(_1240_t, _1239_replacement);
        })))(_1238_replacement);
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
        FactorPathsOptimization._IMapping _1241_dt__update__tmp_h0 = this;
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1242_dt__update_hprovenance_h0 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.Union(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,k), Dafny.Set<RAST._IPath>.FromElements(path)));
        return FactorPathsOptimization.Mapping.create(_1242_dt__update_hprovenance_h0, (_1241_dt__update__tmp_h0).dtor_keys);
      } else {
        FactorPathsOptimization._IMapping _1243_dt__update__tmp_h1 = this;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1244_dt__update_hkeys_h0 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_keys, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(k));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1245_dt__update_hprovenance_h1 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.FromElements(path));
        return FactorPathsOptimization.Mapping.create(_1245_dt__update_hprovenance_h1, _1244_dt__update_hkeys_h0);
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement() {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_provenance).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1246_identifier = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_provenance).Contains(_1246_identifier)) {
            foreach (Dafny.ISet<RAST._IPath> _compr_7 in Dafny.Helpers.SingleValue<Dafny.ISet<RAST._IPath>>(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1246_identifier))) {
              Dafny.ISet<RAST._IPath> _1247_paths = (Dafny.ISet<RAST._IPath>)_compr_7;
              if (((_1247_paths).Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1246_identifier))) && (((new BigInteger((_1247_paths).Count)) == (BigInteger.One)) || (Dafny.Helpers.Id<Func<Dafny.ISet<RAST._IPath>, bool>>((_1248_paths) => Dafny.Helpers.Quantifier<RAST._IPath>(Dafny.Helpers.SingleValue<RAST._IPath>(RAST.__default.dafny__runtime), false, (((_exists_var_1) => {
                RAST._IPath _1249_p = (RAST._IPath)_exists_var_1;
                return ((_1248_paths).Contains(_1249_p)) && (object.Equals(_1249_p, RAST.__default.dafny__runtime));
              }))))(_1247_paths)))) {
                _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>(_1246_identifier, (((new BigInteger((_1247_paths).Count)) == (BigInteger.One)) ? (FactorPathsOptimization.__default.UniqueElementOf<RAST._IPath>(_1247_paths)) : (RAST.__default.dafny__runtime))));
              }
            }
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IPath>.FromCollection(_coll6);
      }))();
    }
    public Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1250_toUse = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IPath, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1251_finalReplacement, _1252_SelfPath) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_1253_key) => {
        return ((_1251_finalReplacement).Contains(_1253_key)) && (!object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_1251_finalReplacement,_1253_key), _1252_SelfPath));
      })))(finalReplacement, SelfPath), (this).dtor_keys);
      return ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
        BigInteger dim12 = new BigInteger((_1250_toUse).Count);
        var arr12 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
        for (int i12 = 0; i12 < dim12; i12++) {
          var _1254_i = (BigInteger) i12;
          arr12[(int)(_1254_i)] = RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PRIV(), (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(finalReplacement,(_1250_toUse).Select(_1254_i))).MSel((_1250_toUse).Select(_1254_i))));
        }
        return Dafny.Sequence<RAST._IModDecl>.FromArray(arr12);
      }))();
    }
  }
} // end of namespace FactorPathsOptimization