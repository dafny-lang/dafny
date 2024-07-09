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
        Dafny.ISequence<RAST._IModDecl> _1166_rewrittenDeclarations = (mod).Fold<Dafny.ISequence<RAST._IModDecl>>(Dafny.Sequence<RAST._IModDecl>.FromElements(), Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IMod, Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>>>((_1167_pathsToRemove, _1168_mod) => ((System.Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>)((_1169_current, _1170_modDecl) => {
          return Dafny.Sequence<RAST._IModDecl>.Concat(_1169_current, Dafny.Sequence<RAST._IModDecl>.FromElements(FactorPathsOptimization.__default.ReplaceModDecl(_1170_modDecl, _1167_pathsToRemove)));
        })))(_1164_pathsToRemove, mod));
        Dafny.ISequence<RAST._IModDecl> _1171_newBody = Dafny.Sequence<RAST._IModDecl>.Concat(_1165_imports, _1166_rewrittenDeclarations);
        RAST._IMod _1172_dt__update__tmp_h0 = mod;
        Dafny.ISequence<RAST._IModDecl> _1173_dt__update_hbody_h0 = _1171_newBody;
        return RAST.Mod.create_Mod((_1172_dt__update__tmp_h0).dtor_name, _1173_dt__update_hbody_h0);
      }
    }
    public static __T UniqueElementOf<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_9 =>  {
        __T _1174_e = default(__T);
        foreach (__T _assign_such_that_2 in (s).Elements) {
          _1174_e = (__T)_assign_such_that_2;
          if ((s).Contains(_1174_e)) {
            goto after__ASSIGN_SUCH_THAT_2;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 89)");
      after__ASSIGN_SUCH_THAT_2: ;
        return _1174_e;
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
          RAST._IMod _1175_mod = _source55.dtor_mod;
          unmatched55 = false;
          return (_pat_let_tv154).Add((_1175_mod).dtor_name, _pat_let_tv155);
        }
      }
      if (unmatched55) {
        if (_source55.is_StructDecl) {
          RAST._IStruct _1176_struct = _source55.dtor_struct;
          unmatched55 = false;
          return (_pat_let_tv156).Add((_1176_struct).dtor_name, _pat_let_tv157);
        }
      }
      if (unmatched55) {
        if (_source55.is_TypeDecl) {
          RAST._ITypeSynonym _1177_tpe = _source55.dtor_tpe;
          unmatched55 = false;
          return (_pat_let_tv158).Add((_1177_tpe).dtor_name, _pat_let_tv159);
        }
      }
      if (unmatched55) {
        if (_source55.is_ConstDecl) {
          RAST._IConstant _1178_c = _source55.dtor_c;
          unmatched55 = false;
          return (_pat_let_tv160).Add((_1178_c).dtor_name, _pat_let_tv161);
        }
      }
      if (unmatched55) {
        if (_source55.is_EnumDecl) {
          RAST._IEnum _1179_enum = _source55.dtor_enum;
          unmatched55 = false;
          return (_pat_let_tv162).Add((_1179_enum).dtor_name, _pat_let_tv163);
        }
      }
      if (unmatched55) {
        if (_source55.is_ImplDecl) {
          RAST._IImpl _1180_impl = _source55.dtor_impl;
          unmatched55 = false;
          return FactorPathsOptimization.__default.GatherImplMapping(_1180_impl, _pat_let_tv164);
        }
      }
      if (unmatched55) {
        if (_source55.is_TraitDecl) {
          RAST._ITrait _1181_tr = _source55.dtor_tr;
          unmatched55 = false;
          return _pat_let_tv165;
        }
      }
      if (unmatched55) {
        if (_source55.is_TopFnDecl) {
          RAST._ITopFnDecl _1182_fn = _source55.dtor_fn;
          unmatched55 = false;
          return (_pat_let_tv166).Add(((_1182_fn).dtor_fn).dtor_name, _pat_let_tv167);
        }
      }
      if (unmatched55) {
        RAST._IUse _1183_use = _source55.dtor_use;
        unmatched55 = false;
        return _pat_let_tv168;
      }
      throw new System.Exception("unexpected control point");
    }
    public static FactorPathsOptimization._IMapping GatherTypeMapping(RAST._IType tpe, FactorPathsOptimization._IMapping current)
    {
      return (tpe).Fold<FactorPathsOptimization._IMapping>(current, ((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_1184_current, _1185_t) => {
        return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
          RAST._IType _source56 = _1185_t;
          bool unmatched56 = true;
          if (unmatched56) {
            if (_source56.is_TypeFromPath) {
              RAST._IPath path4 = _source56.dtor_path;
              if (path4.is_PMemberSelect) {
                RAST._IPath _1186_base = path4.dtor_base;
                Dafny.ISequence<Dafny.Rune> _1187_name = path4.dtor_name;
                unmatched56 = false;
                return (_1184_current).Add(_1187_name, _1186_base);
              }
            }
          }
          if (unmatched56) {
            unmatched56 = false;
            return _1184_current;
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
          Dafny.ISequence<RAST._ITypeParamDecl> _1188_typeParams = _source57.dtor_typeParams;
          RAST._IType _1189_tpe = _source57.dtor_tpe;
          RAST._IType _1190_forType = _source57.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1191_where = _source57.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1192_body = _source57.dtor_body;
          unmatched57 = false;
          return FactorPathsOptimization.__default.GatherTypeMapping(_1190_forType, FactorPathsOptimization.__default.GatherTypeMapping(_1189_tpe, _pat_let_tv169));
        }
      }
      if (unmatched57) {
        Dafny.ISequence<RAST._ITypeParamDecl> _1193_typeParams = _source57.dtor_typeParams;
        RAST._IType _1194_tpe = _source57.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1195_where = _source57.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1196_body = _source57.dtor_body;
        unmatched57 = false;
        return FactorPathsOptimization.__default.GatherTypeMapping(_1194_tpe, _pat_let_tv170);
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv171 = replacement;
      var _pat_let_tv172 = modDecl;
      var _pat_let_tv173 = modDecl;
      var _pat_let_tv174 = modDecl;
      var _pat_let_tv175 = replacement;
      var _pat_let_tv176 = modDecl;
      var _pat_let_tv177 = modDecl;
      var _pat_let_tv178 = modDecl;
      RAST._IModDecl _source58 = modDecl;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_ModDecl) {
          RAST._IMod _1197_mod = _source58.dtor_mod;
          unmatched58 = false;
          return RAST.ModDecl.create_ModDecl(FactorPathsOptimization.__default.apply(_1197_mod));
        }
      }
      if (unmatched58) {
        if (_source58.is_StructDecl) {
          RAST._IStruct _1198_struct = _source58.dtor_struct;
          unmatched58 = false;
          return RAST.ModDecl.create_StructDecl(FactorPathsOptimization.__default.ReplaceStruct(_1198_struct, _pat_let_tv171));
        }
      }
      if (unmatched58) {
        if (_source58.is_TypeDecl) {
          RAST._ITypeSynonym _1199_tpe = _source58.dtor_tpe;
          unmatched58 = false;
          return _pat_let_tv172;
        }
      }
      if (unmatched58) {
        if (_source58.is_ConstDecl) {
          RAST._IConstant _1200_c = _source58.dtor_c;
          unmatched58 = false;
          return _pat_let_tv173;
        }
      }
      if (unmatched58) {
        if (_source58.is_EnumDecl) {
          RAST._IEnum _1201_enum = _source58.dtor_enum;
          unmatched58 = false;
          return _pat_let_tv174;
        }
      }
      if (unmatched58) {
        if (_source58.is_ImplDecl) {
          RAST._IImpl _1202_impl = _source58.dtor_impl;
          unmatched58 = false;
          return RAST.ModDecl.create_ImplDecl(FactorPathsOptimization.__default.ReplaceImplDecl(_1202_impl, _pat_let_tv175));
        }
      }
      if (unmatched58) {
        if (_source58.is_TraitDecl) {
          RAST._ITrait _1203_tr = _source58.dtor_tr;
          unmatched58 = false;
          return _pat_let_tv176;
        }
      }
      if (unmatched58) {
        if (_source58.is_TopFnDecl) {
          RAST._ITopFnDecl _1204_fn = _source58.dtor_fn;
          unmatched58 = false;
          return _pat_let_tv177;
        }
      }
      if (unmatched58) {
        RAST._IUse _1205_use = _source58.dtor_use;
        unmatched58 = false;
        return _pat_let_tv178;
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IType ReplaceType(RAST._IType t, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv179 = replacement;
      var _pat_let_tv180 = replacement;
      var _pat_let_tv181 = t;
      var _pat_let_tv182 = t;
      var _pat_let_tv183 = t;
      RAST._IType _source59 = t;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_TypeFromPath) {
          RAST._IPath path5 = _source59.dtor_path;
          if (path5.is_PMemberSelect) {
            RAST._IPath _1206_base = path5.dtor_base;
            Dafny.ISequence<Dafny.Rune> _1207_id = path5.dtor_name;
            unmatched59 = false;
            if (((_pat_let_tv179).Contains(_1207_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_pat_let_tv180,_1207_id), _1206_base))) {
              return RAST.Type.create_TSynonym(RAST.Type.create_TIdentifier(_1207_id), _pat_let_tv181);
            } else {
              return _pat_let_tv182;
            }
          }
        }
      }
      if (unmatched59) {
        unmatched59 = false;
        return _pat_let_tv183;
      }
      throw new System.Exception("unexpected control point");
    }
    public static Dafny.ISequence<RAST._ITypeParamDecl> ReplaceTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      return Std.Collections.Seq.__default.Map<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>>>((_1208_replacement) => ((System.Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>)((_1209_t) => {
        return Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1209_t, _pat_let10_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let10_0, _1210_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1211_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1212_constraint) => {
          return FactorPathsOptimization.__default.ReplaceType(_1212_constraint, _1211_replacement);
        })))(_1208_replacement), (_1209_t).dtor_constraints), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let11_0, _1213_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1210_dt__update__tmp_h0).dtor_content, _1213_dt__update_hconstraints_h0)))));
      })))(replacement), typeParams);
    }
    public static RAST._IImpl ReplaceImplDecl(RAST._IImpl impl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv184 = replacement;
      var _pat_let_tv185 = replacement;
      var _pat_let_tv186 = replacement;
      var _pat_let_tv187 = replacement;
      var _pat_let_tv188 = replacement;
      RAST._IImpl _source60 = impl;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1214_typeParams = _source60.dtor_typeParams;
          RAST._IType _1215_tpe = _source60.dtor_tpe;
          RAST._IType _1216_forType = _source60.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1217_where = _source60.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1218_body = _source60.dtor_body;
          unmatched60 = false;
          return RAST.Impl.create_ImplFor(FactorPathsOptimization.__default.ReplaceTypeParams(_1214_typeParams, _pat_let_tv184), (_1215_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv185)), (_1216_forType).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv186)), _1217_where, _1218_body);
        }
      }
      if (unmatched60) {
        Dafny.ISequence<RAST._ITypeParamDecl> _1219_typeParams = _source60.dtor_typeParams;
        RAST._IType _1220_tpe = _source60.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1221_where = _source60.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1222_body = _source60.dtor_body;
        unmatched60 = false;
        return RAST.Impl.create_Impl(FactorPathsOptimization.__default.ReplaceTypeParams(_1219_typeParams, _pat_let_tv187), (_1220_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(_pat_let_tv188)), _1221_where, _1222_body);
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IStruct ReplaceStruct(RAST._IStruct @struct, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv189 = replacement;
      var _pat_let_tv190 = replacement;
      RAST._IStruct _source61 = @struct;
      bool unmatched61 = true;
      if (unmatched61) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1223_attributes = _source61.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _1224_name = _source61.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _1225_typeParams = _source61.dtor_typeParams;
        RAST._IFields _1226_fields = _source61.dtor_fields;
        unmatched61 = false;
        return RAST.Struct.create(_1223_attributes, _1224_name, FactorPathsOptimization.__default.ReplaceTypeParams(_1225_typeParams, _pat_let_tv189), FactorPathsOptimization.__default.ReplaceFields(_1226_fields, _pat_let_tv190));
      }
      throw new System.Exception("unexpected control point");
    }
    public static RAST._IFields ReplaceFields(RAST._IFields fields, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      var _pat_let_tv191 = replacement;
      var _pat_let_tv192 = replacement;
      RAST._IFields _source62 = fields;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _1227_sFields = _source62.dtor_fields;
          unmatched62 = false;
          return RAST.Fields.create_NamedFields(Std.Collections.Seq.__default.Map<RAST._IField, RAST._IField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IField, RAST._IField>>>((_1228_replacement) => ((System.Func<RAST._IField, RAST._IField>)((_1229_f) => {
  return Dafny.Helpers.Let<RAST._IField, RAST._IField>(_1229_f, _pat_let12_0 => Dafny.Helpers.Let<RAST._IField, RAST._IField>(_pat_let12_0, _1230_dt__update__tmp_h0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>((_1229_f).dtor_formal, _pat_let14_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>(_pat_let14_0, _1231_dt__update__tmp_h1 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(FactorPathsOptimization.__default.ReplaceType(((_1229_f).dtor_formal).dtor_tpe, _1228_replacement), _pat_let15_0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(_pat_let15_0, _1232_dt__update_htpe_h0 => RAST.Formal.create((_1231_dt__update__tmp_h1).dtor_name, _1232_dt__update_htpe_h0))))), _pat_let13_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(_pat_let13_0, _1233_dt__update_hformal_h0 => RAST.Field.create((_1230_dt__update__tmp_h0).dtor_visibility, _1233_dt__update_hformal_h0)))));
})))(_pat_let_tv191), _1227_sFields));
        }
      }
      if (unmatched62) {
        Dafny.ISequence<RAST._INamelessField> _1234_sFields = _source62.dtor_types;
        unmatched62 = false;
        return RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._INamelessField, RAST._INamelessField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._INamelessField, RAST._INamelessField>>>((_1235_replacement) => ((System.Func<RAST._INamelessField, RAST._INamelessField>)((_1236_f) => {
  return Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_1236_f, _pat_let16_0 => Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_pat_let16_0, _1237_dt__update__tmp_h2 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(FactorPathsOptimization.__default.ReplaceType((_1236_f).dtor_tpe, _1235_replacement), _pat_let17_0 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(_pat_let17_0, _1238_dt__update_htpe_h1 => RAST.NamelessField.create((_1237_dt__update__tmp_h2).dtor_visibility, _1238_dt__update_htpe_h1)))));
})))(_pat_let_tv192), _1234_sFields));
      }
      throw new System.Exception("unexpected control point");
    }
    public static Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>> typeReplacer { get {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>)((_1239_replacement) => {
        return Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1240_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1241_t) => {
          return FactorPathsOptimization.__default.ReplaceType(_1241_t, _1240_replacement);
        })))(_1239_replacement);
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
        FactorPathsOptimization._IMapping _1242_dt__update__tmp_h0 = this;
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1243_dt__update_hprovenance_h0 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.Union(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,k), Dafny.Set<RAST._IPath>.FromElements(path)));
        return FactorPathsOptimization.Mapping.create(_1243_dt__update_hprovenance_h0, (_1242_dt__update__tmp_h0).dtor_keys);
      } else {
        FactorPathsOptimization._IMapping _1244_dt__update__tmp_h1 = this;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1245_dt__update_hkeys_h0 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_keys, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(k));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1246_dt__update_hprovenance_h1 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.FromElements(path));
        return FactorPathsOptimization.Mapping.create(_1246_dt__update_hprovenance_h1, _1245_dt__update_hkeys_h0);
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement() {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_provenance).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1247_identifier = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_provenance).Contains(_1247_identifier)) {
            foreach (Dafny.ISet<RAST._IPath> _compr_7 in Dafny.Helpers.SingleValue<Dafny.ISet<RAST._IPath>>(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1247_identifier))) {
              Dafny.ISet<RAST._IPath> _1248_paths = (Dafny.ISet<RAST._IPath>)_compr_7;
              if (((_1248_paths).Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1247_identifier))) && (((new BigInteger((_1248_paths).Count)) == (BigInteger.One)) || (Dafny.Helpers.Id<Func<Dafny.ISet<RAST._IPath>, bool>>((_1249_paths) => Dafny.Helpers.Quantifier<RAST._IPath>(Dafny.Helpers.SingleValue<RAST._IPath>(RAST.__default.dafny__runtime), false, (((_exists_var_1) => {
                RAST._IPath _1250_p = (RAST._IPath)_exists_var_1;
                return ((_1249_paths).Contains(_1250_p)) && (object.Equals(_1250_p, RAST.__default.dafny__runtime));
              }))))(_1248_paths)))) {
                _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>(_1247_identifier, (((new BigInteger((_1248_paths).Count)) == (BigInteger.One)) ? (FactorPathsOptimization.__default.UniqueElementOf<RAST._IPath>(_1248_paths)) : (RAST.__default.dafny__runtime))));
              }
            }
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IPath>.FromCollection(_coll6);
      }))();
    }
    public Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1251_toUse = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IPath, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1252_finalReplacement, _1253_SelfPath) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_1254_key) => {
        return ((_1252_finalReplacement).Contains(_1254_key)) && (!object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_1252_finalReplacement,_1254_key), _1253_SelfPath));
      })))(finalReplacement, SelfPath), (this).dtor_keys);
      return ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
        BigInteger dim12 = new BigInteger((_1251_toUse).Count);
        var arr12 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
        for (int i12 = 0; i12 < dim12; i12++) {
          var _1255_i = (BigInteger) i12;
          arr12[(int)(_1255_i)] = RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(finalReplacement,(_1251_toUse).Select(_1255_i))).MSel((_1251_toUse).Select(_1255_i))));
        }
        return Dafny.Sequence<RAST._IModDecl>.FromArray(arr12);
      }))();
    }
  }
} // end of namespace FactorPathsOptimization