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
        RAST._IPath _1148_SelfPath = (RAST.__default.crate).MSel((mod).dtor_name);
        FactorPathsOptimization._IMapping _1149_initialMapping = FactorPathsOptimization.Mapping.create(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.FromElements(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        FactorPathsOptimization._IMapping _1150_mappings = (mod).Fold<FactorPathsOptimization._IMapping>(_1149_initialMapping, Dafny.Helpers.Id<Func<RAST._IPath, Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>>>((_1151_SelfPath) => ((System.Func<FactorPathsOptimization._IMapping, RAST._IModDecl, FactorPathsOptimization._IMapping>)((_1152_current, _1153_modDecl) => {
          return FactorPathsOptimization.__default.GatherModMapping(_1151_SelfPath, _1153_modDecl, _1152_current);
        })))(_1148_SelfPath));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> _1154_pathsToRemove = (_1150_mappings).ToFinalReplacement();
        Dafny.ISequence<RAST._IModDecl> _1155_imports = (_1150_mappings).ToUseStatements(_1154_pathsToRemove, _1148_SelfPath);
        Dafny.ISequence<RAST._IModDecl> _1156_rewrittenDeclarations = (mod).Fold<Dafny.ISequence<RAST._IModDecl>>(Dafny.Sequence<RAST._IModDecl>.FromElements(), Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IMod, Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>>>((_1157_pathsToRemove, _1158_mod) => ((System.Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>)((_1159_current, _1160_modDecl) => {
          return Dafny.Sequence<RAST._IModDecl>.Concat(_1159_current, Dafny.Sequence<RAST._IModDecl>.FromElements(FactorPathsOptimization.__default.ReplaceModDecl(_1160_modDecl, _1157_pathsToRemove)));
        })))(_1154_pathsToRemove, mod));
        Dafny.ISequence<RAST._IModDecl> _1161_newBody = Dafny.Sequence<RAST._IModDecl>.Concat(_1155_imports, _1156_rewrittenDeclarations);
        RAST._IMod _1162_dt__update__tmp_h0 = mod;
        Dafny.ISequence<RAST._IModDecl> _1163_dt__update_hbody_h0 = _1161_newBody;
        return RAST.Mod.create_Mod((_1162_dt__update__tmp_h0).dtor_name, _1163_dt__update_hbody_h0);
      }
    }
    public static __T UniqueElementOf<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_9 =>  {
        __T _1164_e = default(__T);
        foreach (__T _assign_such_that_2 in (s).Elements) {
          _1164_e = (__T)_assign_such_that_2;
          if ((s).Contains(_1164_e)) {
            goto after__ASSIGN_SUCH_THAT_2;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 89)");
      after__ASSIGN_SUCH_THAT_2: ;
        return _1164_e;
      }
      );
    }
    public static FactorPathsOptimization._IMapping GatherModMapping(RAST._IPath prefix, RAST._IModDecl modDecl, FactorPathsOptimization._IMapping current)
    {
      RAST._IModDecl _source57 = modDecl;
      {
        if (_source57.is_ModDecl) {
          RAST._IMod _1165_mod = _source57.dtor_mod;
          return (current).Add((_1165_mod).dtor_name, prefix);
        }
      }
      {
        if (_source57.is_StructDecl) {
          RAST._IStruct _1166_struct = _source57.dtor_struct;
          return (current).Add((_1166_struct).dtor_name, prefix);
        }
      }
      {
        if (_source57.is_TypeDecl) {
          RAST._ITypeSynonym _1167_tpe = _source57.dtor_tpe;
          return (current).Add((_1167_tpe).dtor_name, prefix);
        }
      }
      {
        if (_source57.is_ConstDecl) {
          RAST._IConstant _1168_c = _source57.dtor_c;
          return (current).Add((_1168_c).dtor_name, prefix);
        }
      }
      {
        if (_source57.is_EnumDecl) {
          RAST._IEnum _1169_enum = _source57.dtor_enum;
          return (current).Add((_1169_enum).dtor_name, prefix);
        }
      }
      {
        if (_source57.is_ImplDecl) {
          RAST._IImpl _1170_impl = _source57.dtor_impl;
          return FactorPathsOptimization.__default.GatherImplMapping(_1170_impl, current);
        }
      }
      {
        if (_source57.is_TraitDecl) {
          RAST._ITrait _1171_tr = _source57.dtor_tr;
          return current;
        }
      }
      {
        if (_source57.is_TopFnDecl) {
          RAST._ITopFnDecl _1172_fn = _source57.dtor_fn;
          return (current).Add(((_1172_fn).dtor_fn).dtor_name, prefix);
        }
      }
      {
        RAST._IUse _1173_use = _source57.dtor_use;
        return current;
      }
    }
    public static FactorPathsOptimization._IMapping GatherTypeMapping(RAST._IType tpe, FactorPathsOptimization._IMapping current)
    {
      return (tpe).Fold<FactorPathsOptimization._IMapping>(current, ((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_1174_current, _1175_t) => {
        return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
          RAST._IType _source58 = _1175_t;
          {
            if (_source58.is_TypeFromPath) {
              RAST._IPath path4 = _source58.dtor_path;
              if (path4.is_PMemberSelect) {
                RAST._IPath _1176_base = path4.dtor_base;
                Dafny.ISequence<Dafny.Rune> _1177_name = path4.dtor_name;
                return (_1174_current).Add(_1177_name, _1176_base);
              }
            }
          }
          {
            return _1174_current;
          }
        }))();
      })));
    }
    public static FactorPathsOptimization._IMapping GatherImplMapping(RAST._IImpl impl, FactorPathsOptimization._IMapping current)
    {
      RAST._IImpl _source59 = impl;
      {
        if (_source59.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1178_typeParams = _source59.dtor_typeParams;
          RAST._IType _1179_tpe = _source59.dtor_tpe;
          RAST._IType _1180_forType = _source59.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1181_where = _source59.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1182_body = _source59.dtor_body;
          return FactorPathsOptimization.__default.GatherTypeMapping(_1180_forType, FactorPathsOptimization.__default.GatherTypeMapping(_1179_tpe, current));
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _1183_typeParams = _source59.dtor_typeParams;
        RAST._IType _1184_tpe = _source59.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1185_where = _source59.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1186_body = _source59.dtor_body;
        return FactorPathsOptimization.__default.GatherTypeMapping(_1184_tpe, current);
      }
    }
    public static RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IModDecl _source60 = modDecl;
      {
        if (_source60.is_ModDecl) {
          RAST._IMod _1187_mod = _source60.dtor_mod;
          return RAST.ModDecl.create_ModDecl(FactorPathsOptimization.__default.apply(_1187_mod));
        }
      }
      {
        if (_source60.is_StructDecl) {
          RAST._IStruct _1188_struct = _source60.dtor_struct;
          return RAST.ModDecl.create_StructDecl(FactorPathsOptimization.__default.ReplaceStruct(_1188_struct, replacement));
        }
      }
      {
        if (_source60.is_TypeDecl) {
          RAST._ITypeSynonym _1189_tpe = _source60.dtor_tpe;
          return modDecl;
        }
      }
      {
        if (_source60.is_ConstDecl) {
          RAST._IConstant _1190_c = _source60.dtor_c;
          return modDecl;
        }
      }
      {
        if (_source60.is_EnumDecl) {
          RAST._IEnum _1191_enum = _source60.dtor_enum;
          return modDecl;
        }
      }
      {
        if (_source60.is_ImplDecl) {
          RAST._IImpl _1192_impl = _source60.dtor_impl;
          return RAST.ModDecl.create_ImplDecl(FactorPathsOptimization.__default.ReplaceImplDecl(_1192_impl, replacement));
        }
      }
      {
        if (_source60.is_TraitDecl) {
          RAST._ITrait _1193_tr = _source60.dtor_tr;
          return modDecl;
        }
      }
      {
        if (_source60.is_TopFnDecl) {
          RAST._ITopFnDecl _1194_fn = _source60.dtor_fn;
          return modDecl;
        }
      }
      {
        RAST._IUse _1195_use = _source60.dtor_use;
        return modDecl;
      }
    }
    public static RAST._IType ReplaceType(RAST._IType t, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IType _source61 = t;
      {
        if (_source61.is_TypeFromPath) {
          RAST._IPath path5 = _source61.dtor_path;
          if (path5.is_PMemberSelect) {
            RAST._IPath _1196_base = path5.dtor_base;
            Dafny.ISequence<Dafny.Rune> _1197_id = path5.dtor_name;
            if (((replacement).Contains(_1197_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(replacement,_1197_id), _1196_base))) {
              return RAST.Type.create_TSynonym(RAST.Type.create_TIdentifier(_1197_id), t);
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
      return Std.Collections.Seq.__default.Map<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>>>((_1198_replacement) => ((System.Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>)((_1199_t) => {
        return Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1199_t, _pat_let10_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let10_0, _1200_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1201_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1202_constraint) => {
          return FactorPathsOptimization.__default.ReplaceType(_1202_constraint, _1201_replacement);
        })))(_1198_replacement), (_1199_t).dtor_constraints), _pat_let11_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let11_0, _1203_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1200_dt__update__tmp_h0).dtor_name, _1203_dt__update_hconstraints_h0)))));
      })))(replacement), typeParams);
    }
    public static RAST._IImpl ReplaceImplDecl(RAST._IImpl impl, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IImpl _source62 = impl;
      {
        if (_source62.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _1204_typeParams = _source62.dtor_typeParams;
          RAST._IType _1205_tpe = _source62.dtor_tpe;
          RAST._IType _1206_forType = _source62.dtor_forType;
          Dafny.ISequence<Dafny.Rune> _1207_where = _source62.dtor_where;
          Dafny.ISequence<RAST._IImplMember> _1208_body = _source62.dtor_body;
          return RAST.Impl.create_ImplFor(FactorPathsOptimization.__default.ReplaceTypeParams(_1204_typeParams, replacement), (_1205_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), (_1206_forType).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), _1207_where, _1208_body);
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _1209_typeParams = _source62.dtor_typeParams;
        RAST._IType _1210_tpe = _source62.dtor_tpe;
        Dafny.ISequence<Dafny.Rune> _1211_where = _source62.dtor_where;
        Dafny.ISequence<RAST._IImplMember> _1212_body = _source62.dtor_body;
        return RAST.Impl.create_Impl(FactorPathsOptimization.__default.ReplaceTypeParams(_1209_typeParams, replacement), (_1210_tpe).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>(FactorPathsOptimization.__default.typeReplacer)(replacement)), _1211_where, _1212_body);
      }
    }
    public static RAST._IStruct ReplaceStruct(RAST._IStruct @struct, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IStruct _source63 = @struct;
      {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1213_attributes = _source63.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _1214_name = _source63.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _1215_typeParams = _source63.dtor_typeParams;
        RAST._IFields _1216_fields = _source63.dtor_fields;
        return RAST.Struct.create(_1213_attributes, _1214_name, FactorPathsOptimization.__default.ReplaceTypeParams(_1215_typeParams, replacement), FactorPathsOptimization.__default.ReplaceFields(_1216_fields, replacement));
      }
    }
    public static RAST._IFields ReplaceFields(RAST._IFields fields, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      RAST._IFields _source64 = fields;
      {
        if (_source64.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _1217_sFields = _source64.dtor_fields;
          return RAST.Fields.create_NamedFields(Std.Collections.Seq.__default.Map<RAST._IField, RAST._IField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IField, RAST._IField>>>((_1218_replacement) => ((System.Func<RAST._IField, RAST._IField>)((_1219_f) => {
  return Dafny.Helpers.Let<RAST._IField, RAST._IField>(_1219_f, _pat_let12_0 => Dafny.Helpers.Let<RAST._IField, RAST._IField>(_pat_let12_0, _1220_dt__update__tmp_h0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>((_1219_f).dtor_formal, _pat_let14_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>(_pat_let14_0, _1221_dt__update__tmp_h1 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(FactorPathsOptimization.__default.ReplaceType(((_1219_f).dtor_formal).dtor_tpe, _1218_replacement), _pat_let15_0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(_pat_let15_0, _1222_dt__update_htpe_h0 => RAST.Formal.create((_1221_dt__update__tmp_h1).dtor_name, _1222_dt__update_htpe_h0))))), _pat_let13_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(_pat_let13_0, _1223_dt__update_hformal_h0 => RAST.Field.create((_1220_dt__update__tmp_h0).dtor_visibility, _1223_dt__update_hformal_h0)))));
})))(replacement), _1217_sFields));
        }
      }
      {
        Dafny.ISequence<RAST._INamelessField> _1224_sFields = _source64.dtor_types;
        return RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._INamelessField, RAST._INamelessField>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._INamelessField, RAST._INamelessField>>>((_1225_replacement) => ((System.Func<RAST._INamelessField, RAST._INamelessField>)((_1226_f) => {
  return Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_1226_f, _pat_let16_0 => Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_pat_let16_0, _1227_dt__update__tmp_h2 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(FactorPathsOptimization.__default.ReplaceType((_1226_f).dtor_tpe, _1225_replacement), _pat_let17_0 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(_pat_let17_0, _1228_dt__update_htpe_h1 => RAST.NamelessField.create((_1227_dt__update__tmp_h2).dtor_visibility, _1228_dt__update_htpe_h1)))));
})))(replacement), _1224_sFields));
      }
    }
    public static Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>> typeReplacer { get {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>)((_1229_replacement) => {
        return Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_1230_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_1231_t) => {
          return FactorPathsOptimization.__default.ReplaceType(_1231_t, _1230_replacement);
        })))(_1229_replacement);
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
        FactorPathsOptimization._IMapping _1232_dt__update__tmp_h0 = this;
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1233_dt__update_hprovenance_h0 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.Union(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,k), Dafny.Set<RAST._IPath>.FromElements(path)));
        return FactorPathsOptimization.Mapping.create(_1233_dt__update_hprovenance_h0, (_1232_dt__update__tmp_h0).dtor_keys);
      } else {
        FactorPathsOptimization._IMapping _1234_dt__update__tmp_h1 = this;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1235_dt__update_hkeys_h0 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_keys, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(k));
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> _1236_dt__update_hprovenance_h1 = Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Update((this).dtor_provenance, k, Dafny.Set<RAST._IPath>.FromElements(path));
        return FactorPathsOptimization.Mapping.create(_1236_dt__update_hprovenance_h1, _1235_dt__update_hkeys_h0);
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement() {
      return ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_provenance).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1237_identifier = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_provenance).Contains(_1237_identifier)) {
            foreach (Dafny.ISet<RAST._IPath> _compr_7 in Dafny.Helpers.SingleValue<Dafny.ISet<RAST._IPath>>(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1237_identifier))) {
              Dafny.ISet<RAST._IPath> _1238_paths = (Dafny.ISet<RAST._IPath>)_compr_7;
              if (((_1238_paths).Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1237_identifier))) && (((new BigInteger((_1238_paths).Count)) == (BigInteger.One)) || (Dafny.Helpers.Id<Func<Dafny.ISet<RAST._IPath>, bool>>((_1239_paths) => Dafny.Helpers.Quantifier<RAST._IPath>(Dafny.Helpers.SingleValue<RAST._IPath>(RAST.__default.dafny__runtime), false, (((_exists_var_1) => {
                RAST._IPath _1240_p = (RAST._IPath)_exists_var_1;
                return ((_1239_paths).Contains(_1240_p)) && (object.Equals(_1240_p, RAST.__default.dafny__runtime));
              }))))(_1238_paths)))) {
                _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>(_1237_identifier, (((new BigInteger((_1238_paths).Count)) == (BigInteger.One)) ? (FactorPathsOptimization.__default.UniqueElementOf<RAST._IPath>(_1238_paths)) : (RAST.__default.dafny__runtime))));
              }
            }
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IPath>.FromCollection(_coll6);
      }))();
    }
    public Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1241_toUse = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IPath, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1242_finalReplacement, _1243_SelfPath) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_1244_key) => {
        return ((_1242_finalReplacement).Contains(_1244_key)) && (!object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_1242_finalReplacement,_1244_key), _1243_SelfPath));
      })))(finalReplacement, SelfPath), (this).dtor_keys);
      return ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
        BigInteger dim12 = new BigInteger((_1241_toUse).Count);
        var arr12 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
        for (int i12 = 0; i12 < dim12; i12++) {
          var _1245_i = (BigInteger) i12;
          arr12[(int)(_1245_i)] = RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(finalReplacement,(_1241_toUse).Select(_1245_i))).MSel((_1241_toUse).Select(_1245_i))));
        }
        return Dafny.Sequence<RAST._IModDecl>.FromArray(arr12);
      }))();
    }
  }
} // end of namespace FactorPathsOptimization