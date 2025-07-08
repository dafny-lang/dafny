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

namespace FactorPathsOptimization {

  public partial class __default {
    public static Func<RAST._IMod, RAST._IMod> apply(RAST._IPath root) {
      return Dafny.Helpers.Id<Func<RAST._IPath, Func<RAST._IMod, RAST._IMod>>>((_0_root) => ((System.Func<RAST._IMod, RAST._IMod>)((_1_mod) => {
        return FactorPathsOptimization.__default.applyPrefix(_1_mod, (_0_root).MSel((_1_mod).dtor_name));
      })))(root);
    }
    public static RAST._IMod applyPrefix(RAST._IMod mod, RAST._IPath SelfPath)
    {
      if ((mod).is_ExternMod) {
        return mod;
      } else {
        FactorPathsOptimization._IMapping _0_mappings = (FactorPathsOptimization.__default.PathsVisitor()).VisitMod(FactorPathsOptimization.Mapping.create(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.FromElements(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()), mod, SelfPath);
        Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> _1_pathsToRemove = (_0_mappings).ToFinalReplacement(SelfPath);
        Dafny.ISequence<RAST._IModDecl> _2_imports = (_0_mappings).ToUseStatements(_1_pathsToRemove, SelfPath);
        RAST._IMod _3_mod = (FactorPathsOptimization.__default.PathSimplifier(_1_pathsToRemove)).ReplaceMod(mod, SelfPath);
        RAST._IMod _4_dt__update__tmp_h0 = _3_mod;
        Dafny.ISequence<RAST._IModDecl> _5_dt__update_hbody_h0 = Dafny.Sequence<RAST._IModDecl>.Concat(_2_imports, (_3_mod).dtor_body);
        return RAST.Mod.create_Mod((_4_dt__update__tmp_h0).dtor_docString, (_4_dt__update__tmp_h0).dtor_attributes, (_4_dt__update__tmp_h0).dtor_name, _5_dt__update_hbody_h0);
      }
    }
    public static __T UniqueElementOf<__T>(Dafny.ISet<__T> s) {
      return Dafny.Helpers.Let<int, __T>(0, _let_dummy_69 =>  {
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
    public static RAST._IRASTTopDownVisitor<FactorPathsOptimization._IMapping> PathsVisitor() {
      return RAST.RASTTopDownVisitor<FactorPathsOptimization._IMapping>.create(((System.Func<FactorPathsOptimization._IMapping, RAST._IType, FactorPathsOptimization._IMapping>)((_0_current, _1_t) => {
  return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
    RAST._IType _source0 = _1_t;
    {
      if (_source0.is_TypeFromPath) {
        RAST._IPath path0 = _source0.dtor_path;
        if (path0.is_PMemberSelect) {
          RAST._IPath _2_base = path0.dtor_base;
          Dafny.ISequence<Dafny.Rune> _3_name = path0.dtor_name;
          if (object.Equals(_2_base, RAST.Path.create_Self())) {
            return _0_current;
          } else {
            return (_0_current).Add(_3_name, _2_base);
          }
        }
      }
    }
    {
      return _0_current;
    }
  }))();
})), ((System.Func<FactorPathsOptimization._IMapping, RAST._IExpr, FactorPathsOptimization._IMapping>)((_4_current, _5_e) => {
  return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
    RAST._IExpr _source1 = _5_e;
    {
      if (_source1.is_ExprFromPath) {
        RAST._IPath path1 = _source1.dtor_path;
        if (path1.is_PMemberSelect) {
          RAST._IPath _6_base = path1.dtor_base;
          Dafny.ISequence<Dafny.Rune> _7_id = path1.dtor_name;
          if (object.Equals(_6_base, RAST.Path.create_Self())) {
            return _4_current;
          } else if (((new BigInteger((_7_id).Count)).Sign == 1) && (((_7_id).Select((new BigInteger((_7_id).Count)) - (BigInteger.One))) == (new Dafny.Rune('!')))) {
            return (_4_current).Add((_7_id).Take((new BigInteger((_7_id).Count)) - (BigInteger.One)), _6_base);
          } else {
            return (_4_current).Add(_7_id, _6_base);
          }
        }
      }
    }
    {
      return _4_current;
    }
  }))();
})), ((System.Func<FactorPathsOptimization._IMapping, RAST._IModDecl, RAST._IPath, FactorPathsOptimization._IMapping>)((_8_current, _9_modDecl, _10_prefix) => {
  return ((System.Func<FactorPathsOptimization._IMapping>)(() => {
    RAST._IModDecl _source2 = _9_modDecl;
    {
      if (_source2.is_ModDecl) {
        RAST._IMod _11_mod = _source2.dtor_mod;
        return (_8_current).Add((_11_mod).dtor_name, _10_prefix);
      }
    }
    {
      if (_source2.is_StructDecl) {
        RAST._IStruct _12_struct = _source2.dtor_struct;
        return (_8_current).Add((_12_struct).dtor_name, _10_prefix);
      }
    }
    {
      if (_source2.is_TypeDecl) {
        RAST._ITypeSynonym _13_tpe = _source2.dtor_tpe;
        return (_8_current).Add((_13_tpe).dtor_name, _10_prefix);
      }
    }
    {
      if (_source2.is_ConstDecl) {
        RAST._IConstant _14_c = _source2.dtor_c;
        return (_8_current).Add((_14_c).dtor_name, _10_prefix);
      }
    }
    {
      if (_source2.is_EnumDecl) {
        RAST._IEnum _15_enum = _source2.dtor_enum;
        return (_8_current).Add((_15_enum).dtor_name, _10_prefix);
      }
    }
    {
      if (_source2.is_ImplDecl) {
        RAST._IImpl _16_impl = _source2.dtor_impl;
        return _8_current;
      }
    }
    {
      if (_source2.is_TraitDecl) {
        RAST._ITrait _17_tr = _source2.dtor_tr;
        RAST._IType _source3 = (_17_tr).dtor_tpe;
        {
          if (_source3.is_TypeApp) {
            RAST._IType baseName0 = _source3.dtor_baseName;
            if (baseName0.is_TIdentifier) {
              Dafny.ISequence<Dafny.Rune> _18_name = baseName0.dtor_name;
              return (_8_current).Add(_18_name, _10_prefix);
            }
          }
        }
        {
          if (_source3.is_TIdentifier) {
            Dafny.ISequence<Dafny.Rune> _19_name = _source3.dtor_name;
            return (_8_current).Add(_19_name, _10_prefix);
          }
        }
        {
          return _8_current;
        }
      }
    }
    {
      if (_source2.is_TopFnDecl) {
        RAST._ITopFnDecl _20_fn = _source2.dtor_fn;
        return (_8_current).Add(((_20_fn).dtor_fn).dtor_name, _10_prefix);
      }
    }
    {
      RAST._IUse _21_use = _source2.dtor_use;
      return _8_current;
    }
  }))();
})), false);
    }
    public static RAST._IRASTBottomUpReplacer PathSimplifier(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> replacement)
    {
      return RAST.RASTBottomUpReplacer.create(((System.Func<RAST._IMod, RAST._IPath, RAST._IMod>)((_0_m, _1_SelfPath) => {
  return FactorPathsOptimization.__default.applyPrefix(_0_m, (_1_SelfPath).MSel((_0_m).dtor_name));
})), Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IType, RAST._IType>>>((_2_replacement) => ((System.Func<RAST._IType, RAST._IType>)((_3_t) => {
  return ((System.Func<RAST._IType>)(() => {
    RAST._IType _source0 = _3_t;
    {
      if (_source0.is_TypeFromPath) {
        RAST._IPath path0 = _source0.dtor_path;
        if (path0.is_PMemberSelect) {
          RAST._IPath _4_base = path0.dtor_base;
          Dafny.ISequence<Dafny.Rune> _5_id = path0.dtor_name;
          if (((_2_replacement).Contains(_5_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_2_replacement,_5_id), _4_base))) {
            return RAST.Type.create_TSynonym(RAST.Type.create_TIdentifier(_5_id), _3_t);
          } else {
            return _3_t;
          }
        }
      }
    }
    {
      return _3_t;
    }
  }))();
})))(replacement), Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, Func<RAST._IExpr, RAST._IExpr>>>((_6_replacement) => ((System.Func<RAST._IExpr, RAST._IExpr>)((_7_e) => {
  return ((System.Func<RAST._IExpr>)(() => {
    RAST._IExpr _source1 = _7_e;
    {
      if (_source1.is_ExprFromPath) {
        RAST._IPath path1 = _source1.dtor_path;
        if (path1.is_PMemberSelect) {
          RAST._IPath _8_base = path1.dtor_base;
          Dafny.ISequence<Dafny.Rune> _9_id = path1.dtor_name;
          if (((_6_replacement).Contains(_9_id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_6_replacement,_9_id), _8_base))) {
            return RAST.Expr.create_Identifier(_9_id);
          } else if (((new BigInteger((_9_id).Count)).Sign == 1) && (((_9_id).Select((new BigInteger((_9_id).Count)) - (BigInteger.One))) == (new Dafny.Rune('!')))) {
            Dafny.ISequence<Dafny.Rune> _10_macro__id = (_9_id).Take((new BigInteger((_9_id).Count)) - (BigInteger.One));
            if (((_6_replacement).Contains(_10_macro__id)) && (object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_6_replacement,_10_macro__id), _8_base))) {
              return RAST.Expr.create_Identifier(_9_id);
            } else {
              return _7_e;
            }
          } else {
            return _7_e;
          }
        }
      }
    }
    {
      return _7_e;
    }
  }))();
})))(replacement));
    }
  }

  public interface _IMapping {
    bool is_Mapping { get; }
    Dafny.IMap<Dafny.ISequence<Dafny.Rune>,Dafny.ISet<RAST._IPath>> dtor_provenance { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_keys { get; }
    _IMapping DowncastClone();
    FactorPathsOptimization._IMapping Add(Dafny.ISequence<Dafny.Rune> k, RAST._IPath path);
    Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement(RAST._IPath SelfPath);
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
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> ToFinalReplacement(RAST._IPath SelfPath) {
      return Dafny.Helpers.Id<Func<RAST._IPath, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>>((_0_SelfPath) => ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in ((this).dtor_provenance).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1_identifier = (Dafny.ISequence<Dafny.Rune>)_compr_0;
          if (((this).dtor_provenance).Contains(_1_identifier)) {
            foreach (Dafny.ISet<RAST._IPath> _compr_1 in Dafny.Helpers.SingleValue<Dafny.ISet<RAST._IPath>>(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1_identifier))) {
              Dafny.ISet<RAST._IPath> _2_paths = (Dafny.ISet<RAST._IPath>)_compr_1;
              if (((_2_paths).Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISet<RAST._IPath>>.Select((this).dtor_provenance,_1_identifier))) && ((((new BigInteger((_2_paths).Count)) == (BigInteger.One)) || ((_2_paths).Contains(_0_SelfPath))) || ((_2_paths).Contains(RAST.__default.dafny__runtime)))) {
                _coll0.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IPath>(_1_identifier, (((new BigInteger((_2_paths).Count)) == (BigInteger.One)) ? (FactorPathsOptimization.__default.UniqueElementOf<RAST._IPath>(_2_paths)) : ((((_2_paths).Contains(_0_SelfPath)) ? (_0_SelfPath) : (RAST.__default.dafny__runtime))))));
              }
            }
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IPath>.FromCollection(_coll0);
      }))())(SelfPath);
    }
    public Dafny.ISequence<RAST._IModDecl> ToUseStatements(Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath> finalReplacement, RAST._IPath SelfPath)
    {
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_toUse = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IPath>, RAST._IPath, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1_finalReplacement, _2_SelfPath) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_3_key) => {
        return ((_1_finalReplacement).Contains(_3_key)) && (!object.Equals(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(_1_finalReplacement,_3_key), _2_SelfPath));
      })))(finalReplacement, SelfPath), (this).dtor_keys);
      return ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
        BigInteger dim15 = new BigInteger((_0_toUse).Count);
        var arr15 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
        for (int i15 = 0; i15 < dim15; i15++) {
          var _4_i = (BigInteger) i15;
          arr15[(int)(_4_i)] = RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IPath>.Select(finalReplacement,(_0_toUse).Select(_4_i))).MSel((_0_toUse).Select(_4_i))));
        }
        return Dafny.Sequence<RAST._IModDecl>.FromArray(arr15);
      }))();
    }
  }
} // end of namespace FactorPathsOptimization