// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace DafnyCompilerRustUtils {

  public partial class __default {
    public static _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> DafnyNameToContainingPathAndName(Dafny.ISequence<Dafny.Rune> n, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> acc)
    {
    TAIL_CALL_START: ;
      Dafny.ISequence<Dafny.Rune> _1273_s = (n);
      if ((new BigInteger((_1273_s).Count)).Sign == 0) {
        if ((new BigInteger((acc).Count)).Sign == 0) {
          return _System.Tuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        } else {
          return _System.Tuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.create((acc).Subsequence(BigInteger.Zero, (new BigInteger((acc).Count)) - (BigInteger.One)), ((acc).Select((new BigInteger((acc).Count)) - (BigInteger.One))));
        }
      } else if (((_1273_s).Select(BigInteger.Zero)) != (new Dafny.Rune('.'))) {
        if ((new BigInteger((acc).Count)).Sign == 0) {
          Dafny.ISequence<Dafny.Rune> _in125 = (_1273_s).Drop(BigInteger.One);
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in126 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1273_s).Subsequence(BigInteger.Zero, BigInteger.One));
          n = _in125;
          acc = _in126;
          goto TAIL_CALL_START;
        } else {
          Dafny.ISequence<Dafny.Rune> _in127 = (_1273_s).Drop(BigInteger.One);
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in128 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((acc).Subsequence(BigInteger.Zero, (new BigInteger((acc).Count)) - (BigInteger.One)), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.Concat((((acc).Select((new BigInteger((acc).Count)) - (BigInteger.One)))), Dafny.Sequence<Dafny.Rune>.FromElements((_1273_s).Select(BigInteger.Zero)))));
          n = _in127;
          acc = _in128;
          goto TAIL_CALL_START;
        }
      } else if ((new BigInteger((acc).Count)).Sign == 0) {
        Dafny.ISequence<Dafny.Rune> _in129 = (_1273_s).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in130 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
        n = _in129;
        acc = _in130;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<Dafny.Rune> _in131 = (_1273_s).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in132 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(acc, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
        n = _in131;
        acc = _in132;
        goto TAIL_CALL_START;
      }
    }
  }

  public partial class ModWithBody {
    private static readonly Dafny.TypeDescriptor<RAST._IMod> _TYPE = new Dafny.TypeDescriptor<RAST._IMod>(RAST.Mod.Default());
    public static Dafny.TypeDescriptor<RAST._IMod> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(RAST._IMod __source) {
      RAST._IMod _1274_x = __source;
      return (_1274_x).is_Mod;
    }
  }

  public partial class ExternMod {
    private static readonly Dafny.TypeDescriptor<RAST._IMod> _TYPE = new Dafny.TypeDescriptor<RAST._IMod>(RAST.Mod.Default());
    public static Dafny.TypeDescriptor<RAST._IMod> _TypeDescriptor() {
      return _TYPE;
    }
    public static bool _Is(RAST._IMod __source) {
      RAST._IMod _1275_x = __source;
      return (_1275_x).is_ExternMod;
    }
  }

  public interface _ISeqMap<K, V> {
    bool is_SeqMap { get; }
    Dafny.ISequence<K> dtor_keys { get; }
    Dafny.IMap<K,V> dtor_values { get; }
    _ISeqMap<__K, __V> DowncastClone<__K, __V>(Func<K, __K> converter0, Func<V, __V> converter1);
  }
  public class SeqMap<K, V> : _ISeqMap<K, V> {
    public readonly Dafny.ISequence<K> _keys;
    public readonly Dafny.IMap<K,V> _values;
    public SeqMap(Dafny.ISequence<K> keys, Dafny.IMap<K,V> values) {
      this._keys = keys;
      this._values = values;
    }
    public _ISeqMap<__K, __V> DowncastClone<__K, __V>(Func<K, __K> converter0, Func<V, __V> converter1) {
      if (this is _ISeqMap<__K, __V> dt) { return dt; }
      return new SeqMap<__K, __V>((_keys).DowncastClone<__K>(Dafny.Helpers.CastConverter<K, __K>), (_values).DowncastClone<__K, __V>(Dafny.Helpers.CastConverter<K, __K>, Dafny.Helpers.CastConverter<V, __V>));
    }
    public override bool Equals(object other) {
      var oth = other as DafnyCompilerRustUtils.SeqMap<K, V>;
      return oth != null && object.Equals(this._keys, oth._keys) && object.Equals(this._values, oth._values);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._keys));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._values));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyCompilerRustUtils.SeqMap.SeqMap";
      s += "(";
      s += Dafny.Helpers.ToString(this._keys);
      s += ", ";
      s += Dafny.Helpers.ToString(this._values);
      s += ")";
      return s;
    }
    public static DafnyCompilerRustUtils._ISeqMap<K, V> Default() {
      return create(Dafny.Sequence<K>.Empty, Dafny.Map<K, V>.Empty);
    }
    public static Dafny.TypeDescriptor<DafnyCompilerRustUtils._ISeqMap<K, V>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<DafnyCompilerRustUtils._ISeqMap<K, V>>(DafnyCompilerRustUtils.SeqMap<K, V>.Default());
    }
    public static _ISeqMap<K, V> create(Dafny.ISequence<K> keys, Dafny.IMap<K,V> values) {
      return new SeqMap<K, V>(keys, values);
    }
    public static _ISeqMap<K, V> create_SeqMap(Dafny.ISequence<K> keys, Dafny.IMap<K,V> values) {
      return create(keys, values);
    }
    public bool is_SeqMap { get { return true; } }
    public Dafny.ISequence<K> dtor_keys {
      get {
        return this._keys;
      }
    }
    public Dafny.IMap<K,V> dtor_values {
      get {
        return this._values;
      }
    }
    public static DafnyCompilerRustUtils._ISeqMap<K, V> Empty() {
      return DafnyCompilerRustUtils.SeqMap<K, V>.create(Dafny.Sequence<K>.FromElements(), Dafny.Map<K, V>.FromElements());
    }
    public static DafnyCompilerRustUtils._ISeqMap<K, V> Single(K key, V @value)
    {
      return DafnyCompilerRustUtils.SeqMap<K, V>.create(Dafny.Sequence<K>.FromElements(key), Dafny.Map<K, V>.FromElements(new Dafny.Pair<K, V>(key, @value)));
    }
  }

  public interface _IGatheringModule {
    bool is_GatheringModule { get; }
    bool is_ExternMod { get; }
    RAST._IMod dtor_existingMod { get; }
    DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> dtor_submodules { get; }
    RAST._IMod dtor_m { get; }
    _IGatheringModule DowncastClone();
    DafnyCompilerRustUtils._IGatheringModule Merge(DafnyCompilerRustUtils._IGatheringModule m2);
    RAST._IMod ToRust();
  }
  public abstract class GatheringModule : _IGatheringModule {
    public GatheringModule() {
    }
    private static readonly DafnyCompilerRustUtils._IGatheringModule theDefault = create_GatheringModule(RAST.Mod.Default(), DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default());
    public static DafnyCompilerRustUtils._IGatheringModule Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DafnyCompilerRustUtils._IGatheringModule> _TYPE = new Dafny.TypeDescriptor<DafnyCompilerRustUtils._IGatheringModule>(DafnyCompilerRustUtils.GatheringModule.Default());
    public static Dafny.TypeDescriptor<DafnyCompilerRustUtils._IGatheringModule> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGatheringModule create_GatheringModule(RAST._IMod existingMod, DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> submodules) {
      return new GatheringModule_GatheringModule(existingMod, submodules);
    }
    public static _IGatheringModule create_ExternMod(RAST._IMod m) {
      return new GatheringModule_ExternMod(m);
    }
    public bool is_GatheringModule { get { return this is GatheringModule_GatheringModule; } }
    public bool is_ExternMod { get { return this is GatheringModule_ExternMod; } }
    public RAST._IMod dtor_existingMod {
      get {
        var d = this;
        return ((GatheringModule_GatheringModule)d)._existingMod;
      }
    }
    public DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> dtor_submodules {
      get {
        var d = this;
        return ((GatheringModule_GatheringModule)d)._submodules;
      }
    }
    public RAST._IMod dtor_m {
      get {
        var d = this;
        return ((GatheringModule_ExternMod)d)._m;
      }
    }
    public abstract _IGatheringModule DowncastClone();
    public static DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> MergeSeqMap(DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> m1, DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> m2)
    {
      return DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((m1).dtor_keys, Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1276_m1) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_1277_k) => {
  return !((_1276_m1).dtor_keys).Contains(_1277_k);
})))(m1), (m2).dtor_keys)), Dafny.Helpers.Id<Func<DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>, DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,DafnyCompilerRustUtils._IGatheringModule>>>((_1278_m1, _1279_m2) => ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,DafnyCompilerRustUtils._IGatheringModule>>)(() => {
  var _coll7 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,DafnyCompilerRustUtils._IGatheringModule>>();
  foreach (Dafny.ISequence<Dafny.Rune> _compr_8 in (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(((_1278_m1).dtor_values).Keys, ((_1279_m2).dtor_values).Keys)).Elements) {
    Dafny.ISequence<Dafny.Rune> _1280_k = (Dafny.ISequence<Dafny.Rune>)_compr_8;
    if ((Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(((_1278_m1).dtor_values).Keys, ((_1279_m2).dtor_values).Keys)).Contains(_1280_k)) {
      _coll7.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,DafnyCompilerRustUtils._IGatheringModule>(_1280_k, ((((_1278_m1).dtor_values).Contains(_1280_k)) ? (((((_1279_m2).dtor_values).Contains(_1280_k)) ? ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_1278_m1).dtor_values,_1280_k)).Merge(Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_1279_m2).dtor_values,_1280_k))) : (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_1278_m1).dtor_values,_1280_k)))) : (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_1279_m2).dtor_values,_1280_k)))));
    }
  }
  return Dafny.Map<Dafny.ISequence<Dafny.Rune>,DafnyCompilerRustUtils._IGatheringModule>.FromCollection(_coll7);
}))())(m1, m2));
    }
    public static DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> MergeSeqMapAll(DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> m1, Dafny.ISequence<DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>> m2s)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((m2s).Count)).Sign == 0) {
        return m1;
      } else {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _in133 = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(m1, (m2s).Select(BigInteger.Zero));
        Dafny.ISequence<DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>> _in134 = (m2s).Drop(BigInteger.One);
        m1 = _in133;
        m2s = _in134;
        goto TAIL_CALL_START;
      }
    }
    public DafnyCompilerRustUtils._IGatheringModule Merge(DafnyCompilerRustUtils._IGatheringModule m2) {
      if (!((this).is_GatheringModule)) {
        return m2;
      } else if (!((m2).is_GatheringModule)) {
        return this;
      } else {
        return DafnyCompilerRustUtils.GatheringModule.create_GatheringModule(RAST.Mod.create_Mod(((this).dtor_existingMod).dtor_name, Dafny.Sequence<RAST._IModDecl>.Concat(((this).dtor_existingMod).dtor_body, ((m2).dtor_existingMod).dtor_body)), DafnyCompilerRustUtils.GatheringModule.MergeSeqMap((this).dtor_submodules, (m2).dtor_submodules));
      }
    }
    public static DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> Wrap(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath, RAST._IMod rawDecl)
    {
      if ((new BigInteger((containingPath).Count)).Sign == 0) {
        Dafny.ISequence<Dafny.Rune> _1281_name = (rawDecl).dtor_name;
        if ((rawDecl).is_Mod) {
          return DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Single(_1281_name, DafnyCompilerRustUtils.GatheringModule.create_GatheringModule(rawDecl, DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty()));
        } else {
          return DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Single(_1281_name, DafnyCompilerRustUtils.GatheringModule.create_ExternMod(rawDecl));
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _1282_enclosingModule = (containingPath).Select(BigInteger.Zero);
        return DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Single(_1282_enclosingModule, DafnyCompilerRustUtils.GatheringModule.create_GatheringModule(RAST.Mod.create_Mod(_1282_enclosingModule, Dafny.Sequence<RAST._IModDecl>.FromElements()), DafnyCompilerRustUtils.GatheringModule.Wrap((containingPath).Drop(BigInteger.One), rawDecl)));
      }
    }
    public RAST._IMod ToRust() {
      if ((this).is_ExternMod) {
        return (this).dtor_m;
      } else {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1283_keysWithContent = Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_1284_key) => {
          return (((this).dtor_submodules).dtor_values).Contains(_1284_key);
        })), ((this).dtor_submodules).dtor_keys);
        RAST._IMod _1285_dt__update__tmp_h0 = (this).dtor_existingMod;
        Dafny.ISequence<RAST._IModDecl> _1286_dt__update_hbody_h0 = Dafny.Sequence<RAST._IModDecl>.Concat(((this).dtor_existingMod).dtor_body, ((System.Func<Dafny.ISequence<RAST._IModDecl>>) (() => {
          BigInteger dim13 = new BigInteger((_1283_keysWithContent).Count);
          var arr13 = new RAST._IModDecl[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
          for (int i13 = 0; i13 < dim13; i13++) {
            var _1287_i = (BigInteger) i13;
            arr13[(int)(_1287_i)] = Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, RAST._IModDecl>((_1283_keysWithContent).Select(_1287_i), _pat_let18_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, RAST._IModDecl>(_pat_let18_0, _1288_moduleName => Dafny.Helpers.Let<RAST._IMod, RAST._IModDecl>((Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select(((this).dtor_submodules).dtor_values,_1288_moduleName)).ToRust(), _pat_let19_0 => Dafny.Helpers.Let<RAST._IMod, RAST._IModDecl>(_pat_let19_0, _1289_submodule => RAST.ModDecl.create_ModDecl(_1289_submodule)))));
          }
          return Dafny.Sequence<RAST._IModDecl>.FromArray(arr13);
        }))());
        return RAST.Mod.create_Mod((_1285_dt__update__tmp_h0).dtor_name, _1286_dt__update_hbody_h0);
      }
    }
  }
  public class GatheringModule_GatheringModule : GatheringModule {
    public readonly RAST._IMod _existingMod;
    public readonly DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _submodules;
    public GatheringModule_GatheringModule(RAST._IMod existingMod, DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> submodules) : base() {
      this._existingMod = existingMod;
      this._submodules = submodules;
    }
    public override _IGatheringModule DowncastClone() {
      if (this is _IGatheringModule dt) { return dt; }
      return new GatheringModule_GatheringModule(_existingMod, _submodules);
    }
    public override bool Equals(object other) {
      var oth = other as DafnyCompilerRustUtils.GatheringModule_GatheringModule;
      return oth != null && object.Equals(this._existingMod, oth._existingMod) && object.Equals(this._submodules, oth._submodules);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._existingMod));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._submodules));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyCompilerRustUtils.GatheringModule.GatheringModule";
      s += "(";
      s += Dafny.Helpers.ToString(this._existingMod);
      s += ", ";
      s += Dafny.Helpers.ToString(this._submodules);
      s += ")";
      return s;
    }
  }
  public class GatheringModule_ExternMod : GatheringModule {
    public readonly RAST._IMod _m;
    public GatheringModule_ExternMod(RAST._IMod m) : base() {
      this._m = m;
    }
    public override _IGatheringModule DowncastClone() {
      if (this is _IGatheringModule dt) { return dt; }
      return new GatheringModule_ExternMod(_m);
    }
    public override bool Equals(object other) {
      var oth = other as DafnyCompilerRustUtils.GatheringModule_ExternMod;
      return oth != null && object.Equals(this._m, oth._m);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._m));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyCompilerRustUtils.GatheringModule.ExternMod";
      s += "(";
      s += Dafny.Helpers.ToString(this._m);
      s += ")";
      return s;
    }
  }
} // end of namespace DafnyCompilerRustUtils