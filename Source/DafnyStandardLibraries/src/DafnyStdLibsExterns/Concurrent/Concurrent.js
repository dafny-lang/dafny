var DafnyStdLibsExterns = DafnyStdLibsExterns || {};

DafnyStdLibsExterns.Concurrent = (function() {
    let $module = {};

    $module.MutableMap = class MutableMap {
      constructor () {
        this._tname = "DafnyStdLibs.Concurrent.MutableMap";
        this.internal = _dafny.Map.Empty;
      }
      _parentTraits() {
        return [];
      }
      __ctor(inv) {
        let _this = this;
        (_this).internal = _dafny.Map.Empty.slice();
        return;
      }
      Keys() {
        let _this = this;
        let keys = _dafny.Set.Empty;
        keys = (_this.internal).Keys;
        return keys;
      }
      HasKey(k) {
        let _this = this;
        let used = false;
        used = ((_this.internal).Keys).contains(k);
        return used;
      }
      Values() {
        let _this = this;
        let values = _dafny.Set.Empty;
        values = (_this.internal).Values;
        return values;
      }
      Items() {
        let _this = this;
        let items = _dafny.Set.Empty;
        items = (_this.internal).Items;
        return items;
      }
      Get(k) {
        let _this = this;
        let r = DafnyStdLibs_Wrappers.Option.Default();
        r = ((((_this.internal).Keys).contains(k)) ? (DafnyStdLibs_Wrappers.Option.create_Some((_this.internal).get(k))) : (DafnyStdLibs_Wrappers.Option.create_None()));
        return r;
      }
      Put(k, v) {
        let _this = this;
        (_this).internal = (_this.internal).update(k, v);
        return;
      }
      Remove(k) {
        let _this = this;
        (_this).internal = (_this.internal).Subtract(_dafny.Set.fromElements(k));
        return;
      }
      Size() {
        let _this = this;
        let c = _dafny.ZERO;
        c = new BigNumber((_this.internal).length);
        return c;
      }
    };
  
    $module.AtomicBox = class AtomicBox {
      constructor () {
        this._tname = "DafnyStdLibs.Concurrent.AtomicBox";
        this.boxed = undefined;
      }
      _parentTraits() {
        return [];
      }
      __ctor(inv, t) {
        let _this = this;
        (_this).boxed = t;
        return;
      }
      Get() {
        let _this = this;
        let t = undefined;
        t = _this.boxed;
        return t;
      }
      Put(t) {
        let _this = this;
        (_this).boxed = t;
        return;
      }
    };
  
    $module.Lock = class Lock {
      constructor () {
        this._tname = "DafnyStdLibs.Concurrent.Lock";
      }
      _parentTraits() {
        return [];
      }
      __ctor() {
        let _this = this;
        return;
      }
      __Lock() {
        let _this = this;
        return;
      }
      Unlock() {
        let _this = this;
        return;
      }
    };
    return $module;
  })(); // end of module DafnyStdLibs_ConcurrentDafny