// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace DAST {


  public interface _IModule {
    bool is_Module { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    bool dtor_isExtern { get; }
    Dafny.ISequence<DAST._IModuleItem> dtor_body { get; }
    _IModule DowncastClone();
  }
  public class Module : _IModule {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly bool _i_isExtern;
    public readonly Dafny.ISequence<DAST._IModuleItem> _i_body;
    public Module(Dafny.ISequence<Dafny.Rune> name, bool isExtern, Dafny.ISequence<DAST._IModuleItem> body) {
      this._i_name = name;
      this._i_isExtern = isExtern;
      this._i_body = body;
    }
    public _IModule DowncastClone() {
      if (this is _IModule dt) { return dt; }
      return new Module(_i_name, _i_isExtern, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Module;
      return oth != null && object.Equals(this._i_name, oth._i_name) && this._i_isExtern == oth._i_isExtern && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_isExtern));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Module.Module";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_isExtern);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
    private static readonly DAST._IModule theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, false, Dafny.Sequence<DAST._IModuleItem>.Empty);
    public static DAST._IModule Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IModule> _TYPE = new Dafny.TypeDescriptor<DAST._IModule>(DAST.Module.Default());
    public static Dafny.TypeDescriptor<DAST._IModule> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IModule create(Dafny.ISequence<Dafny.Rune> name, bool isExtern, Dafny.ISequence<DAST._IModuleItem> body) {
      return new Module(name, isExtern, body);
    }
    public static _IModule create_Module(Dafny.ISequence<Dafny.Rune> name, bool isExtern, Dafny.ISequence<DAST._IModuleItem> body) {
      return create(name, isExtern, body);
    }
    public bool is_Module { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public bool dtor_isExtern {
      get {
        return this._i_isExtern;
      }
    }
    public Dafny.ISequence<DAST._IModuleItem> dtor_body {
      get {
        return this._i_body;
      }
    }
  }

  public interface _IModuleItem {
    bool is_Module { get; }
    bool is_Class { get; }
    bool is_Trait { get; }
    bool is_Newtype { get; }
    bool is_Datatype { get; }
    DAST._IModule dtor_Module_i_a0 { get; }
    DAST._IClass dtor_Class_i_a0 { get; }
    DAST._ITrait dtor_Trait_i_a0 { get; }
    DAST._INewtype dtor_Newtype_i_a0 { get; }
    DAST._IDatatype dtor_Datatype_i_a0 { get; }
    _IModuleItem DowncastClone();
  }
  public abstract class ModuleItem : _IModuleItem {
    public ModuleItem() {
    }
    private static readonly DAST._IModuleItem theDefault = create_Module(DAST.Module.Default());
    public static DAST._IModuleItem Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IModuleItem> _TYPE = new Dafny.TypeDescriptor<DAST._IModuleItem>(DAST.ModuleItem.Default());
    public static Dafny.TypeDescriptor<DAST._IModuleItem> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IModuleItem create_Module(DAST._IModule _a0) {
      return new ModuleItem_Module(_a0);
    }
    public static _IModuleItem create_Class(DAST._IClass _a0) {
      return new ModuleItem_Class(_a0);
    }
    public static _IModuleItem create_Trait(DAST._ITrait _a0) {
      return new ModuleItem_Trait(_a0);
    }
    public static _IModuleItem create_Newtype(DAST._INewtype _a0) {
      return new ModuleItem_Newtype(_a0);
    }
    public static _IModuleItem create_Datatype(DAST._IDatatype _a0) {
      return new ModuleItem_Datatype(_a0);
    }
    public bool is_Module { get { return this is ModuleItem_Module; } }
    public bool is_Class { get { return this is ModuleItem_Class; } }
    public bool is_Trait { get { return this is ModuleItem_Trait; } }
    public bool is_Newtype { get { return this is ModuleItem_Newtype; } }
    public bool is_Datatype { get { return this is ModuleItem_Datatype; } }
    public DAST._IModule dtor_Module_i_a0 {
      get {
        var d = this;
        return ((ModuleItem_Module)d)._i_a0;
      }
    }
    public DAST._IClass dtor_Class_i_a0 {
      get {
        var d = this;
        return ((ModuleItem_Class)d)._i_a0;
      }
    }
    public DAST._ITrait dtor_Trait_i_a0 {
      get {
        var d = this;
        return ((ModuleItem_Trait)d)._i_a0;
      }
    }
    public DAST._INewtype dtor_Newtype_i_a0 {
      get {
        var d = this;
        return ((ModuleItem_Newtype)d)._i_a0;
      }
    }
    public DAST._IDatatype dtor_Datatype_i_a0 {
      get {
        var d = this;
        return ((ModuleItem_Datatype)d)._i_a0;
      }
    }
    public abstract _IModuleItem DowncastClone();
  }
  public class ModuleItem_Module : ModuleItem {
    public readonly DAST._IModule _i_a0;
    public ModuleItem_Module(DAST._IModule _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Module(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Module;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Module";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Class : ModuleItem {
    public readonly DAST._IClass _i_a0;
    public ModuleItem_Class(DAST._IClass _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Class(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Class;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Class";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Trait : ModuleItem {
    public readonly DAST._ITrait _i_a0;
    public ModuleItem_Trait(DAST._ITrait _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Trait(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Trait;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Newtype : ModuleItem {
    public readonly DAST._INewtype _i_a0;
    public ModuleItem_Newtype(DAST._INewtype _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Newtype(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Newtype;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Newtype";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Datatype : ModuleItem {
    public readonly DAST._IDatatype _i_a0;
    public ModuleItem_Datatype(DAST._IDatatype _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Datatype(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Datatype;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Datatype";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }

  public interface _IType {
    bool is_Path { get; }
    bool is_Nullable { get; }
    bool is_Tuple { get; }
    bool is_Array { get; }
    bool is_Seq { get; }
    bool is_Set { get; }
    bool is_Multiset { get; }
    bool is_Map { get; }
    bool is_SetBuilder { get; }
    bool is_MapBuilder { get; }
    bool is_Arrow { get; }
    bool is_Primitive { get; }
    bool is_Passthrough { get; }
    bool is_TypeArg { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Path_i_a0 { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    DAST._IResolvedType dtor_resolved { get; }
    DAST._IType dtor_Nullable_i_a0 { get; }
    Dafny.ISequence<DAST._IType> dtor_Tuple_i_a0 { get; }
    DAST._IType dtor_element { get; }
    BigInteger dtor_dims { get; }
    DAST._IType dtor_key { get; }
    DAST._IType dtor_value { get; }
    Dafny.ISequence<DAST._IType> dtor_args { get; }
    DAST._IType dtor_result { get; }
    DAST._IPrimitive dtor_Primitive_i_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Passthrough_i_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_TypeArg_i_a0 { get; }
    _IType DowncastClone();
  }
  public abstract class Type : _IType {
    public Type() {
    }
    private static readonly DAST._IType theDefault = create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Sequence<DAST._IType>.Empty, DAST.ResolvedType.Default());
    public static DAST._IType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IType> _TYPE = new Dafny.TypeDescriptor<DAST._IType>(DAST.Type.Default());
    public static Dafny.TypeDescriptor<DAST._IType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IType create_Path(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0, Dafny.ISequence<DAST._IType> typeArgs, DAST._IResolvedType resolved) {
      return new Type_Path(_a0, typeArgs, resolved);
    }
    public static _IType create_Nullable(DAST._IType _a0) {
      return new Type_Nullable(_a0);
    }
    public static _IType create_Tuple(Dafny.ISequence<DAST._IType> _a0) {
      return new Type_Tuple(_a0);
    }
    public static _IType create_Array(DAST._IType element, BigInteger dims) {
      return new Type_Array(element, dims);
    }
    public static _IType create_Seq(DAST._IType element) {
      return new Type_Seq(element);
    }
    public static _IType create_Set(DAST._IType element) {
      return new Type_Set(element);
    }
    public static _IType create_Multiset(DAST._IType element) {
      return new Type_Multiset(element);
    }
    public static _IType create_Map(DAST._IType key, DAST._IType @value) {
      return new Type_Map(key, @value);
    }
    public static _IType create_SetBuilder(DAST._IType element) {
      return new Type_SetBuilder(element);
    }
    public static _IType create_MapBuilder(DAST._IType key, DAST._IType @value) {
      return new Type_MapBuilder(key, @value);
    }
    public static _IType create_Arrow(Dafny.ISequence<DAST._IType> args, DAST._IType result) {
      return new Type_Arrow(args, result);
    }
    public static _IType create_Primitive(DAST._IPrimitive _a0) {
      return new Type_Primitive(_a0);
    }
    public static _IType create_Passthrough(Dafny.ISequence<Dafny.Rune> _a0) {
      return new Type_Passthrough(_a0);
    }
    public static _IType create_TypeArg(Dafny.ISequence<Dafny.Rune> _a0) {
      return new Type_TypeArg(_a0);
    }
    public bool is_Path { get { return this is Type_Path; } }
    public bool is_Nullable { get { return this is Type_Nullable; } }
    public bool is_Tuple { get { return this is Type_Tuple; } }
    public bool is_Array { get { return this is Type_Array; } }
    public bool is_Seq { get { return this is Type_Seq; } }
    public bool is_Set { get { return this is Type_Set; } }
    public bool is_Multiset { get { return this is Type_Multiset; } }
    public bool is_Map { get { return this is Type_Map; } }
    public bool is_SetBuilder { get { return this is Type_SetBuilder; } }
    public bool is_MapBuilder { get { return this is Type_MapBuilder; } }
    public bool is_Arrow { get { return this is Type_Arrow; } }
    public bool is_Primitive { get { return this is Type_Primitive; } }
    public bool is_Passthrough { get { return this is Type_Passthrough; } }
    public bool is_TypeArg { get { return this is Type_TypeArg; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Path_i_a0 {
      get {
        var d = this;
        return ((Type_Path)d)._i_a0;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        return ((Type_Path)d)._i_typeArgs;
      }
    }
    public DAST._IResolvedType dtor_resolved {
      get {
        var d = this;
        return ((Type_Path)d)._i_resolved;
      }
    }
    public DAST._IType dtor_Nullable_i_a0 {
      get {
        var d = this;
        return ((Type_Nullable)d)._i_a0;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_Tuple_i_a0 {
      get {
        var d = this;
        return ((Type_Tuple)d)._i_a0;
      }
    }
    public DAST._IType dtor_element {
      get {
        var d = this;
        if (d is Type_Array) { return ((Type_Array)d)._i_element; }
        if (d is Type_Seq) { return ((Type_Seq)d)._i_element; }
        if (d is Type_Set) { return ((Type_Set)d)._i_element; }
        if (d is Type_Multiset) { return ((Type_Multiset)d)._i_element; }
        return ((Type_SetBuilder)d)._i_element;
      }
    }
    public BigInteger dtor_dims {
      get {
        var d = this;
        return ((Type_Array)d)._i_dims;
      }
    }
    public DAST._IType dtor_key {
      get {
        var d = this;
        if (d is Type_Map) { return ((Type_Map)d)._i_key; }
        return ((Type_MapBuilder)d)._i_key;
      }
    }
    public DAST._IType dtor_value {
      get {
        var d = this;
        if (d is Type_Map) { return ((Type_Map)d)._i_value; }
        return ((Type_MapBuilder)d)._i_value;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_args {
      get {
        var d = this;
        return ((Type_Arrow)d)._i_args;
      }
    }
    public DAST._IType dtor_result {
      get {
        var d = this;
        return ((Type_Arrow)d)._i_result;
      }
    }
    public DAST._IPrimitive dtor_Primitive_i_a0 {
      get {
        var d = this;
        return ((Type_Primitive)d)._i_a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_Passthrough_i_a0 {
      get {
        var d = this;
        return ((Type_Passthrough)d)._i_a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_TypeArg_i_a0 {
      get {
        var d = this;
        return ((Type_TypeArg)d)._i_a0;
      }
    }
    public abstract _IType DowncastClone();
  }
  public class Type_Path : Type {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_a0;
    public readonly Dafny.ISequence<DAST._IType> _i_typeArgs;
    public readonly DAST._IResolvedType _i_resolved;
    public Type_Path(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0, Dafny.ISequence<DAST._IType> typeArgs, DAST._IResolvedType resolved) : base() {
      this._i_a0 = _a0;
      this._i_typeArgs = typeArgs;
      this._i_resolved = resolved;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Path(_i_a0, _i_typeArgs, _i_resolved);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Path;
      return oth != null && object.Equals(this._i_a0, oth._i_a0) && object.Equals(this._i_typeArgs, oth._i_typeArgs) && object.Equals(this._i_resolved, oth._i_resolved);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_resolved));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Path";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_resolved);
      s += ")";
      return s;
    }
  }
  public class Type_Nullable : Type {
    public readonly DAST._IType _i_a0;
    public Type_Nullable(DAST._IType _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Nullable(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Nullable;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Nullable";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Type_Tuple : Type {
    public readonly Dafny.ISequence<DAST._IType> _i_a0;
    public Type_Tuple(Dafny.ISequence<DAST._IType> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Tuple(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Tuple;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Tuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Type_Array : Type {
    public readonly DAST._IType _i_element;
    public readonly BigInteger _i_dims;
    public Type_Array(DAST._IType element, BigInteger dims) : base() {
      this._i_element = element;
      this._i_dims = dims;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Array(_i_element, _i_dims);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Array;
      return oth != null && object.Equals(this._i_element, oth._i_element) && this._i_dims == oth._i_dims;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_element));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_dims));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_element);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_dims);
      s += ")";
      return s;
    }
  }
  public class Type_Seq : Type {
    public readonly DAST._IType _i_element;
    public Type_Seq(DAST._IType element) : base() {
      this._i_element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Seq(_i_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Seq;
      return oth != null && object.Equals(this._i_element, oth._i_element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_element));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Seq";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_element);
      s += ")";
      return s;
    }
  }
  public class Type_Set : Type {
    public readonly DAST._IType _i_element;
    public Type_Set(DAST._IType element) : base() {
      this._i_element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Set(_i_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Set;
      return oth != null && object.Equals(this._i_element, oth._i_element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_element));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Set";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_element);
      s += ")";
      return s;
    }
  }
  public class Type_Multiset : Type {
    public readonly DAST._IType _i_element;
    public Type_Multiset(DAST._IType element) : base() {
      this._i_element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Multiset(_i_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Multiset;
      return oth != null && object.Equals(this._i_element, oth._i_element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_element));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Multiset";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_element);
      s += ")";
      return s;
    }
  }
  public class Type_Map : Type {
    public readonly DAST._IType _i_key;
    public readonly DAST._IType _i_value;
    public Type_Map(DAST._IType key, DAST._IType @value) : base() {
      this._i_key = key;
      this._i_value = @value;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Map(_i_key, _i_value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Map;
      return oth != null && object.Equals(this._i_key, oth._i_key) && object.Equals(this._i_value, oth._i_value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Map";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_value);
      s += ")";
      return s;
    }
  }
  public class Type_SetBuilder : Type {
    public readonly DAST._IType _i_element;
    public Type_SetBuilder(DAST._IType element) : base() {
      this._i_element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_SetBuilder(_i_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_SetBuilder;
      return oth != null && object.Equals(this._i_element, oth._i_element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_element));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.SetBuilder";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_element);
      s += ")";
      return s;
    }
  }
  public class Type_MapBuilder : Type {
    public readonly DAST._IType _i_key;
    public readonly DAST._IType _i_value;
    public Type_MapBuilder(DAST._IType key, DAST._IType @value) : base() {
      this._i_key = key;
      this._i_value = @value;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_MapBuilder(_i_key, _i_value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_MapBuilder;
      return oth != null && object.Equals(this._i_key, oth._i_key) && object.Equals(this._i_value, oth._i_value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.MapBuilder";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_value);
      s += ")";
      return s;
    }
  }
  public class Type_Arrow : Type {
    public readonly Dafny.ISequence<DAST._IType> _i_args;
    public readonly DAST._IType _i_result;
    public Type_Arrow(Dafny.ISequence<DAST._IType> args, DAST._IType result) : base() {
      this._i_args = args;
      this._i_result = result;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Arrow(_i_args, _i_result);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Arrow;
      return oth != null && object.Equals(this._i_args, oth._i_args) && object.Equals(this._i_result, oth._i_result);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_result));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Arrow";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_result);
      s += ")";
      return s;
    }
  }
  public class Type_Primitive : Type {
    public readonly DAST._IPrimitive _i_a0;
    public Type_Primitive(DAST._IPrimitive _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Primitive(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Primitive;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Primitive";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Type_Passthrough : Type {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public Type_Passthrough(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Passthrough(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Passthrough;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Passthrough";
      s += "(";
      s += this._i_a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Type_TypeArg : Type {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public Type_TypeArg(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TypeArg(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_TypeArg;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Type.TypeArg";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }

  public interface _IPrimitive {
    bool is_Int { get; }
    bool is_Real { get; }
    bool is_String { get; }
    bool is_Bool { get; }
    bool is_Char { get; }
    _IPrimitive DowncastClone();
  }
  public abstract class Primitive : _IPrimitive {
    public Primitive() {
    }
    private static readonly DAST._IPrimitive theDefault = create_Int();
    public static DAST._IPrimitive Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IPrimitive> _TYPE = new Dafny.TypeDescriptor<DAST._IPrimitive>(DAST.Primitive.Default());
    public static Dafny.TypeDescriptor<DAST._IPrimitive> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPrimitive create_Int() {
      return new Primitive_Int();
    }
    public static _IPrimitive create_Real() {
      return new Primitive_Real();
    }
    public static _IPrimitive create_String() {
      return new Primitive_String();
    }
    public static _IPrimitive create_Bool() {
      return new Primitive_Bool();
    }
    public static _IPrimitive create_Char() {
      return new Primitive_Char();
    }
    public bool is_Int { get { return this is Primitive_Int; } }
    public bool is_Real { get { return this is Primitive_Real; } }
    public bool is_String { get { return this is Primitive_String; } }
    public bool is_Bool { get { return this is Primitive_Bool; } }
    public bool is_Char { get { return this is Primitive_Char; } }
    public static System.Collections.Generic.IEnumerable<_IPrimitive> AllSingletonConstructors {
      get {
        yield return Primitive.create_Int();
        yield return Primitive.create_Real();
        yield return Primitive.create_String();
        yield return Primitive.create_Bool();
        yield return Primitive.create_Char();
      }
    }
    public abstract _IPrimitive DowncastClone();
  }
  public class Primitive_Int : Primitive {
    public Primitive_Int() : base() {
    }
    public override _IPrimitive DowncastClone() {
      if (this is _IPrimitive dt) { return dt; }
      return new Primitive_Int();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Primitive_Int;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.Int";
      return s;
    }
  }
  public class Primitive_Real : Primitive {
    public Primitive_Real() : base() {
    }
    public override _IPrimitive DowncastClone() {
      if (this is _IPrimitive dt) { return dt; }
      return new Primitive_Real();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Primitive_Real;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.Real";
      return s;
    }
  }
  public class Primitive_String : Primitive {
    public Primitive_String() : base() {
    }
    public override _IPrimitive DowncastClone() {
      if (this is _IPrimitive dt) { return dt; }
      return new Primitive_String();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Primitive_String;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.String";
      return s;
    }
  }
  public class Primitive_Bool : Primitive {
    public Primitive_Bool() : base() {
    }
    public override _IPrimitive DowncastClone() {
      if (this is _IPrimitive dt) { return dt; }
      return new Primitive_Bool();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Primitive_Bool;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.Bool";
      return s;
    }
  }
  public class Primitive_Char : Primitive {
    public Primitive_Char() : base() {
    }
    public override _IPrimitive DowncastClone() {
      if (this is _IPrimitive dt) { return dt; }
      return new Primitive_Char();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Primitive_Char;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.Char";
      return s;
    }
  }

  public interface _INewtypeRange {
    bool is_U8 { get; }
    bool is_I8 { get; }
    bool is_U16 { get; }
    bool is_I16 { get; }
    bool is_U32 { get; }
    bool is_I32 { get; }
    bool is_U64 { get; }
    bool is_I64 { get; }
    bool is_U128 { get; }
    bool is_I128 { get; }
    bool is_BigInt { get; }
    bool is_NoRange { get; }
    _INewtypeRange DowncastClone();
  }
  public abstract class NewtypeRange : _INewtypeRange {
    public NewtypeRange() {
    }
    private static readonly DAST._INewtypeRange theDefault = create_U8();
    public static DAST._INewtypeRange Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtypeRange> _TYPE = new Dafny.TypeDescriptor<DAST._INewtypeRange>(DAST.NewtypeRange.Default());
    public static Dafny.TypeDescriptor<DAST._INewtypeRange> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtypeRange create_U8() {
      return new NewtypeRange_U8();
    }
    public static _INewtypeRange create_I8() {
      return new NewtypeRange_I8();
    }
    public static _INewtypeRange create_U16() {
      return new NewtypeRange_U16();
    }
    public static _INewtypeRange create_I16() {
      return new NewtypeRange_I16();
    }
    public static _INewtypeRange create_U32() {
      return new NewtypeRange_U32();
    }
    public static _INewtypeRange create_I32() {
      return new NewtypeRange_I32();
    }
    public static _INewtypeRange create_U64() {
      return new NewtypeRange_U64();
    }
    public static _INewtypeRange create_I64() {
      return new NewtypeRange_I64();
    }
    public static _INewtypeRange create_U128() {
      return new NewtypeRange_U128();
    }
    public static _INewtypeRange create_I128() {
      return new NewtypeRange_I128();
    }
    public static _INewtypeRange create_BigInt() {
      return new NewtypeRange_BigInt();
    }
    public static _INewtypeRange create_NoRange() {
      return new NewtypeRange_NoRange();
    }
    public bool is_U8 { get { return this is NewtypeRange_U8; } }
    public bool is_I8 { get { return this is NewtypeRange_I8; } }
    public bool is_U16 { get { return this is NewtypeRange_U16; } }
    public bool is_I16 { get { return this is NewtypeRange_I16; } }
    public bool is_U32 { get { return this is NewtypeRange_U32; } }
    public bool is_I32 { get { return this is NewtypeRange_I32; } }
    public bool is_U64 { get { return this is NewtypeRange_U64; } }
    public bool is_I64 { get { return this is NewtypeRange_I64; } }
    public bool is_U128 { get { return this is NewtypeRange_U128; } }
    public bool is_I128 { get { return this is NewtypeRange_I128; } }
    public bool is_BigInt { get { return this is NewtypeRange_BigInt; } }
    public bool is_NoRange { get { return this is NewtypeRange_NoRange; } }
    public static System.Collections.Generic.IEnumerable<_INewtypeRange> AllSingletonConstructors {
      get {
        yield return NewtypeRange.create_U8();
        yield return NewtypeRange.create_I8();
        yield return NewtypeRange.create_U16();
        yield return NewtypeRange.create_I16();
        yield return NewtypeRange.create_U32();
        yield return NewtypeRange.create_I32();
        yield return NewtypeRange.create_U64();
        yield return NewtypeRange.create_I64();
        yield return NewtypeRange.create_U128();
        yield return NewtypeRange.create_I128();
        yield return NewtypeRange.create_BigInt();
        yield return NewtypeRange.create_NoRange();
      }
    }
    public abstract _INewtypeRange DowncastClone();
  }
  public class NewtypeRange_U8 : NewtypeRange {
    public NewtypeRange_U8() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U8();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U8;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U8";
      return s;
    }
  }
  public class NewtypeRange_I8 : NewtypeRange {
    public NewtypeRange_I8() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I8();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I8;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I8";
      return s;
    }
  }
  public class NewtypeRange_U16 : NewtypeRange {
    public NewtypeRange_U16() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U16();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U16";
      return s;
    }
  }
  public class NewtypeRange_I16 : NewtypeRange {
    public NewtypeRange_I16() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I16();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I16";
      return s;
    }
  }
  public class NewtypeRange_U32 : NewtypeRange {
    public NewtypeRange_U32() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U32();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U32;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U32";
      return s;
    }
  }
  public class NewtypeRange_I32 : NewtypeRange {
    public NewtypeRange_I32() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I32();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I32;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I32";
      return s;
    }
  }
  public class NewtypeRange_U64 : NewtypeRange {
    public NewtypeRange_U64() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U64();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U64";
      return s;
    }
  }
  public class NewtypeRange_I64 : NewtypeRange {
    public NewtypeRange_I64() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I64();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I64";
      return s;
    }
  }
  public class NewtypeRange_U128 : NewtypeRange {
    public NewtypeRange_U128() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_U128();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_U128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.U128";
      return s;
    }
  }
  public class NewtypeRange_I128 : NewtypeRange {
    public NewtypeRange_I128() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_I128();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_I128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.I128";
      return s;
    }
  }
  public class NewtypeRange_BigInt : NewtypeRange {
    public NewtypeRange_BigInt() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_BigInt();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_BigInt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.BigInt";
      return s;
    }
  }
  public class NewtypeRange_NoRange : NewtypeRange {
    public NewtypeRange_NoRange() : base() {
    }
    public override _INewtypeRange DowncastClone() {
      if (this is _INewtypeRange dt) { return dt; }
      return new NewtypeRange_NoRange();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.NewtypeRange_NoRange;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.NewtypeRange.NoRange";
      return s;
    }
  }

  public interface _IResolvedType {
    bool is_Datatype { get; }
    bool is_Trait { get; }
    bool is_Newtype { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path { get; }
    DAST._IType dtor_baseType { get; }
    DAST._INewtypeRange dtor_range { get; }
    bool dtor_erase { get; }
    _IResolvedType DowncastClone();
  }
  public abstract class ResolvedType : _IResolvedType {
    public ResolvedType() {
    }
    private static readonly DAST._IResolvedType theDefault = create_Datatype(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty);
    public static DAST._IResolvedType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IResolvedType> _TYPE = new Dafny.TypeDescriptor<DAST._IResolvedType>(DAST.ResolvedType.Default());
    public static Dafny.TypeDescriptor<DAST._IResolvedType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IResolvedType create_Datatype(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) {
      return new ResolvedType_Datatype(path);
    }
    public static _IResolvedType create_Trait(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) {
      return new ResolvedType_Trait(path);
    }
    public static _IResolvedType create_Newtype(DAST._IType baseType, DAST._INewtypeRange range, bool erase) {
      return new ResolvedType_Newtype(baseType, range, erase);
    }
    public bool is_Datatype { get { return this is ResolvedType_Datatype; } }
    public bool is_Trait { get { return this is ResolvedType_Trait; } }
    public bool is_Newtype { get { return this is ResolvedType_Newtype; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path {
      get {
        var d = this;
        if (d is ResolvedType_Datatype) { return ((ResolvedType_Datatype)d)._i_path; }
        return ((ResolvedType_Trait)d)._i_path;
      }
    }
    public DAST._IType dtor_baseType {
      get {
        var d = this;
        return ((ResolvedType_Newtype)d)._i_baseType;
      }
    }
    public DAST._INewtypeRange dtor_range {
      get {
        var d = this;
        return ((ResolvedType_Newtype)d)._i_range;
      }
    }
    public bool dtor_erase {
      get {
        var d = this;
        return ((ResolvedType_Newtype)d)._i_erase;
      }
    }
    public abstract _IResolvedType DowncastClone();
  }
  public class ResolvedType_Datatype : ResolvedType {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_path;
    public ResolvedType_Datatype(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) : base() {
      this._i_path = path;
    }
    public override _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType_Datatype(_i_path);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType_Datatype;
      return oth != null && object.Equals(this._i_path, oth._i_path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_path));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.Datatype";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_path);
      s += ")";
      return s;
    }
  }
  public class ResolvedType_Trait : ResolvedType {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_path;
    public ResolvedType_Trait(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) : base() {
      this._i_path = path;
    }
    public override _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType_Trait(_i_path);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType_Trait;
      return oth != null && object.Equals(this._i_path, oth._i_path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_path));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_path);
      s += ")";
      return s;
    }
  }
  public class ResolvedType_Newtype : ResolvedType {
    public readonly DAST._IType _i_baseType;
    public readonly DAST._INewtypeRange _i_range;
    public readonly bool _i_erase;
    public ResolvedType_Newtype(DAST._IType baseType, DAST._INewtypeRange range, bool erase) : base() {
      this._i_baseType = baseType;
      this._i_range = range;
      this._i_erase = erase;
    }
    public override _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType_Newtype(_i_baseType, _i_range, _i_erase);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType_Newtype;
      return oth != null && object.Equals(this._i_baseType, oth._i_baseType) && object.Equals(this._i_range, oth._i_range) && this._i_erase == oth._i_erase;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_baseType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_erase));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.Newtype";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_baseType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_erase);
      s += ")";
      return s;
    }
  }

  public interface _IIdent {
    bool is_Ident { get; }
    Dafny.ISequence<Dafny.Rune> dtor_id { get; }
  }
  public class Ident : _IIdent {
    public readonly Dafny.ISequence<Dafny.Rune> _i_id;
    public Ident(Dafny.ISequence<Dafny.Rune> id) {
      this._i_id = id;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Ident;
      return oth != null && object.Equals(this._i_id, oth._i_id);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_id));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Ident.Ident";
      s += "(";
      s += this._i_id.ToVerbatimString(true);
      s += ")";
      return s;
    }
    private static readonly Dafny.ISequence<Dafny.Rune> theDefault = Dafny.Sequence<Dafny.Rune>.Empty;
    public static Dafny.ISequence<Dafny.Rune> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IIdent create(Dafny.ISequence<Dafny.Rune> id) {
      return new Ident(id);
    }
    public static _IIdent create_Ident(Dafny.ISequence<Dafny.Rune> id) {
      return create(id);
    }
    public bool is_Ident { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_id {
      get {
        return this._i_id;
      }
    }
  }

  public interface _IClass {
    bool is_Class { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_enclosingModule { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IType> dtor_superClasses { get; }
    Dafny.ISequence<DAST._IField> dtor_fields { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    _IClass DowncastClone();
  }
  public class Class : _IClass {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<Dafny.Rune> _i_enclosingModule;
    public readonly Dafny.ISequence<DAST._IType> _i_typeParams;
    public readonly Dafny.ISequence<DAST._IType> _i_superClasses;
    public readonly Dafny.ISequence<DAST._IField> _i_fields;
    public readonly Dafny.ISequence<DAST._IMethod> _i_body;
    public Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body) {
      this._i_name = name;
      this._i_enclosingModule = enclosingModule;
      this._i_typeParams = typeParams;
      this._i_superClasses = superClasses;
      this._i_fields = fields;
      this._i_body = body;
    }
    public _IClass DowncastClone() {
      if (this is _IClass dt) { return dt; }
      return new Class(_i_name, _i_enclosingModule, _i_typeParams, _i_superClasses, _i_fields, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Class;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_enclosingModule, oth._i_enclosingModule) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_superClasses, oth._i_superClasses) && object.Equals(this._i_fields, oth._i_fields) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_enclosingModule));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_superClasses));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_fields));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Class.Class";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_enclosingModule);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_superClasses);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_fields);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
    private static readonly DAST._IClass theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IField>.Empty, Dafny.Sequence<DAST._IMethod>.Empty);
    public static DAST._IClass Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IClass> _TYPE = new Dafny.TypeDescriptor<DAST._IClass>(DAST.Class.Default());
    public static Dafny.TypeDescriptor<DAST._IClass> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IClass create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body) {
      return new Class(name, enclosingModule, typeParams, superClasses, fields, body);
    }
    public static _IClass create_Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body) {
      return create(name, enclosingModule, typeParams, superClasses, fields, body);
    }
    public bool is_Class { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_enclosingModule {
      get {
        return this._i_enclosingModule;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_superClasses {
      get {
        return this._i_superClasses;
      }
    }
    public Dafny.ISequence<DAST._IField> dtor_fields {
      get {
        return this._i_fields;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_body {
      get {
        return this._i_body;
      }
    }
  }

  public interface _ITrait {
    bool is_Trait { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    _ITrait DowncastClone();
  }
  public class Trait : _ITrait {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<DAST._IType> _i_typeParams;
    public readonly Dafny.ISequence<DAST._IMethod> _i_body;
    public Trait(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IMethod> body) {
      this._i_name = name;
      this._i_typeParams = typeParams;
      this._i_body = body;
    }
    public _ITrait DowncastClone() {
      if (this is _ITrait dt) { return dt; }
      return new Trait(_i_name, _i_typeParams, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Trait;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Trait.Trait";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
    private static readonly DAST._ITrait theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IMethod>.Empty);
    public static DAST._ITrait Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ITrait> _TYPE = new Dafny.TypeDescriptor<DAST._ITrait>(DAST.Trait.Default());
    public static Dafny.TypeDescriptor<DAST._ITrait> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITrait create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IMethod> body) {
      return new Trait(name, typeParams, body);
    }
    public static _ITrait create_Trait(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IMethod> body) {
      return create(name, typeParams, body);
    }
    public bool is_Trait { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_body {
      get {
        return this._i_body;
      }
    }
  }

  public interface _IDatatype {
    bool is_Datatype { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.Rune> dtor_enclosingModule { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IDatatypeCtor> dtor_ctors { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    bool dtor_isCo { get; }
    _IDatatype DowncastClone();
  }
  public class Datatype : _IDatatype {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<Dafny.Rune> _i_enclosingModule;
    public readonly Dafny.ISequence<DAST._IType> _i_typeParams;
    public readonly Dafny.ISequence<DAST._IDatatypeCtor> _i_ctors;
    public readonly Dafny.ISequence<DAST._IMethod> _i_body;
    public readonly bool _i_isCo;
    public Datatype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IMethod> body, bool isCo) {
      this._i_name = name;
      this._i_enclosingModule = enclosingModule;
      this._i_typeParams = typeParams;
      this._i_ctors = ctors;
      this._i_body = body;
      this._i_isCo = isCo;
    }
    public _IDatatype DowncastClone() {
      if (this is _IDatatype dt) { return dt; }
      return new Datatype(_i_name, _i_enclosingModule, _i_typeParams, _i_ctors, _i_body, _i_isCo);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Datatype;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_enclosingModule, oth._i_enclosingModule) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_ctors, oth._i_ctors) && object.Equals(this._i_body, oth._i_body) && this._i_isCo == oth._i_isCo;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_enclosingModule));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_ctors));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_isCo));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Datatype.Datatype";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_enclosingModule);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_ctors);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_isCo);
      s += ")";
      return s;
    }
    private static readonly DAST._IDatatype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IDatatypeCtor>.Empty, Dafny.Sequence<DAST._IMethod>.Empty, false);
    public static DAST._IDatatype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IDatatype> _TYPE = new Dafny.TypeDescriptor<DAST._IDatatype>(DAST.Datatype.Default());
    public static Dafny.TypeDescriptor<DAST._IDatatype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDatatype create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IMethod> body, bool isCo) {
      return new Datatype(name, enclosingModule, typeParams, ctors, body, isCo);
    }
    public static _IDatatype create_Datatype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IMethod> body, bool isCo) {
      return create(name, enclosingModule, typeParams, ctors, body, isCo);
    }
    public bool is_Datatype { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_enclosingModule {
      get {
        return this._i_enclosingModule;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public Dafny.ISequence<DAST._IDatatypeCtor> dtor_ctors {
      get {
        return this._i_ctors;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_body {
      get {
        return this._i_body;
      }
    }
    public bool dtor_isCo {
      get {
        return this._i_isCo;
      }
    }
  }

  public interface _IDatatypeCtor {
    bool is_DatatypeCtor { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IFormal> dtor_args { get; }
    bool dtor_hasAnyArgs { get; }
    _IDatatypeCtor DowncastClone();
  }
  public class DatatypeCtor : _IDatatypeCtor {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<DAST._IFormal> _i_args;
    public readonly bool _i_hasAnyArgs;
    public DatatypeCtor(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IFormal> args, bool hasAnyArgs) {
      this._i_name = name;
      this._i_args = args;
      this._i_hasAnyArgs = hasAnyArgs;
    }
    public _IDatatypeCtor DowncastClone() {
      if (this is _IDatatypeCtor dt) { return dt; }
      return new DatatypeCtor(_i_name, _i_args, _i_hasAnyArgs);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.DatatypeCtor;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_args, oth._i_args) && this._i_hasAnyArgs == oth._i_hasAnyArgs;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_hasAnyArgs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.DatatypeCtor.DatatypeCtor";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_hasAnyArgs);
      s += ")";
      return s;
    }
    private static readonly DAST._IDatatypeCtor theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IFormal>.Empty, false);
    public static DAST._IDatatypeCtor Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IDatatypeCtor> _TYPE = new Dafny.TypeDescriptor<DAST._IDatatypeCtor>(DAST.DatatypeCtor.Default());
    public static Dafny.TypeDescriptor<DAST._IDatatypeCtor> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDatatypeCtor create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IFormal> args, bool hasAnyArgs) {
      return new DatatypeCtor(name, args, hasAnyArgs);
    }
    public static _IDatatypeCtor create_DatatypeCtor(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IFormal> args, bool hasAnyArgs) {
      return create(name, args, hasAnyArgs);
    }
    public bool is_DatatypeCtor { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_args {
      get {
        return this._i_args;
      }
    }
    public bool dtor_hasAnyArgs {
      get {
        return this._i_hasAnyArgs;
      }
    }
  }

  public interface _INewtype {
    bool is_Newtype { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    DAST._IType dtor_base { get; }
    DAST._INewtypeRange dtor_range { get; }
    Dafny.ISequence<DAST._IStatement> dtor_witnessStmts { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_witnessExpr { get; }
    _INewtype DowncastClone();
  }
  public class Newtype : _INewtype {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<DAST._IType> _i_typeParams;
    public readonly DAST._IType _i_base;
    public readonly DAST._INewtypeRange _i_range;
    public readonly Dafny.ISequence<DAST._IStatement> _i_witnessStmts;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _i_witnessExpr;
    public Newtype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, DAST._IType @base, DAST._INewtypeRange range, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr) {
      this._i_name = name;
      this._i_typeParams = typeParams;
      this._i_base = @base;
      this._i_range = range;
      this._i_witnessStmts = witnessStmts;
      this._i_witnessExpr = witnessExpr;
    }
    public _INewtype DowncastClone() {
      if (this is _INewtype dt) { return dt; }
      return new Newtype(_i_name, _i_typeParams, _i_base, _i_range, _i_witnessStmts, _i_witnessExpr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Newtype;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_base, oth._i_base) && object.Equals(this._i_range, oth._i_range) && object.Equals(this._i_witnessStmts, oth._i_witnessStmts) && object.Equals(this._i_witnessExpr, oth._i_witnessExpr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_witnessStmts));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_witnessExpr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Newtype.Newtype";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_base);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_witnessStmts);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_witnessExpr);
      s += ")";
      return s;
    }
    private static readonly DAST._INewtype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, DAST.Type.Default(), DAST.NewtypeRange.Default(), Dafny.Sequence<DAST._IStatement>.Empty, Std.Wrappers.Option<DAST._IExpression>.Default());
    public static DAST._INewtype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtype> _TYPE = new Dafny.TypeDescriptor<DAST._INewtype>(DAST.Newtype.Default());
    public static Dafny.TypeDescriptor<DAST._INewtype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtype create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, DAST._IType @base, DAST._INewtypeRange range, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr) {
      return new Newtype(name, typeParams, @base, range, witnessStmts, witnessExpr);
    }
    public static _INewtype create_Newtype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, DAST._IType @base, DAST._INewtypeRange range, Dafny.ISequence<DAST._IStatement> witnessStmts, Std.Wrappers._IOption<DAST._IExpression> witnessExpr) {
      return create(name, typeParams, @base, range, witnessStmts, witnessExpr);
    }
    public bool is_Newtype { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public DAST._IType dtor_base {
      get {
        return this._i_base;
      }
    }
    public DAST._INewtypeRange dtor_range {
      get {
        return this._i_range;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_witnessStmts {
      get {
        return this._i_witnessStmts;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_witnessExpr {
      get {
        return this._i_witnessExpr;
      }
    }
  }

  public interface _IClassItem {
    bool is_Method { get; }
    DAST._IMethod dtor_Method_i_a0 { get; }
  }
  public class ClassItem : _IClassItem {
    public readonly DAST._IMethod _i_a0;
    public ClassItem(DAST._IMethod _a0) {
      this._i_a0 = _a0;
    }
    public static DAST._IMethod DowncastClone(DAST._IMethod _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ClassItem;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.ClassItem.Method";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
    private static readonly DAST._IMethod theDefault = DAST.Method.Default();
    public static DAST._IMethod Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IMethod> _TYPE = new Dafny.TypeDescriptor<DAST._IMethod>(DAST.Method.Default());
    public static Dafny.TypeDescriptor<DAST._IMethod> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IClassItem create(DAST._IMethod _a0) {
      return new ClassItem(_a0);
    }
    public static _IClassItem create_Method(DAST._IMethod _a0) {
      return create(_a0);
    }
    public bool is_Method { get { return true; } }
    public DAST._IMethod dtor_Method_i_a0 {
      get {
        return this._i_a0;
      }
    }
  }

  public interface _IField {
    bool is_Field { get; }
    DAST._IFormal dtor_formal { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_defaultValue { get; }
    _IField DowncastClone();
  }
  public class Field : _IField {
    public readonly DAST._IFormal _i_formal;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _i_defaultValue;
    public Field(DAST._IFormal formal, Std.Wrappers._IOption<DAST._IExpression> defaultValue) {
      this._i_formal = formal;
      this._i_defaultValue = defaultValue;
    }
    public _IField DowncastClone() {
      if (this is _IField dt) { return dt; }
      return new Field(_i_formal, _i_defaultValue);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Field;
      return oth != null && object.Equals(this._i_formal, oth._i_formal) && object.Equals(this._i_defaultValue, oth._i_defaultValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_formal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_defaultValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Field.Field";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_formal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_defaultValue);
      s += ")";
      return s;
    }
    private static readonly DAST._IField theDefault = create(DAST.Formal.Default(), Std.Wrappers.Option<DAST._IExpression>.Default());
    public static DAST._IField Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IField> _TYPE = new Dafny.TypeDescriptor<DAST._IField>(DAST.Field.Default());
    public static Dafny.TypeDescriptor<DAST._IField> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IField create(DAST._IFormal formal, Std.Wrappers._IOption<DAST._IExpression> defaultValue) {
      return new Field(formal, defaultValue);
    }
    public static _IField create_Field(DAST._IFormal formal, Std.Wrappers._IOption<DAST._IExpression> defaultValue) {
      return create(formal, defaultValue);
    }
    public bool is_Field { get { return true; } }
    public DAST._IFormal dtor_formal {
      get {
        return this._i_formal;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_defaultValue {
      get {
        return this._i_defaultValue;
      }
    }
  }

  public interface _IFormal {
    bool is_Formal { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    DAST._IType dtor_typ { get; }
    _IFormal DowncastClone();
  }
  public class Formal : _IFormal {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly DAST._IType _i_typ;
    public Formal(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ) {
      this._i_name = name;
      this._i_typ = typ;
    }
    public _IFormal DowncastClone() {
      if (this is _IFormal dt) { return dt; }
      return new Formal(_i_name, _i_typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Formal;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typ, oth._i_typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Formal.Formal";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typ);
      s += ")";
      return s;
    }
    private static readonly DAST._IFormal theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, DAST.Type.Default());
    public static DAST._IFormal Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IFormal> _TYPE = new Dafny.TypeDescriptor<DAST._IFormal>(DAST.Formal.Default());
    public static Dafny.TypeDescriptor<DAST._IFormal> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFormal create(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ) {
      return new Formal(name, typ);
    }
    public static _IFormal create_Formal(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ) {
      return create(name, typ);
    }
    public bool is_Formal { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public DAST._IType dtor_typ {
      get {
        return this._i_typ;
      }
    }
  }

  public interface _IMethod {
    bool is_Method { get; }
    bool dtor_isStatic { get; }
    bool dtor_hasBody { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_overridingPath { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IFormal> dtor_params { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    Dafny.ISequence<DAST._IType> dtor_outTypes { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outVars { get; }
    _IMethod DowncastClone();
  }
  public class Method : _IMethod {
    public readonly bool _i_isStatic;
    public readonly bool _i_hasBody;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _i_overridingPath;
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly Dafny.ISequence<DAST._IType> _i_typeParams;
    public readonly Dafny.ISequence<DAST._IFormal> _i_params;
    public readonly Dafny.ISequence<DAST._IStatement> _i_body;
    public readonly Dafny.ISequence<DAST._IType> _i_outTypes;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _i_outVars;
    public Method(bool isStatic, bool hasBody, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      this._i_isStatic = isStatic;
      this._i_hasBody = hasBody;
      this._i_overridingPath = overridingPath;
      this._i_name = name;
      this._i_typeParams = typeParams;
      this._i_params = @params;
      this._i_body = body;
      this._i_outTypes = outTypes;
      this._i_outVars = outVars;
    }
    public _IMethod DowncastClone() {
      if (this is _IMethod dt) { return dt; }
      return new Method(_i_isStatic, _i_hasBody, _i_overridingPath, _i_name, _i_typeParams, _i_params, _i_body, _i_outTypes, _i_outVars);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Method;
      return oth != null && this._i_isStatic == oth._i_isStatic && this._i_hasBody == oth._i_hasBody && object.Equals(this._i_overridingPath, oth._i_overridingPath) && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typeParams, oth._i_typeParams) && object.Equals(this._i_params, oth._i_params) && object.Equals(this._i_body, oth._i_body) && object.Equals(this._i_outTypes, oth._i_outTypes) && object.Equals(this._i_outVars, oth._i_outVars);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_isStatic));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_hasBody));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_overridingPath));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_outTypes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_outVars));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Method.Method";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_isStatic);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_hasBody);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_overridingPath);
      s += ", ";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_params);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_outTypes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_outVars);
      s += ")";
      return s;
    }
    private static readonly DAST._IMethod theDefault = create(false, false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IFormal>.Empty, Dafny.Sequence<DAST._IStatement>.Empty, Dafny.Sequence<DAST._IType>.Empty, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.Default());
    public static DAST._IMethod Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IMethod> _TYPE = new Dafny.TypeDescriptor<DAST._IMethod>(DAST.Method.Default());
    public static Dafny.TypeDescriptor<DAST._IMethod> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMethod create(bool isStatic, bool hasBody, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      return new Method(isStatic, hasBody, overridingPath, name, typeParams, @params, body, outTypes, outVars);
    }
    public static _IMethod create_Method(bool isStatic, bool hasBody, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      return create(isStatic, hasBody, overridingPath, name, typeParams, @params, body, outTypes, outVars);
    }
    public bool is_Method { get { return true; } }
    public bool dtor_isStatic {
      get {
        return this._i_isStatic;
      }
    }
    public bool dtor_hasBody {
      get {
        return this._i_hasBody;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_overridingPath {
      get {
        return this._i_overridingPath;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._i_name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._i_typeParams;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_params {
      get {
        return this._i_params;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        return this._i_body;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_outTypes {
      get {
        return this._i_outTypes;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outVars {
      get {
        return this._i_outVars;
      }
    }
  }

  public interface _ICallName {
    bool is_Name { get; }
    bool is_MapBuilderAdd { get; }
    bool is_MapBuilderBuild { get; }
    bool is_SetBuilderAdd { get; }
    bool is_SetBuilderBuild { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    _ICallName DowncastClone();
  }
  public abstract class CallName : _ICallName {
    public CallName() {
    }
    private static readonly DAST._ICallName theDefault = create_Name(Dafny.Sequence<Dafny.Rune>.Empty);
    public static DAST._ICallName Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ICallName> _TYPE = new Dafny.TypeDescriptor<DAST._ICallName>(DAST.CallName.Default());
    public static Dafny.TypeDescriptor<DAST._ICallName> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICallName create_Name(Dafny.ISequence<Dafny.Rune> name) {
      return new CallName_Name(name);
    }
    public static _ICallName create_MapBuilderAdd() {
      return new CallName_MapBuilderAdd();
    }
    public static _ICallName create_MapBuilderBuild() {
      return new CallName_MapBuilderBuild();
    }
    public static _ICallName create_SetBuilderAdd() {
      return new CallName_SetBuilderAdd();
    }
    public static _ICallName create_SetBuilderBuild() {
      return new CallName_SetBuilderBuild();
    }
    public bool is_Name { get { return this is CallName_Name; } }
    public bool is_MapBuilderAdd { get { return this is CallName_MapBuilderAdd; } }
    public bool is_MapBuilderBuild { get { return this is CallName_MapBuilderBuild; } }
    public bool is_SetBuilderAdd { get { return this is CallName_SetBuilderAdd; } }
    public bool is_SetBuilderBuild { get { return this is CallName_SetBuilderBuild; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((CallName_Name)d)._i_name;
      }
    }
    public abstract _ICallName DowncastClone();
  }
  public class CallName_Name : CallName {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public CallName_Name(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._i_name = name;
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_Name(_i_name);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_Name;
      return oth != null && object.Equals(this._i_name, oth._i_name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.Name";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class CallName_MapBuilderAdd : CallName {
    public CallName_MapBuilderAdd() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_MapBuilderAdd();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_MapBuilderAdd;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.MapBuilderAdd";
      return s;
    }
  }
  public class CallName_MapBuilderBuild : CallName {
    public CallName_MapBuilderBuild() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_MapBuilderBuild();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_MapBuilderBuild;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.MapBuilderBuild";
      return s;
    }
  }
  public class CallName_SetBuilderAdd : CallName {
    public CallName_SetBuilderAdd() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_SetBuilderAdd();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_SetBuilderAdd;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.SetBuilderAdd";
      return s;
    }
  }
  public class CallName_SetBuilderBuild : CallName {
    public CallName_SetBuilderBuild() : base() {
    }
    public override _ICallName DowncastClone() {
      if (this is _ICallName dt) { return dt; }
      return new CallName_SetBuilderBuild();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CallName_SetBuilderBuild;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CallName.SetBuilderBuild";
      return s;
    }
  }

  public interface _IStatement {
    bool is_DeclareVar { get; }
    bool is_Assign { get; }
    bool is_If { get; }
    bool is_Labeled { get; }
    bool is_While { get; }
    bool is_Foreach { get; }
    bool is_Call { get; }
    bool is_Return { get; }
    bool is_EarlyReturn { get; }
    bool is_Break { get; }
    bool is_TailRecursive { get; }
    bool is_JumpTailCallStart { get; }
    bool is_Halt { get; }
    bool is_Print { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    DAST._IType dtor_typ { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_maybeValue { get; }
    DAST._IAssignLhs dtor_lhs { get; }
    DAST._IExpression dtor_value { get; }
    DAST._IExpression dtor_cond { get; }
    Dafny.ISequence<DAST._IStatement> dtor_thn { get; }
    Dafny.ISequence<DAST._IStatement> dtor_els { get; }
    Dafny.ISequence<Dafny.Rune> dtor_lbl { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    Dafny.ISequence<Dafny.Rune> dtor_boundName { get; }
    DAST._IType dtor_boundType { get; }
    DAST._IExpression dtor_over { get; }
    DAST._IExpression dtor_on { get; }
    DAST._ICallName dtor_callName { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outs { get; }
    DAST._IExpression dtor_expr { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_toLabel { get; }
    DAST._IExpression dtor_Print_i_a0 { get; }
    _IStatement DowncastClone();
  }
  public abstract class Statement : _IStatement {
    public Statement() {
    }
    private static readonly DAST._IStatement theDefault = create_DeclareVar(Dafny.Sequence<Dafny.Rune>.Empty, DAST.Type.Default(), Std.Wrappers.Option<DAST._IExpression>.Default());
    public static DAST._IStatement Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IStatement> _TYPE = new Dafny.TypeDescriptor<DAST._IStatement>(DAST.Statement.Default());
    public static Dafny.TypeDescriptor<DAST._IStatement> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStatement create_DeclareVar(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, Std.Wrappers._IOption<DAST._IExpression> maybeValue) {
      return new Statement_DeclareVar(name, typ, maybeValue);
    }
    public static _IStatement create_Assign(DAST._IAssignLhs lhs, DAST._IExpression @value) {
      return new Statement_Assign(lhs, @value);
    }
    public static _IStatement create_If(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> thn, Dafny.ISequence<DAST._IStatement> els) {
      return new Statement_If(cond, thn, els);
    }
    public static _IStatement create_Labeled(Dafny.ISequence<Dafny.Rune> lbl, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_Labeled(lbl, body);
    }
    public static _IStatement create_While(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_While(cond, body);
    }
    public static _IStatement create_Foreach(Dafny.ISequence<Dafny.Rune> boundName, DAST._IType boundType, DAST._IExpression over, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_Foreach(boundName, boundType, over, body);
    }
    public static _IStatement create_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outs) {
      return new Statement_Call(@on, callName, typeArgs, args, outs);
    }
    public static _IStatement create_Return(DAST._IExpression expr) {
      return new Statement_Return(expr);
    }
    public static _IStatement create_EarlyReturn() {
      return new Statement_EarlyReturn();
    }
    public static _IStatement create_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> toLabel) {
      return new Statement_Break(toLabel);
    }
    public static _IStatement create_TailRecursive(Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_TailRecursive(body);
    }
    public static _IStatement create_JumpTailCallStart() {
      return new Statement_JumpTailCallStart();
    }
    public static _IStatement create_Halt() {
      return new Statement_Halt();
    }
    public static _IStatement create_Print(DAST._IExpression _a0) {
      return new Statement_Print(_a0);
    }
    public bool is_DeclareVar { get { return this is Statement_DeclareVar; } }
    public bool is_Assign { get { return this is Statement_Assign; } }
    public bool is_If { get { return this is Statement_If; } }
    public bool is_Labeled { get { return this is Statement_Labeled; } }
    public bool is_While { get { return this is Statement_While; } }
    public bool is_Foreach { get { return this is Statement_Foreach; } }
    public bool is_Call { get { return this is Statement_Call; } }
    public bool is_Return { get { return this is Statement_Return; } }
    public bool is_EarlyReturn { get { return this is Statement_EarlyReturn; } }
    public bool is_Break { get { return this is Statement_Break; } }
    public bool is_TailRecursive { get { return this is Statement_TailRecursive; } }
    public bool is_JumpTailCallStart { get { return this is Statement_JumpTailCallStart; } }
    public bool is_Halt { get { return this is Statement_Halt; } }
    public bool is_Print { get { return this is Statement_Print; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((Statement_DeclareVar)d)._i_name;
      }
    }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        return ((Statement_DeclareVar)d)._i_typ;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_maybeValue {
      get {
        var d = this;
        return ((Statement_DeclareVar)d)._i_maybeValue;
      }
    }
    public DAST._IAssignLhs dtor_lhs {
      get {
        var d = this;
        return ((Statement_Assign)d)._i_lhs;
      }
    }
    public DAST._IExpression dtor_value {
      get {
        var d = this;
        return ((Statement_Assign)d)._i_value;
      }
    }
    public DAST._IExpression dtor_cond {
      get {
        var d = this;
        if (d is Statement_If) { return ((Statement_If)d)._i_cond; }
        return ((Statement_While)d)._i_cond;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_thn {
      get {
        var d = this;
        return ((Statement_If)d)._i_thn;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_els {
      get {
        var d = this;
        return ((Statement_If)d)._i_els;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_lbl {
      get {
        var d = this;
        return ((Statement_Labeled)d)._i_lbl;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        var d = this;
        if (d is Statement_Labeled) { return ((Statement_Labeled)d)._i_body; }
        if (d is Statement_While) { return ((Statement_While)d)._i_body; }
        if (d is Statement_Foreach) { return ((Statement_Foreach)d)._i_body; }
        return ((Statement_TailRecursive)d)._i_body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_boundName {
      get {
        var d = this;
        return ((Statement_Foreach)d)._i_boundName;
      }
    }
    public DAST._IType dtor_boundType {
      get {
        var d = this;
        return ((Statement_Foreach)d)._i_boundType;
      }
    }
    public DAST._IExpression dtor_over {
      get {
        var d = this;
        return ((Statement_Foreach)d)._i_over;
      }
    }
    public DAST._IExpression dtor_on {
      get {
        var d = this;
        return ((Statement_Call)d)._i_on;
      }
    }
    public DAST._ICallName dtor_callName {
      get {
        var d = this;
        return ((Statement_Call)d)._i_callName;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        return ((Statement_Call)d)._i_typeArgs;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_args {
      get {
        var d = this;
        return ((Statement_Call)d)._i_args;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outs {
      get {
        var d = this;
        return ((Statement_Call)d)._i_outs;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        return ((Statement_Return)d)._i_expr;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_toLabel {
      get {
        var d = this;
        return ((Statement_Break)d)._i_toLabel;
      }
    }
    public DAST._IExpression dtor_Print_i_a0 {
      get {
        var d = this;
        return ((Statement_Print)d)._i_a0;
      }
    }
    public abstract _IStatement DowncastClone();
  }
  public class Statement_DeclareVar : Statement {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly DAST._IType _i_typ;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _i_maybeValue;
    public Statement_DeclareVar(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, Std.Wrappers._IOption<DAST._IExpression> maybeValue) : base() {
      this._i_name = name;
      this._i_typ = typ;
      this._i_maybeValue = maybeValue;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_DeclareVar(_i_name, _i_typ, _i_maybeValue);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_DeclareVar;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typ, oth._i_typ) && object.Equals(this._i_maybeValue, oth._i_maybeValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typ));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_maybeValue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.DeclareVar";
      s += "(";
      s += this._i_name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typ);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_maybeValue);
      s += ")";
      return s;
    }
  }
  public class Statement_Assign : Statement {
    public readonly DAST._IAssignLhs _i_lhs;
    public readonly DAST._IExpression _i_value;
    public Statement_Assign(DAST._IAssignLhs lhs, DAST._IExpression @value) : base() {
      this._i_lhs = lhs;
      this._i_value = @value;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Assign(_i_lhs, _i_value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Assign;
      return oth != null && object.Equals(this._i_lhs, oth._i_lhs) && object.Equals(this._i_value, oth._i_value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_lhs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Assign";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_lhs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_value);
      s += ")";
      return s;
    }
  }
  public class Statement_If : Statement {
    public readonly DAST._IExpression _i_cond;
    public readonly Dafny.ISequence<DAST._IStatement> _i_thn;
    public readonly Dafny.ISequence<DAST._IStatement> _i_els;
    public Statement_If(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> thn, Dafny.ISequence<DAST._IStatement> els) : base() {
      this._i_cond = cond;
      this._i_thn = thn;
      this._i_els = els;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_If(_i_cond, _i_thn, _i_els);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_If;
      return oth != null && object.Equals(this._i_cond, oth._i_cond) && object.Equals(this._i_thn, oth._i_thn) && object.Equals(this._i_els, oth._i_els);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_els));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.If";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_thn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_els);
      s += ")";
      return s;
    }
  }
  public class Statement_Labeled : Statement {
    public readonly Dafny.ISequence<Dafny.Rune> _i_lbl;
    public readonly Dafny.ISequence<DAST._IStatement> _i_body;
    public Statement_Labeled(Dafny.ISequence<Dafny.Rune> lbl, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._i_lbl = lbl;
      this._i_body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Labeled(_i_lbl, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Labeled;
      return oth != null && object.Equals(this._i_lbl, oth._i_lbl) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_lbl));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Labeled";
      s += "(";
      s += this._i_lbl.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Statement_While : Statement {
    public readonly DAST._IExpression _i_cond;
    public readonly Dafny.ISequence<DAST._IStatement> _i_body;
    public Statement_While(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._i_cond = cond;
      this._i_body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_While(_i_cond, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_While;
      return oth != null && object.Equals(this._i_cond, oth._i_cond) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.While";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Statement_Foreach : Statement {
    public readonly Dafny.ISequence<Dafny.Rune> _i_boundName;
    public readonly DAST._IType _i_boundType;
    public readonly DAST._IExpression _i_over;
    public readonly Dafny.ISequence<DAST._IStatement> _i_body;
    public Statement_Foreach(Dafny.ISequence<Dafny.Rune> boundName, DAST._IType boundType, DAST._IExpression over, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._i_boundName = boundName;
      this._i_boundType = boundType;
      this._i_over = over;
      this._i_body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Foreach(_i_boundName, _i_boundType, _i_over, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Foreach;
      return oth != null && object.Equals(this._i_boundName, oth._i_boundName) && object.Equals(this._i_boundType, oth._i_boundType) && object.Equals(this._i_over, oth._i_over) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_boundName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_boundType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_over));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Foreach";
      s += "(";
      s += this._i_boundName.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_boundType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_over);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Statement_Call : Statement {
    public readonly DAST._IExpression _i_on;
    public readonly DAST._ICallName _i_callName;
    public readonly Dafny.ISequence<DAST._IType> _i_typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _i_args;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _i_outs;
    public Statement_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outs) : base() {
      this._i_on = @on;
      this._i_callName = callName;
      this._i_typeArgs = typeArgs;
      this._i_args = args;
      this._i_outs = outs;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Call(_i_on, _i_callName, _i_typeArgs, _i_args, _i_outs);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Call;
      return oth != null && object.Equals(this._i_on, oth._i_on) && object.Equals(this._i_callName, oth._i_callName) && object.Equals(this._i_typeArgs, oth._i_typeArgs) && object.Equals(this._i_args, oth._i_args) && object.Equals(this._i_outs, oth._i_outs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_callName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_outs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_callName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_outs);
      s += ")";
      return s;
    }
  }
  public class Statement_Return : Statement {
    public readonly DAST._IExpression _i_expr;
    public Statement_Return(DAST._IExpression expr) : base() {
      this._i_expr = expr;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Return(_i_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Return;
      return oth != null && object.Equals(this._i_expr, oth._i_expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Return";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ")";
      return s;
    }
  }
  public class Statement_EarlyReturn : Statement {
    public Statement_EarlyReturn() : base() {
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_EarlyReturn();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_EarlyReturn;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.EarlyReturn";
      return s;
    }
  }
  public class Statement_Break : Statement {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _i_toLabel;
    public Statement_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> toLabel) : base() {
      this._i_toLabel = toLabel;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Break(_i_toLabel);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Break;
      return oth != null && object.Equals(this._i_toLabel, oth._i_toLabel);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_toLabel));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Break";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_toLabel);
      s += ")";
      return s;
    }
  }
  public class Statement_TailRecursive : Statement {
    public readonly Dafny.ISequence<DAST._IStatement> _i_body;
    public Statement_TailRecursive(Dafny.ISequence<DAST._IStatement> body) : base() {
      this._i_body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_TailRecursive(_i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_TailRecursive;
      return oth != null && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.TailRecursive";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Statement_JumpTailCallStart : Statement {
    public Statement_JumpTailCallStart() : base() {
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_JumpTailCallStart();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_JumpTailCallStart;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.JumpTailCallStart";
      return s;
    }
  }
  public class Statement_Halt : Statement {
    public Statement_Halt() : base() {
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Halt();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Halt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Halt";
      return s;
    }
  }
  public class Statement_Print : Statement {
    public readonly DAST._IExpression _i_a0;
    public Statement_Print(DAST._IExpression _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Print(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Print;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Print";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }

  public interface _IAssignLhs {
    bool is_Ident { get; }
    bool is_Select { get; }
    bool is_Index { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Ident_i_a0 { get; }
    DAST._IExpression dtor_expr { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    Dafny.ISequence<DAST._IExpression> dtor_indices { get; }
    _IAssignLhs DowncastClone();
  }
  public abstract class AssignLhs : _IAssignLhs {
    public AssignLhs() {
    }
    private static readonly DAST._IAssignLhs theDefault = create_Ident(Dafny.Sequence<Dafny.Rune>.Empty);
    public static DAST._IAssignLhs Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IAssignLhs> _TYPE = new Dafny.TypeDescriptor<DAST._IAssignLhs>(DAST.AssignLhs.Default());
    public static Dafny.TypeDescriptor<DAST._IAssignLhs> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssignLhs create_Ident(Dafny.ISequence<Dafny.Rune> _a0) {
      return new AssignLhs_Ident(_a0);
    }
    public static _IAssignLhs create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field) {
      return new AssignLhs_Select(expr, field);
    }
    public static _IAssignLhs create_Index(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> indices) {
      return new AssignLhs_Index(expr, indices);
    }
    public bool is_Ident { get { return this is AssignLhs_Ident; } }
    public bool is_Select { get { return this is AssignLhs_Select; } }
    public bool is_Index { get { return this is AssignLhs_Index; } }
    public Dafny.ISequence<Dafny.Rune> dtor_Ident_i_a0 {
      get {
        var d = this;
        return ((AssignLhs_Ident)d)._i_a0;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        if (d is AssignLhs_Select) { return ((AssignLhs_Select)d)._i_expr; }
        return ((AssignLhs_Index)d)._i_expr;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        return ((AssignLhs_Select)d)._i_field;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_indices {
      get {
        var d = this;
        return ((AssignLhs_Index)d)._i_indices;
      }
    }
    public abstract _IAssignLhs DowncastClone();
  }
  public class AssignLhs_Ident : AssignLhs {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public AssignLhs_Ident(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Ident(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Ident;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Ident";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_Select : AssignLhs {
    public readonly DAST._IExpression _i_expr;
    public readonly Dafny.ISequence<Dafny.Rune> _i_field;
    public AssignLhs_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field) : base() {
      this._i_expr = expr;
      this._i_field = field;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Select(_i_expr, _i_field);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Select;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_field, oth._i_field);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_field));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += this._i_field.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_Index : AssignLhs {
    public readonly DAST._IExpression _i_expr;
    public readonly Dafny.ISequence<DAST._IExpression> _i_indices;
    public AssignLhs_Index(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> indices) : base() {
      this._i_expr = expr;
      this._i_indices = indices;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Index(_i_expr, _i_indices);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Index;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_indices, oth._i_indices);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_indices));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_indices);
      s += ")";
      return s;
    }
  }

  public interface _ICollKind {
    bool is_Seq { get; }
    bool is_Array { get; }
    bool is_Map { get; }
    _ICollKind DowncastClone();
  }
  public abstract class CollKind : _ICollKind {
    public CollKind() {
    }
    private static readonly DAST._ICollKind theDefault = create_Seq();
    public static DAST._ICollKind Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ICollKind> _TYPE = new Dafny.TypeDescriptor<DAST._ICollKind>(DAST.CollKind.Default());
    public static Dafny.TypeDescriptor<DAST._ICollKind> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICollKind create_Seq() {
      return new CollKind_Seq();
    }
    public static _ICollKind create_Array() {
      return new CollKind_Array();
    }
    public static _ICollKind create_Map() {
      return new CollKind_Map();
    }
    public bool is_Seq { get { return this is CollKind_Seq; } }
    public bool is_Array { get { return this is CollKind_Array; } }
    public bool is_Map { get { return this is CollKind_Map; } }
    public static System.Collections.Generic.IEnumerable<_ICollKind> AllSingletonConstructors {
      get {
        yield return CollKind.create_Seq();
        yield return CollKind.create_Array();
        yield return CollKind.create_Map();
      }
    }
    public abstract _ICollKind DowncastClone();
  }
  public class CollKind_Seq : CollKind {
    public CollKind_Seq() : base() {
    }
    public override _ICollKind DowncastClone() {
      if (this is _ICollKind dt) { return dt; }
      return new CollKind_Seq();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CollKind_Seq;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CollKind.Seq";
      return s;
    }
  }
  public class CollKind_Array : CollKind {
    public CollKind_Array() : base() {
    }
    public override _ICollKind DowncastClone() {
      if (this is _ICollKind dt) { return dt; }
      return new CollKind_Array();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CollKind_Array;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CollKind.Array";
      return s;
    }
  }
  public class CollKind_Map : CollKind {
    public CollKind_Map() : base() {
    }
    public override _ICollKind DowncastClone() {
      if (this is _ICollKind dt) { return dt; }
      return new CollKind_Map();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.CollKind_Map;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.CollKind.Map";
      return s;
    }
  }

  public interface _IBinOp {
    bool is_Eq { get; }
    bool is_Div { get; }
    bool is_EuclidianDiv { get; }
    bool is_Mod { get; }
    bool is_EuclidianMod { get; }
    bool is_Lt { get; }
    bool is_LtChar { get; }
    bool is_Plus { get; }
    bool is_Minus { get; }
    bool is_Times { get; }
    bool is_BitwiseAnd { get; }
    bool is_BitwiseOr { get; }
    bool is_BitwiseXor { get; }
    bool is_BitwiseShiftRight { get; }
    bool is_BitwiseShiftLeft { get; }
    bool is_And { get; }
    bool is_Or { get; }
    bool is_In { get; }
    bool is_SeqProperPrefix { get; }
    bool is_SeqPrefix { get; }
    bool is_SetMerge { get; }
    bool is_SetSubtraction { get; }
    bool is_SetIntersection { get; }
    bool is_Subset { get; }
    bool is_ProperSubset { get; }
    bool is_SetDisjoint { get; }
    bool is_MapMerge { get; }
    bool is_MapSubtraction { get; }
    bool is_MultisetMerge { get; }
    bool is_MultisetSubtraction { get; }
    bool is_MultisetIntersection { get; }
    bool is_Submultiset { get; }
    bool is_ProperSubmultiset { get; }
    bool is_MultisetDisjoint { get; }
    bool is_Concat { get; }
    bool is_Passthrough { get; }
    bool dtor_referential { get; }
    bool dtor_nullable { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Passthrough_i_a0 { get; }
    _IBinOp DowncastClone();
  }
  public abstract class BinOp : _IBinOp {
    public BinOp() {
    }
    private static readonly DAST._IBinOp theDefault = create_Eq(false, false);
    public static DAST._IBinOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IBinOp> _TYPE = new Dafny.TypeDescriptor<DAST._IBinOp>(DAST.BinOp.Default());
    public static Dafny.TypeDescriptor<DAST._IBinOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IBinOp create_Eq(bool referential, bool nullable) {
      return new BinOp_Eq(referential, nullable);
    }
    public static _IBinOp create_Div() {
      return new BinOp_Div();
    }
    public static _IBinOp create_EuclidianDiv() {
      return new BinOp_EuclidianDiv();
    }
    public static _IBinOp create_Mod() {
      return new BinOp_Mod();
    }
    public static _IBinOp create_EuclidianMod() {
      return new BinOp_EuclidianMod();
    }
    public static _IBinOp create_Lt() {
      return new BinOp_Lt();
    }
    public static _IBinOp create_LtChar() {
      return new BinOp_LtChar();
    }
    public static _IBinOp create_Plus() {
      return new BinOp_Plus();
    }
    public static _IBinOp create_Minus() {
      return new BinOp_Minus();
    }
    public static _IBinOp create_Times() {
      return new BinOp_Times();
    }
    public static _IBinOp create_BitwiseAnd() {
      return new BinOp_BitwiseAnd();
    }
    public static _IBinOp create_BitwiseOr() {
      return new BinOp_BitwiseOr();
    }
    public static _IBinOp create_BitwiseXor() {
      return new BinOp_BitwiseXor();
    }
    public static _IBinOp create_BitwiseShiftRight() {
      return new BinOp_BitwiseShiftRight();
    }
    public static _IBinOp create_BitwiseShiftLeft() {
      return new BinOp_BitwiseShiftLeft();
    }
    public static _IBinOp create_And() {
      return new BinOp_And();
    }
    public static _IBinOp create_Or() {
      return new BinOp_Or();
    }
    public static _IBinOp create_In() {
      return new BinOp_In();
    }
    public static _IBinOp create_SeqProperPrefix() {
      return new BinOp_SeqProperPrefix();
    }
    public static _IBinOp create_SeqPrefix() {
      return new BinOp_SeqPrefix();
    }
    public static _IBinOp create_SetMerge() {
      return new BinOp_SetMerge();
    }
    public static _IBinOp create_SetSubtraction() {
      return new BinOp_SetSubtraction();
    }
    public static _IBinOp create_SetIntersection() {
      return new BinOp_SetIntersection();
    }
    public static _IBinOp create_Subset() {
      return new BinOp_Subset();
    }
    public static _IBinOp create_ProperSubset() {
      return new BinOp_ProperSubset();
    }
    public static _IBinOp create_SetDisjoint() {
      return new BinOp_SetDisjoint();
    }
    public static _IBinOp create_MapMerge() {
      return new BinOp_MapMerge();
    }
    public static _IBinOp create_MapSubtraction() {
      return new BinOp_MapSubtraction();
    }
    public static _IBinOp create_MultisetMerge() {
      return new BinOp_MultisetMerge();
    }
    public static _IBinOp create_MultisetSubtraction() {
      return new BinOp_MultisetSubtraction();
    }
    public static _IBinOp create_MultisetIntersection() {
      return new BinOp_MultisetIntersection();
    }
    public static _IBinOp create_Submultiset() {
      return new BinOp_Submultiset();
    }
    public static _IBinOp create_ProperSubmultiset() {
      return new BinOp_ProperSubmultiset();
    }
    public static _IBinOp create_MultisetDisjoint() {
      return new BinOp_MultisetDisjoint();
    }
    public static _IBinOp create_Concat() {
      return new BinOp_Concat();
    }
    public static _IBinOp create_Passthrough(Dafny.ISequence<Dafny.Rune> _a0) {
      return new BinOp_Passthrough(_a0);
    }
    public bool is_Eq { get { return this is BinOp_Eq; } }
    public bool is_Div { get { return this is BinOp_Div; } }
    public bool is_EuclidianDiv { get { return this is BinOp_EuclidianDiv; } }
    public bool is_Mod { get { return this is BinOp_Mod; } }
    public bool is_EuclidianMod { get { return this is BinOp_EuclidianMod; } }
    public bool is_Lt { get { return this is BinOp_Lt; } }
    public bool is_LtChar { get { return this is BinOp_LtChar; } }
    public bool is_Plus { get { return this is BinOp_Plus; } }
    public bool is_Minus { get { return this is BinOp_Minus; } }
    public bool is_Times { get { return this is BinOp_Times; } }
    public bool is_BitwiseAnd { get { return this is BinOp_BitwiseAnd; } }
    public bool is_BitwiseOr { get { return this is BinOp_BitwiseOr; } }
    public bool is_BitwiseXor { get { return this is BinOp_BitwiseXor; } }
    public bool is_BitwiseShiftRight { get { return this is BinOp_BitwiseShiftRight; } }
    public bool is_BitwiseShiftLeft { get { return this is BinOp_BitwiseShiftLeft; } }
    public bool is_And { get { return this is BinOp_And; } }
    public bool is_Or { get { return this is BinOp_Or; } }
    public bool is_In { get { return this is BinOp_In; } }
    public bool is_SeqProperPrefix { get { return this is BinOp_SeqProperPrefix; } }
    public bool is_SeqPrefix { get { return this is BinOp_SeqPrefix; } }
    public bool is_SetMerge { get { return this is BinOp_SetMerge; } }
    public bool is_SetSubtraction { get { return this is BinOp_SetSubtraction; } }
    public bool is_SetIntersection { get { return this is BinOp_SetIntersection; } }
    public bool is_Subset { get { return this is BinOp_Subset; } }
    public bool is_ProperSubset { get { return this is BinOp_ProperSubset; } }
    public bool is_SetDisjoint { get { return this is BinOp_SetDisjoint; } }
    public bool is_MapMerge { get { return this is BinOp_MapMerge; } }
    public bool is_MapSubtraction { get { return this is BinOp_MapSubtraction; } }
    public bool is_MultisetMerge { get { return this is BinOp_MultisetMerge; } }
    public bool is_MultisetSubtraction { get { return this is BinOp_MultisetSubtraction; } }
    public bool is_MultisetIntersection { get { return this is BinOp_MultisetIntersection; } }
    public bool is_Submultiset { get { return this is BinOp_Submultiset; } }
    public bool is_ProperSubmultiset { get { return this is BinOp_ProperSubmultiset; } }
    public bool is_MultisetDisjoint { get { return this is BinOp_MultisetDisjoint; } }
    public bool is_Concat { get { return this is BinOp_Concat; } }
    public bool is_Passthrough { get { return this is BinOp_Passthrough; } }
    public bool dtor_referential {
      get {
        var d = this;
        return ((BinOp_Eq)d)._i_referential;
      }
    }
    public bool dtor_nullable {
      get {
        var d = this;
        return ((BinOp_Eq)d)._i_nullable;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_Passthrough_i_a0 {
      get {
        var d = this;
        return ((BinOp_Passthrough)d)._i_a0;
      }
    }
    public abstract _IBinOp DowncastClone();
  }
  public class BinOp_Eq : BinOp {
    public readonly bool _i_referential;
    public readonly bool _i_nullable;
    public BinOp_Eq(bool referential, bool nullable) : base() {
      this._i_referential = referential;
      this._i_nullable = nullable;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Eq(_i_referential, _i_nullable);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Eq;
      return oth != null && this._i_referential == oth._i_referential && this._i_nullable == oth._i_nullable;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_referential));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_nullable));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Eq";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_referential);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_nullable);
      s += ")";
      return s;
    }
  }
  public class BinOp_Div : BinOp {
    public BinOp_Div() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Div();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Div;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Div";
      return s;
    }
  }
  public class BinOp_EuclidianDiv : BinOp {
    public BinOp_EuclidianDiv() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_EuclidianDiv();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_EuclidianDiv;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.EuclidianDiv";
      return s;
    }
  }
  public class BinOp_Mod : BinOp {
    public BinOp_Mod() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Mod();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Mod;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Mod";
      return s;
    }
  }
  public class BinOp_EuclidianMod : BinOp {
    public BinOp_EuclidianMod() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_EuclidianMod();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_EuclidianMod;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.EuclidianMod";
      return s;
    }
  }
  public class BinOp_Lt : BinOp {
    public BinOp_Lt() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Lt();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Lt;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Lt";
      return s;
    }
  }
  public class BinOp_LtChar : BinOp {
    public BinOp_LtChar() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_LtChar();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_LtChar;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.LtChar";
      return s;
    }
  }
  public class BinOp_Plus : BinOp {
    public BinOp_Plus() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Plus();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Plus;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Plus";
      return s;
    }
  }
  public class BinOp_Minus : BinOp {
    public BinOp_Minus() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Minus();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Minus;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Minus";
      return s;
    }
  }
  public class BinOp_Times : BinOp {
    public BinOp_Times() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Times();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Times;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Times";
      return s;
    }
  }
  public class BinOp_BitwiseAnd : BinOp {
    public BinOp_BitwiseAnd() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseAnd();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseAnd;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseAnd";
      return s;
    }
  }
  public class BinOp_BitwiseOr : BinOp {
    public BinOp_BitwiseOr() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseOr();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseOr;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseOr";
      return s;
    }
  }
  public class BinOp_BitwiseXor : BinOp {
    public BinOp_BitwiseXor() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseXor();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseXor;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseXor";
      return s;
    }
  }
  public class BinOp_BitwiseShiftRight : BinOp {
    public BinOp_BitwiseShiftRight() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseShiftRight();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseShiftRight;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseShiftRight";
      return s;
    }
  }
  public class BinOp_BitwiseShiftLeft : BinOp {
    public BinOp_BitwiseShiftLeft() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_BitwiseShiftLeft();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_BitwiseShiftLeft;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.BitwiseShiftLeft";
      return s;
    }
  }
  public class BinOp_And : BinOp {
    public BinOp_And() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_And();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_And;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.And";
      return s;
    }
  }
  public class BinOp_Or : BinOp {
    public BinOp_Or() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Or();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Or;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Or";
      return s;
    }
  }
  public class BinOp_In : BinOp {
    public BinOp_In() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_In();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_In;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.In";
      return s;
    }
  }
  public class BinOp_SeqProperPrefix : BinOp {
    public BinOp_SeqProperPrefix() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SeqProperPrefix();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SeqProperPrefix;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SeqProperPrefix";
      return s;
    }
  }
  public class BinOp_SeqPrefix : BinOp {
    public BinOp_SeqPrefix() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SeqPrefix();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SeqPrefix;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SeqPrefix";
      return s;
    }
  }
  public class BinOp_SetMerge : BinOp {
    public BinOp_SetMerge() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetMerge();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetMerge;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetMerge";
      return s;
    }
  }
  public class BinOp_SetSubtraction : BinOp {
    public BinOp_SetSubtraction() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetSubtraction();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetSubtraction;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetSubtraction";
      return s;
    }
  }
  public class BinOp_SetIntersection : BinOp {
    public BinOp_SetIntersection() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetIntersection();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetIntersection;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetIntersection";
      return s;
    }
  }
  public class BinOp_Subset : BinOp {
    public BinOp_Subset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Subset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Subset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Subset";
      return s;
    }
  }
  public class BinOp_ProperSubset : BinOp {
    public BinOp_ProperSubset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_ProperSubset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_ProperSubset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.ProperSubset";
      return s;
    }
  }
  public class BinOp_SetDisjoint : BinOp {
    public BinOp_SetDisjoint() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_SetDisjoint();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_SetDisjoint;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.SetDisjoint";
      return s;
    }
  }
  public class BinOp_MapMerge : BinOp {
    public BinOp_MapMerge() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MapMerge();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MapMerge;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MapMerge";
      return s;
    }
  }
  public class BinOp_MapSubtraction : BinOp {
    public BinOp_MapSubtraction() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MapSubtraction();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MapSubtraction;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 27;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MapSubtraction";
      return s;
    }
  }
  public class BinOp_MultisetMerge : BinOp {
    public BinOp_MultisetMerge() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetMerge();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetMerge;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetMerge";
      return s;
    }
  }
  public class BinOp_MultisetSubtraction : BinOp {
    public BinOp_MultisetSubtraction() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetSubtraction();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetSubtraction;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 29;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetSubtraction";
      return s;
    }
  }
  public class BinOp_MultisetIntersection : BinOp {
    public BinOp_MultisetIntersection() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetIntersection();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetIntersection;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetIntersection";
      return s;
    }
  }
  public class BinOp_Submultiset : BinOp {
    public BinOp_Submultiset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Submultiset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Submultiset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 31;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Submultiset";
      return s;
    }
  }
  public class BinOp_ProperSubmultiset : BinOp {
    public BinOp_ProperSubmultiset() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_ProperSubmultiset();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_ProperSubmultiset;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 32;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.ProperSubmultiset";
      return s;
    }
  }
  public class BinOp_MultisetDisjoint : BinOp {
    public BinOp_MultisetDisjoint() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_MultisetDisjoint();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_MultisetDisjoint;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 33;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.MultisetDisjoint";
      return s;
    }
  }
  public class BinOp_Concat : BinOp {
    public BinOp_Concat() : base() {
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Concat();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Concat;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 34;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Concat";
      return s;
    }
  }
  public class BinOp_Passthrough : BinOp {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public BinOp_Passthrough(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IBinOp DowncastClone() {
      if (this is _IBinOp dt) { return dt; }
      return new BinOp_Passthrough(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.BinOp_Passthrough;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 35;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.BinOp.Passthrough";
      s += "(";
      s += this._i_a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _IExpression {
    bool is_Literal { get; }
    bool is_Ident { get; }
    bool is_Companion { get; }
    bool is_Tuple { get; }
    bool is_New { get; }
    bool is_NewArray { get; }
    bool is_DatatypeValue { get; }
    bool is_Convert { get; }
    bool is_SeqConstruct { get; }
    bool is_SeqValue { get; }
    bool is_SetValue { get; }
    bool is_MultisetValue { get; }
    bool is_MapValue { get; }
    bool is_MapBuilder { get; }
    bool is_SeqUpdate { get; }
    bool is_MapUpdate { get; }
    bool is_SetBuilder { get; }
    bool is_ToMultiset { get; }
    bool is_This { get; }
    bool is_Ite { get; }
    bool is_UnOp { get; }
    bool is_BinOp { get; }
    bool is_ArrayLen { get; }
    bool is_MapKeys { get; }
    bool is_MapValues { get; }
    bool is_Select { get; }
    bool is_SelectFn { get; }
    bool is_Index { get; }
    bool is_IndexRange { get; }
    bool is_TupleSelect { get; }
    bool is_Call { get; }
    bool is_Lambda { get; }
    bool is_BetaRedex { get; }
    bool is_IIFE { get; }
    bool is_Apply { get; }
    bool is_TypeTest { get; }
    bool is_InitializationValue { get; }
    bool is_BoolBoundedPool { get; }
    bool is_SetBoundedPool { get; }
    bool is_SeqBoundedPool { get; }
    bool is_IntRange { get; }
    DAST._ILiteral dtor_Literal_i_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Ident_i_a0 { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Companion_i_a0 { get; }
    Dafny.ISequence<DAST._IExpression> dtor_Tuple_i_a0 { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    Dafny.ISequence<DAST._IExpression> dtor_dims { get; }
    DAST._IType dtor_typ { get; }
    Dafny.ISequence<Dafny.Rune> dtor_variant { get; }
    bool dtor_isCo { get; }
    Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> dtor_contents { get; }
    DAST._IExpression dtor_value { get; }
    DAST._IType dtor_from { get; }
    DAST._IExpression dtor_length { get; }
    DAST._IExpression dtor_elem { get; }
    Dafny.ISequence<DAST._IExpression> dtor_elements { get; }
    Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> dtor_mapElems { get; }
    DAST._IType dtor_keyType { get; }
    DAST._IType dtor_valueType { get; }
    DAST._IExpression dtor_expr { get; }
    DAST._IExpression dtor_indexExpr { get; }
    DAST._IType dtor_elemType { get; }
    DAST._IExpression dtor_ToMultiset_i_a0 { get; }
    DAST._IExpression dtor_cond { get; }
    DAST._IExpression dtor_thn { get; }
    DAST._IExpression dtor_els { get; }
    DAST._IUnaryOp dtor_unOp { get; }
    DAST.Format._IUnaryOpFormat dtor_format1 { get; }
    DAST._IBinOp dtor_op { get; }
    DAST._IExpression dtor_left { get; }
    DAST._IExpression dtor_right { get; }
    DAST.Format._IBinaryOpFormat dtor_format2 { get; }
    BigInteger dtor_dim { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    bool dtor_isConstant { get; }
    bool dtor_onDatatype { get; }
    bool dtor_isStatic { get; }
    BigInteger dtor_arity { get; }
    DAST._ICollKind dtor_collKind { get; }
    Dafny.ISequence<DAST._IExpression> dtor_indices { get; }
    bool dtor_isArray { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_low { get; }
    Std.Wrappers._IOption<DAST._IExpression> dtor_high { get; }
    BigInteger dtor_index { get; }
    DAST._IExpression dtor_on { get; }
    DAST._ICallName dtor_callName { get; }
    Dafny.ISequence<DAST._IFormal> dtor_params { get; }
    DAST._IType dtor_retType { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> dtor_values { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    DAST._IExpression dtor_iifeBody { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_dType { get; }
    DAST._IExpression dtor_of { get; }
    bool dtor_includeDuplicates { get; }
    DAST._IExpression dtor_lo { get; }
    DAST._IExpression dtor_hi { get; }
    _IExpression DowncastClone();
  }
  public abstract class Expression : _IExpression {
    public Expression() {
    }
    private static readonly DAST._IExpression theDefault = create_Literal(DAST.Literal.Default());
    public static DAST._IExpression Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IExpression> _TYPE = new Dafny.TypeDescriptor<DAST._IExpression>(DAST.Expression.Default());
    public static Dafny.TypeDescriptor<DAST._IExpression> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpression create_Literal(DAST._ILiteral _a0) {
      return new Expression_Literal(_a0);
    }
    public static _IExpression create_Ident(Dafny.ISequence<Dafny.Rune> _a0) {
      return new Expression_Ident(_a0);
    }
    public static _IExpression create_Companion(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0) {
      return new Expression_Companion(_a0);
    }
    public static _IExpression create_Tuple(Dafny.ISequence<DAST._IExpression> _a0) {
      return new Expression_Tuple(_a0);
    }
    public static _IExpression create_New(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_New(path, typeArgs, args);
    }
    public static _IExpression create_NewArray(Dafny.ISequence<DAST._IExpression> dims, DAST._IType typ) {
      return new Expression_NewArray(dims, typ);
    }
    public static _IExpression create_DatatypeValue(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<Dafny.Rune> variant, bool isCo, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> contents) {
      return new Expression_DatatypeValue(path, typeArgs, variant, isCo, contents);
    }
    public static _IExpression create_Convert(DAST._IExpression @value, DAST._IType @from, DAST._IType typ) {
      return new Expression_Convert(@value, @from, typ);
    }
    public static _IExpression create_SeqConstruct(DAST._IExpression length, DAST._IExpression elem) {
      return new Expression_SeqConstruct(length, elem);
    }
    public static _IExpression create_SeqValue(Dafny.ISequence<DAST._IExpression> elements, DAST._IType typ) {
      return new Expression_SeqValue(elements, typ);
    }
    public static _IExpression create_SetValue(Dafny.ISequence<DAST._IExpression> elements) {
      return new Expression_SetValue(elements);
    }
    public static _IExpression create_MultisetValue(Dafny.ISequence<DAST._IExpression> elements) {
      return new Expression_MultisetValue(elements);
    }
    public static _IExpression create_MapValue(Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> mapElems) {
      return new Expression_MapValue(mapElems);
    }
    public static _IExpression create_MapBuilder(DAST._IType keyType, DAST._IType valueType) {
      return new Expression_MapBuilder(keyType, valueType);
    }
    public static _IExpression create_SeqUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value) {
      return new Expression_SeqUpdate(expr, indexExpr, @value);
    }
    public static _IExpression create_MapUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value) {
      return new Expression_MapUpdate(expr, indexExpr, @value);
    }
    public static _IExpression create_SetBuilder(DAST._IType elemType) {
      return new Expression_SetBuilder(elemType);
    }
    public static _IExpression create_ToMultiset(DAST._IExpression _a0) {
      return new Expression_ToMultiset(_a0);
    }
    public static _IExpression create_This() {
      return new Expression_This();
    }
    public static _IExpression create_Ite(DAST._IExpression cond, DAST._IExpression thn, DAST._IExpression els) {
      return new Expression_Ite(cond, thn, els);
    }
    public static _IExpression create_UnOp(DAST._IUnaryOp unOp, DAST._IExpression expr, DAST.Format._IUnaryOpFormat format1) {
      return new Expression_UnOp(unOp, expr, format1);
    }
    public static _IExpression create_BinOp(DAST._IBinOp op, DAST._IExpression left, DAST._IExpression right, DAST.Format._IBinaryOpFormat format2) {
      return new Expression_BinOp(op, left, right, format2);
    }
    public static _IExpression create_ArrayLen(DAST._IExpression expr, BigInteger dim) {
      return new Expression_ArrayLen(expr, dim);
    }
    public static _IExpression create_MapKeys(DAST._IExpression expr) {
      return new Expression_MapKeys(expr);
    }
    public static _IExpression create_MapValues(DAST._IExpression expr) {
      return new Expression_MapValues(expr);
    }
    public static _IExpression create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant, bool onDatatype) {
      return new Expression_Select(expr, field, isConstant, onDatatype);
    }
    public static _IExpression create_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, BigInteger arity) {
      return new Expression_SelectFn(expr, field, onDatatype, isStatic, arity);
    }
    public static _IExpression create_Index(DAST._IExpression expr, DAST._ICollKind collKind, Dafny.ISequence<DAST._IExpression> indices) {
      return new Expression_Index(expr, collKind, indices);
    }
    public static _IExpression create_IndexRange(DAST._IExpression expr, bool isArray, Std.Wrappers._IOption<DAST._IExpression> low, Std.Wrappers._IOption<DAST._IExpression> high) {
      return new Expression_IndexRange(expr, isArray, low, high);
    }
    public static _IExpression create_TupleSelect(DAST._IExpression expr, BigInteger index) {
      return new Expression_TupleSelect(expr, index);
    }
    public static _IExpression create_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_Call(@on, callName, typeArgs, args);
    }
    public static _IExpression create_Lambda(Dafny.ISequence<DAST._IFormal> @params, DAST._IType retType, Dafny.ISequence<DAST._IStatement> body) {
      return new Expression_Lambda(@params, retType, body);
    }
    public static _IExpression create_BetaRedex(Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> values, DAST._IType retType, DAST._IExpression expr) {
      return new Expression_BetaRedex(values, retType, expr);
    }
    public static _IExpression create_IIFE(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, DAST._IExpression @value, DAST._IExpression iifeBody) {
      return new Expression_IIFE(name, typ, @value, iifeBody);
    }
    public static _IExpression create_Apply(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_Apply(expr, args);
    }
    public static _IExpression create_TypeTest(DAST._IExpression @on, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dType, Dafny.ISequence<Dafny.Rune> variant) {
      return new Expression_TypeTest(@on, dType, variant);
    }
    public static _IExpression create_InitializationValue(DAST._IType typ) {
      return new Expression_InitializationValue(typ);
    }
    public static _IExpression create_BoolBoundedPool() {
      return new Expression_BoolBoundedPool();
    }
    public static _IExpression create_SetBoundedPool(DAST._IExpression of) {
      return new Expression_SetBoundedPool(of);
    }
    public static _IExpression create_SeqBoundedPool(DAST._IExpression of, bool includeDuplicates) {
      return new Expression_SeqBoundedPool(of, includeDuplicates);
    }
    public static _IExpression create_IntRange(DAST._IExpression lo, DAST._IExpression hi) {
      return new Expression_IntRange(lo, hi);
    }
    public bool is_Literal { get { return this is Expression_Literal; } }
    public bool is_Ident { get { return this is Expression_Ident; } }
    public bool is_Companion { get { return this is Expression_Companion; } }
    public bool is_Tuple { get { return this is Expression_Tuple; } }
    public bool is_New { get { return this is Expression_New; } }
    public bool is_NewArray { get { return this is Expression_NewArray; } }
    public bool is_DatatypeValue { get { return this is Expression_DatatypeValue; } }
    public bool is_Convert { get { return this is Expression_Convert; } }
    public bool is_SeqConstruct { get { return this is Expression_SeqConstruct; } }
    public bool is_SeqValue { get { return this is Expression_SeqValue; } }
    public bool is_SetValue { get { return this is Expression_SetValue; } }
    public bool is_MultisetValue { get { return this is Expression_MultisetValue; } }
    public bool is_MapValue { get { return this is Expression_MapValue; } }
    public bool is_MapBuilder { get { return this is Expression_MapBuilder; } }
    public bool is_SeqUpdate { get { return this is Expression_SeqUpdate; } }
    public bool is_MapUpdate { get { return this is Expression_MapUpdate; } }
    public bool is_SetBuilder { get { return this is Expression_SetBuilder; } }
    public bool is_ToMultiset { get { return this is Expression_ToMultiset; } }
    public bool is_This { get { return this is Expression_This; } }
    public bool is_Ite { get { return this is Expression_Ite; } }
    public bool is_UnOp { get { return this is Expression_UnOp; } }
    public bool is_BinOp { get { return this is Expression_BinOp; } }
    public bool is_ArrayLen { get { return this is Expression_ArrayLen; } }
    public bool is_MapKeys { get { return this is Expression_MapKeys; } }
    public bool is_MapValues { get { return this is Expression_MapValues; } }
    public bool is_Select { get { return this is Expression_Select; } }
    public bool is_SelectFn { get { return this is Expression_SelectFn; } }
    public bool is_Index { get { return this is Expression_Index; } }
    public bool is_IndexRange { get { return this is Expression_IndexRange; } }
    public bool is_TupleSelect { get { return this is Expression_TupleSelect; } }
    public bool is_Call { get { return this is Expression_Call; } }
    public bool is_Lambda { get { return this is Expression_Lambda; } }
    public bool is_BetaRedex { get { return this is Expression_BetaRedex; } }
    public bool is_IIFE { get { return this is Expression_IIFE; } }
    public bool is_Apply { get { return this is Expression_Apply; } }
    public bool is_TypeTest { get { return this is Expression_TypeTest; } }
    public bool is_InitializationValue { get { return this is Expression_InitializationValue; } }
    public bool is_BoolBoundedPool { get { return this is Expression_BoolBoundedPool; } }
    public bool is_SetBoundedPool { get { return this is Expression_SetBoundedPool; } }
    public bool is_SeqBoundedPool { get { return this is Expression_SeqBoundedPool; } }
    public bool is_IntRange { get { return this is Expression_IntRange; } }
    public DAST._ILiteral dtor_Literal_i_a0 {
      get {
        var d = this;
        return ((Expression_Literal)d)._i_a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_Ident_i_a0 {
      get {
        var d = this;
        return ((Expression_Ident)d)._i_a0;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Companion_i_a0 {
      get {
        var d = this;
        return ((Expression_Companion)d)._i_a0;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_Tuple_i_a0 {
      get {
        var d = this;
        return ((Expression_Tuple)d)._i_a0;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path {
      get {
        var d = this;
        if (d is Expression_New) { return ((Expression_New)d)._i_path; }
        return ((Expression_DatatypeValue)d)._i_path;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        if (d is Expression_New) { return ((Expression_New)d)._i_typeArgs; }
        if (d is Expression_DatatypeValue) { return ((Expression_DatatypeValue)d)._i_typeArgs; }
        return ((Expression_Call)d)._i_typeArgs;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_args {
      get {
        var d = this;
        if (d is Expression_New) { return ((Expression_New)d)._i_args; }
        if (d is Expression_Call) { return ((Expression_Call)d)._i_args; }
        return ((Expression_Apply)d)._i_args;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_dims {
      get {
        var d = this;
        return ((Expression_NewArray)d)._i_dims;
      }
    }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        if (d is Expression_NewArray) { return ((Expression_NewArray)d)._i_typ; }
        if (d is Expression_Convert) { return ((Expression_Convert)d)._i_typ; }
        if (d is Expression_SeqValue) { return ((Expression_SeqValue)d)._i_typ; }
        if (d is Expression_IIFE) { return ((Expression_IIFE)d)._i_typ; }
        return ((Expression_InitializationValue)d)._i_typ;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_variant {
      get {
        var d = this;
        if (d is Expression_DatatypeValue) { return ((Expression_DatatypeValue)d)._i_variant; }
        return ((Expression_TypeTest)d)._i_variant;
      }
    }
    public bool dtor_isCo {
      get {
        var d = this;
        return ((Expression_DatatypeValue)d)._i_isCo;
      }
    }
    public Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> dtor_contents {
      get {
        var d = this;
        return ((Expression_DatatypeValue)d)._i_contents;
      }
    }
    public DAST._IExpression dtor_value {
      get {
        var d = this;
        if (d is Expression_Convert) { return ((Expression_Convert)d)._i_value; }
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._i_value; }
        if (d is Expression_MapUpdate) { return ((Expression_MapUpdate)d)._i_value; }
        return ((Expression_IIFE)d)._i_value;
      }
    }
    public DAST._IType dtor_from {
      get {
        var d = this;
        return ((Expression_Convert)d)._i_from;
      }
    }
    public DAST._IExpression dtor_length {
      get {
        var d = this;
        return ((Expression_SeqConstruct)d)._i_length;
      }
    }
    public DAST._IExpression dtor_elem {
      get {
        var d = this;
        return ((Expression_SeqConstruct)d)._i_elem;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_elements {
      get {
        var d = this;
        if (d is Expression_SeqValue) { return ((Expression_SeqValue)d)._i_elements; }
        if (d is Expression_SetValue) { return ((Expression_SetValue)d)._i_elements; }
        return ((Expression_MultisetValue)d)._i_elements;
      }
    }
    public Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> dtor_mapElems {
      get {
        var d = this;
        return ((Expression_MapValue)d)._i_mapElems;
      }
    }
    public DAST._IType dtor_keyType {
      get {
        var d = this;
        return ((Expression_MapBuilder)d)._i_keyType;
      }
    }
    public DAST._IType dtor_valueType {
      get {
        var d = this;
        return ((Expression_MapBuilder)d)._i_valueType;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._i_expr; }
        if (d is Expression_MapUpdate) { return ((Expression_MapUpdate)d)._i_expr; }
        if (d is Expression_UnOp) { return ((Expression_UnOp)d)._i_expr; }
        if (d is Expression_ArrayLen) { return ((Expression_ArrayLen)d)._i_expr; }
        if (d is Expression_MapKeys) { return ((Expression_MapKeys)d)._i_expr; }
        if (d is Expression_MapValues) { return ((Expression_MapValues)d)._i_expr; }
        if (d is Expression_Select) { return ((Expression_Select)d)._i_expr; }
        if (d is Expression_SelectFn) { return ((Expression_SelectFn)d)._i_expr; }
        if (d is Expression_Index) { return ((Expression_Index)d)._i_expr; }
        if (d is Expression_IndexRange) { return ((Expression_IndexRange)d)._i_expr; }
        if (d is Expression_TupleSelect) { return ((Expression_TupleSelect)d)._i_expr; }
        if (d is Expression_BetaRedex) { return ((Expression_BetaRedex)d)._i_expr; }
        return ((Expression_Apply)d)._i_expr;
      }
    }
    public DAST._IExpression dtor_indexExpr {
      get {
        var d = this;
        if (d is Expression_SeqUpdate) { return ((Expression_SeqUpdate)d)._i_indexExpr; }
        return ((Expression_MapUpdate)d)._i_indexExpr;
      }
    }
    public DAST._IType dtor_elemType {
      get {
        var d = this;
        return ((Expression_SetBuilder)d)._i_elemType;
      }
    }
    public DAST._IExpression dtor_ToMultiset_i_a0 {
      get {
        var d = this;
        return ((Expression_ToMultiset)d)._i_a0;
      }
    }
    public DAST._IExpression dtor_cond {
      get {
        var d = this;
        return ((Expression_Ite)d)._i_cond;
      }
    }
    public DAST._IExpression dtor_thn {
      get {
        var d = this;
        return ((Expression_Ite)d)._i_thn;
      }
    }
    public DAST._IExpression dtor_els {
      get {
        var d = this;
        return ((Expression_Ite)d)._i_els;
      }
    }
    public DAST._IUnaryOp dtor_unOp {
      get {
        var d = this;
        return ((Expression_UnOp)d)._i_unOp;
      }
    }
    public DAST.Format._IUnaryOpFormat dtor_format1 {
      get {
        var d = this;
        return ((Expression_UnOp)d)._i_format1;
      }
    }
    public DAST._IBinOp dtor_op {
      get {
        var d = this;
        return ((Expression_BinOp)d)._i_op;
      }
    }
    public DAST._IExpression dtor_left {
      get {
        var d = this;
        return ((Expression_BinOp)d)._i_left;
      }
    }
    public DAST._IExpression dtor_right {
      get {
        var d = this;
        return ((Expression_BinOp)d)._i_right;
      }
    }
    public DAST.Format._IBinaryOpFormat dtor_format2 {
      get {
        var d = this;
        return ((Expression_BinOp)d)._i_format2;
      }
    }
    public BigInteger dtor_dim {
      get {
        var d = this;
        return ((Expression_ArrayLen)d)._i_dim;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        if (d is Expression_Select) { return ((Expression_Select)d)._i_field; }
        return ((Expression_SelectFn)d)._i_field;
      }
    }
    public bool dtor_isConstant {
      get {
        var d = this;
        return ((Expression_Select)d)._i_isConstant;
      }
    }
    public bool dtor_onDatatype {
      get {
        var d = this;
        if (d is Expression_Select) { return ((Expression_Select)d)._i_onDatatype; }
        return ((Expression_SelectFn)d)._i_onDatatype;
      }
    }
    public bool dtor_isStatic {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._i_isStatic;
      }
    }
    public BigInteger dtor_arity {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._i_arity;
      }
    }
    public DAST._ICollKind dtor_collKind {
      get {
        var d = this;
        return ((Expression_Index)d)._i_collKind;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_indices {
      get {
        var d = this;
        return ((Expression_Index)d)._i_indices;
      }
    }
    public bool dtor_isArray {
      get {
        var d = this;
        return ((Expression_IndexRange)d)._i_isArray;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_low {
      get {
        var d = this;
        return ((Expression_IndexRange)d)._i_low;
      }
    }
    public Std.Wrappers._IOption<DAST._IExpression> dtor_high {
      get {
        var d = this;
        return ((Expression_IndexRange)d)._i_high;
      }
    }
    public BigInteger dtor_index {
      get {
        var d = this;
        return ((Expression_TupleSelect)d)._i_index;
      }
    }
    public DAST._IExpression dtor_on {
      get {
        var d = this;
        if (d is Expression_Call) { return ((Expression_Call)d)._i_on; }
        return ((Expression_TypeTest)d)._i_on;
      }
    }
    public DAST._ICallName dtor_callName {
      get {
        var d = this;
        return ((Expression_Call)d)._i_callName;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_params {
      get {
        var d = this;
        return ((Expression_Lambda)d)._i_params;
      }
    }
    public DAST._IType dtor_retType {
      get {
        var d = this;
        if (d is Expression_Lambda) { return ((Expression_Lambda)d)._i_retType; }
        return ((Expression_BetaRedex)d)._i_retType;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        var d = this;
        return ((Expression_Lambda)d)._i_body;
      }
    }
    public Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> dtor_values {
      get {
        var d = this;
        return ((Expression_BetaRedex)d)._i_values;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((Expression_IIFE)d)._i_name;
      }
    }
    public DAST._IExpression dtor_iifeBody {
      get {
        var d = this;
        return ((Expression_IIFE)d)._i_iifeBody;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_dType {
      get {
        var d = this;
        return ((Expression_TypeTest)d)._i_dType;
      }
    }
    public DAST._IExpression dtor_of {
      get {
        var d = this;
        if (d is Expression_SetBoundedPool) { return ((Expression_SetBoundedPool)d)._i_of; }
        return ((Expression_SeqBoundedPool)d)._i_of;
      }
    }
    public bool dtor_includeDuplicates {
      get {
        var d = this;
        return ((Expression_SeqBoundedPool)d)._i_includeDuplicates;
      }
    }
    public DAST._IExpression dtor_lo {
      get {
        var d = this;
        return ((Expression_IntRange)d)._i_lo;
      }
    }
    public DAST._IExpression dtor_hi {
      get {
        var d = this;
        return ((Expression_IntRange)d)._i_hi;
      }
    }
    public abstract _IExpression DowncastClone();
  }
  public class Expression_Literal : Expression {
    public readonly DAST._ILiteral _i_a0;
    public Expression_Literal(DAST._ILiteral _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Literal(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Literal;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Literal";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Expression_Ident : Expression {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public Expression_Ident(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Ident(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Ident;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Ident";
      s += "(";
      s += this._i_a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expression_Companion : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_a0;
    public Expression_Companion(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Companion(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Companion;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Companion";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Expression_Tuple : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _i_a0;
    public Expression_Tuple(Dafny.ISequence<DAST._IExpression> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Tuple(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Tuple;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Tuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Expression_New : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_path;
    public readonly Dafny.ISequence<DAST._IType> _i_typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _i_args;
    public Expression_New(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._i_path = path;
      this._i_typeArgs = typeArgs;
      this._i_args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_New(_i_path, _i_typeArgs, _i_args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_New;
      return oth != null && object.Equals(this._i_path, oth._i_path) && object.Equals(this._i_typeArgs, oth._i_typeArgs) && object.Equals(this._i_args, oth._i_args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_path));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_args));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.New";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_path);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_args);
      s += ")";
      return s;
    }
  }
  public class Expression_NewArray : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _i_dims;
    public readonly DAST._IType _i_typ;
    public Expression_NewArray(Dafny.ISequence<DAST._IExpression> dims, DAST._IType typ) : base() {
      this._i_dims = dims;
      this._i_typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_NewArray(_i_dims, _i_typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_NewArray;
      return oth != null && object.Equals(this._i_dims, oth._i_dims) && object.Equals(this._i_typ, oth._i_typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_dims));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.NewArray";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_dims);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typ);
      s += ")";
      return s;
    }
  }
  public class Expression_DatatypeValue : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_path;
    public readonly Dafny.ISequence<DAST._IType> _i_typeArgs;
    public readonly Dafny.ISequence<Dafny.Rune> _i_variant;
    public readonly bool _i_isCo;
    public readonly Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _i_contents;
    public Expression_DatatypeValue(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<Dafny.Rune> variant, bool isCo, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> contents) : base() {
      this._i_path = path;
      this._i_typeArgs = typeArgs;
      this._i_variant = variant;
      this._i_isCo = isCo;
      this._i_contents = contents;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_DatatypeValue(_i_path, _i_typeArgs, _i_variant, _i_isCo, _i_contents);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_DatatypeValue;
      return oth != null && object.Equals(this._i_path, oth._i_path) && object.Equals(this._i_typeArgs, oth._i_typeArgs) && object.Equals(this._i_variant, oth._i_variant) && this._i_isCo == oth._i_isCo && object.Equals(this._i_contents, oth._i_contents);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_path));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_variant));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_isCo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_contents));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.DatatypeValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_path);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeArgs);
      s += ", ";
      s += this._i_variant.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_isCo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_contents);
      s += ")";
      return s;
    }
  }
  public class Expression_Convert : Expression {
    public readonly DAST._IExpression _i_value;
    public readonly DAST._IType _i_from;
    public readonly DAST._IType _i_typ;
    public Expression_Convert(DAST._IExpression @value, DAST._IType @from, DAST._IType typ) : base() {
      this._i_value = @value;
      this._i_from = @from;
      this._i_typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Convert(_i_value, _i_from, _i_typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Convert;
      return oth != null && object.Equals(this._i_value, oth._i_value) && object.Equals(this._i_from, oth._i_from) && object.Equals(this._i_typ, oth._i_typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_from));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Convert";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_from);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typ);
      s += ")";
      return s;
    }
  }
  public class Expression_SeqConstruct : Expression {
    public readonly DAST._IExpression _i_length;
    public readonly DAST._IExpression _i_elem;
    public Expression_SeqConstruct(DAST._IExpression length, DAST._IExpression elem) : base() {
      this._i_length = length;
      this._i_elem = elem;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqConstruct(_i_length, _i_elem);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqConstruct;
      return oth != null && object.Equals(this._i_length, oth._i_length) && object.Equals(this._i_elem, oth._i_elem);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_length));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_elem));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqConstruct";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_length);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_elem);
      s += ")";
      return s;
    }
  }
  public class Expression_SeqValue : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _i_elements;
    public readonly DAST._IType _i_typ;
    public Expression_SeqValue(Dafny.ISequence<DAST._IExpression> elements, DAST._IType typ) : base() {
      this._i_elements = elements;
      this._i_typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqValue(_i_elements, _i_typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqValue;
      return oth != null && object.Equals(this._i_elements, oth._i_elements) && object.Equals(this._i_typ, oth._i_typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_elements));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_elements);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typ);
      s += ")";
      return s;
    }
  }
  public class Expression_SetValue : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _i_elements;
    public Expression_SetValue(Dafny.ISequence<DAST._IExpression> elements) : base() {
      this._i_elements = elements;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SetValue(_i_elements);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SetValue;
      return oth != null && object.Equals(this._i_elements, oth._i_elements);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_elements));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SetValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_elements);
      s += ")";
      return s;
    }
  }
  public class Expression_MultisetValue : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _i_elements;
    public Expression_MultisetValue(Dafny.ISequence<DAST._IExpression> elements) : base() {
      this._i_elements = elements;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MultisetValue(_i_elements);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MultisetValue;
      return oth != null && object.Equals(this._i_elements, oth._i_elements);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_elements));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MultisetValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_elements);
      s += ")";
      return s;
    }
  }
  public class Expression_MapValue : Expression {
    public readonly Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _i_mapElems;
    public Expression_MapValue(Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> mapElems) : base() {
      this._i_mapElems = mapElems;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapValue(_i_mapElems);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapValue;
      return oth != null && object.Equals(this._i_mapElems, oth._i_mapElems);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_mapElems));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_mapElems);
      s += ")";
      return s;
    }
  }
  public class Expression_MapBuilder : Expression {
    public readonly DAST._IType _i_keyType;
    public readonly DAST._IType _i_valueType;
    public Expression_MapBuilder(DAST._IType keyType, DAST._IType valueType) : base() {
      this._i_keyType = keyType;
      this._i_valueType = valueType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapBuilder(_i_keyType, _i_valueType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapBuilder;
      return oth != null && object.Equals(this._i_keyType, oth._i_keyType) && object.Equals(this._i_valueType, oth._i_valueType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_keyType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_valueType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapBuilder";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_keyType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_valueType);
      s += ")";
      return s;
    }
  }
  public class Expression_SeqUpdate : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly DAST._IExpression _i_indexExpr;
    public readonly DAST._IExpression _i_value;
    public Expression_SeqUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value) : base() {
      this._i_expr = expr;
      this._i_indexExpr = indexExpr;
      this._i_value = @value;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqUpdate(_i_expr, _i_indexExpr, _i_value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqUpdate;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_indexExpr, oth._i_indexExpr) && object.Equals(this._i_value, oth._i_value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_indexExpr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqUpdate";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_indexExpr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_value);
      s += ")";
      return s;
    }
  }
  public class Expression_MapUpdate : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly DAST._IExpression _i_indexExpr;
    public readonly DAST._IExpression _i_value;
    public Expression_MapUpdate(DAST._IExpression expr, DAST._IExpression indexExpr, DAST._IExpression @value) : base() {
      this._i_expr = expr;
      this._i_indexExpr = indexExpr;
      this._i_value = @value;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapUpdate(_i_expr, _i_indexExpr, _i_value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapUpdate;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_indexExpr, oth._i_indexExpr) && object.Equals(this._i_value, oth._i_value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_indexExpr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapUpdate";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_indexExpr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_value);
      s += ")";
      return s;
    }
  }
  public class Expression_SetBuilder : Expression {
    public readonly DAST._IType _i_elemType;
    public Expression_SetBuilder(DAST._IType elemType) : base() {
      this._i_elemType = elemType;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SetBuilder(_i_elemType);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SetBuilder;
      return oth != null && object.Equals(this._i_elemType, oth._i_elemType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_elemType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SetBuilder";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_elemType);
      s += ")";
      return s;
    }
  }
  public class Expression_ToMultiset : Expression {
    public readonly DAST._IExpression _i_a0;
    public Expression_ToMultiset(DAST._IExpression _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ToMultiset(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ToMultiset;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ToMultiset";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Expression_This : Expression {
    public Expression_This() : base() {
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_This();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_This;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.This";
      return s;
    }
  }
  public class Expression_Ite : Expression {
    public readonly DAST._IExpression _i_cond;
    public readonly DAST._IExpression _i_thn;
    public readonly DAST._IExpression _i_els;
    public Expression_Ite(DAST._IExpression cond, DAST._IExpression thn, DAST._IExpression els) : base() {
      this._i_cond = cond;
      this._i_thn = thn;
      this._i_els = els;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Ite(_i_cond, _i_thn, _i_els);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Ite;
      return oth != null && object.Equals(this._i_cond, oth._i_cond) && object.Equals(this._i_thn, oth._i_thn) && object.Equals(this._i_els, oth._i_els);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_els));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Ite";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_thn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_els);
      s += ")";
      return s;
    }
  }
  public class Expression_UnOp : Expression {
    public readonly DAST._IUnaryOp _i_unOp;
    public readonly DAST._IExpression _i_expr;
    public readonly DAST.Format._IUnaryOpFormat _i_format1;
    public Expression_UnOp(DAST._IUnaryOp unOp, DAST._IExpression expr, DAST.Format._IUnaryOpFormat format1) : base() {
      this._i_unOp = unOp;
      this._i_expr = expr;
      this._i_format1 = format1;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_UnOp(_i_unOp, _i_expr, _i_format1);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_UnOp;
      return oth != null && object.Equals(this._i_unOp, oth._i_unOp) && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_format1, oth._i_format1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_unOp));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_format1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.UnOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_unOp);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_format1);
      s += ")";
      return s;
    }
  }
  public class Expression_BinOp : Expression {
    public readonly DAST._IBinOp _i_op;
    public readonly DAST._IExpression _i_left;
    public readonly DAST._IExpression _i_right;
    public readonly DAST.Format._IBinaryOpFormat _i_format2;
    public Expression_BinOp(DAST._IBinOp op, DAST._IExpression left, DAST._IExpression right, DAST.Format._IBinaryOpFormat format2) : base() {
      this._i_op = op;
      this._i_left = left;
      this._i_right = right;
      this._i_format2 = format2;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_BinOp(_i_op, _i_left, _i_right, _i_format2);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_BinOp;
      return oth != null && object.Equals(this._i_op, oth._i_op) && object.Equals(this._i_left, oth._i_left) && object.Equals(this._i_right, oth._i_right) && object.Equals(this._i_format2, oth._i_format2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_op));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_right));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_format2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BinOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_op);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_right);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_format2);
      s += ")";
      return s;
    }
  }
  public class Expression_ArrayLen : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly BigInteger _i_dim;
    public Expression_ArrayLen(DAST._IExpression expr, BigInteger dim) : base() {
      this._i_expr = expr;
      this._i_dim = dim;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ArrayLen(_i_expr, _i_dim);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ArrayLen;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && this._i_dim == oth._i_dim;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_dim));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ArrayLen";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_dim);
      s += ")";
      return s;
    }
  }
  public class Expression_MapKeys : Expression {
    public readonly DAST._IExpression _i_expr;
    public Expression_MapKeys(DAST._IExpression expr) : base() {
      this._i_expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapKeys(_i_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapKeys;
      return oth != null && object.Equals(this._i_expr, oth._i_expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapKeys";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ")";
      return s;
    }
  }
  public class Expression_MapValues : Expression {
    public readonly DAST._IExpression _i_expr;
    public Expression_MapValues(DAST._IExpression expr) : base() {
      this._i_expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapValues(_i_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapValues;
      return oth != null && object.Equals(this._i_expr, oth._i_expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapValues";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ")";
      return s;
    }
  }
  public class Expression_Select : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly Dafny.ISequence<Dafny.Rune> _i_field;
    public readonly bool _i_isConstant;
    public readonly bool _i_onDatatype;
    public Expression_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant, bool onDatatype) : base() {
      this._i_expr = expr;
      this._i_field = field;
      this._i_isConstant = isConstant;
      this._i_onDatatype = onDatatype;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Select(_i_expr, _i_field, _i_isConstant, _i_onDatatype);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Select;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_field, oth._i_field) && this._i_isConstant == oth._i_isConstant && this._i_onDatatype == oth._i_onDatatype;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_field));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_isConstant));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_onDatatype));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += this._i_field.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_isConstant);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_onDatatype);
      s += ")";
      return s;
    }
  }
  public class Expression_SelectFn : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly Dafny.ISequence<Dafny.Rune> _i_field;
    public readonly bool _i_onDatatype;
    public readonly bool _i_isStatic;
    public readonly BigInteger _i_arity;
    public Expression_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, BigInteger arity) : base() {
      this._i_expr = expr;
      this._i_field = field;
      this._i_onDatatype = onDatatype;
      this._i_isStatic = isStatic;
      this._i_arity = arity;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SelectFn(_i_expr, _i_field, _i_onDatatype, _i_isStatic, _i_arity);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SelectFn;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_field, oth._i_field) && this._i_onDatatype == oth._i_onDatatype && this._i_isStatic == oth._i_isStatic && this._i_arity == oth._i_arity;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_field));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_onDatatype));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_isStatic));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_arity));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SelectFn";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += this._i_field.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_onDatatype);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_isStatic);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_arity);
      s += ")";
      return s;
    }
  }
  public class Expression_Index : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly DAST._ICollKind _i_collKind;
    public readonly Dafny.ISequence<DAST._IExpression> _i_indices;
    public Expression_Index(DAST._IExpression expr, DAST._ICollKind collKind, Dafny.ISequence<DAST._IExpression> indices) : base() {
      this._i_expr = expr;
      this._i_collKind = collKind;
      this._i_indices = indices;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Index(_i_expr, _i_collKind, _i_indices);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Index;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_collKind, oth._i_collKind) && object.Equals(this._i_indices, oth._i_indices);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 27;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_collKind));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_indices));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_collKind);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_indices);
      s += ")";
      return s;
    }
  }
  public class Expression_IndexRange : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly bool _i_isArray;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _i_low;
    public readonly Std.Wrappers._IOption<DAST._IExpression> _i_high;
    public Expression_IndexRange(DAST._IExpression expr, bool isArray, Std.Wrappers._IOption<DAST._IExpression> low, Std.Wrappers._IOption<DAST._IExpression> high) : base() {
      this._i_expr = expr;
      this._i_isArray = isArray;
      this._i_low = low;
      this._i_high = high;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IndexRange(_i_expr, _i_isArray, _i_low, _i_high);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IndexRange;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && this._i_isArray == oth._i_isArray && object.Equals(this._i_low, oth._i_low) && object.Equals(this._i_high, oth._i_high);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_isArray));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_low));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_high));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IndexRange";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_isArray);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_low);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_high);
      s += ")";
      return s;
    }
  }
  public class Expression_TupleSelect : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly BigInteger _i_index;
    public Expression_TupleSelect(DAST._IExpression expr, BigInteger index) : base() {
      this._i_expr = expr;
      this._i_index = index;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_TupleSelect(_i_expr, _i_index);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_TupleSelect;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && this._i_index == oth._i_index;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 29;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_index));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.TupleSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_index);
      s += ")";
      return s;
    }
  }
  public class Expression_Call : Expression {
    public readonly DAST._IExpression _i_on;
    public readonly DAST._ICallName _i_callName;
    public readonly Dafny.ISequence<DAST._IType> _i_typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _i_args;
    public Expression_Call(DAST._IExpression @on, DAST._ICallName callName, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._i_on = @on;
      this._i_callName = callName;
      this._i_typeArgs = typeArgs;
      this._i_args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Call(_i_on, _i_callName, _i_typeArgs, _i_args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Call;
      return oth != null && object.Equals(this._i_on, oth._i_on) && object.Equals(this._i_callName, oth._i_callName) && object.Equals(this._i_typeArgs, oth._i_typeArgs) && object.Equals(this._i_args, oth._i_args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_callName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_args));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_callName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_args);
      s += ")";
      return s;
    }
  }
  public class Expression_Lambda : Expression {
    public readonly Dafny.ISequence<DAST._IFormal> _i_params;
    public readonly DAST._IType _i_retType;
    public readonly Dafny.ISequence<DAST._IStatement> _i_body;
    public Expression_Lambda(Dafny.ISequence<DAST._IFormal> @params, DAST._IType retType, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._i_params = @params;
      this._i_retType = retType;
      this._i_body = body;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Lambda(_i_params, _i_retType, _i_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Lambda;
      return oth != null && object.Equals(this._i_params, oth._i_params) && object.Equals(this._i_retType, oth._i_retType) && object.Equals(this._i_body, oth._i_body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 31;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Lambda";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_params);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_retType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_body);
      s += ")";
      return s;
    }
  }
  public class Expression_BetaRedex : Expression {
    public readonly Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _i_values;
    public readonly DAST._IType _i_retType;
    public readonly DAST._IExpression _i_expr;
    public Expression_BetaRedex(Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> values, DAST._IType retType, DAST._IExpression expr) : base() {
      this._i_values = values;
      this._i_retType = retType;
      this._i_expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_BetaRedex(_i_values, _i_retType, _i_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_BetaRedex;
      return oth != null && object.Equals(this._i_values, oth._i_values) && object.Equals(this._i_retType, oth._i_retType) && object.Equals(this._i_expr, oth._i_expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 32;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_values));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BetaRedex";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_values);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_retType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ")";
      return s;
    }
  }
  public class Expression_IIFE : Expression {
    public readonly Dafny.ISequence<Dafny.Rune> _i_name;
    public readonly DAST._IType _i_typ;
    public readonly DAST._IExpression _i_value;
    public readonly DAST._IExpression _i_iifeBody;
    public Expression_IIFE(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, DAST._IExpression @value, DAST._IExpression iifeBody) : base() {
      this._i_name = name;
      this._i_typ = typ;
      this._i_value = @value;
      this._i_iifeBody = iifeBody;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IIFE(_i_name, _i_typ, _i_value, _i_iifeBody);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IIFE;
      return oth != null && object.Equals(this._i_name, oth._i_name) && object.Equals(this._i_typ, oth._i_typ) && object.Equals(this._i_value, oth._i_value) && object.Equals(this._i_iifeBody, oth._i_iifeBody);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 33;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typ));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_iifeBody));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IIFE";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_typ);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_iifeBody);
      s += ")";
      return s;
    }
  }
  public class Expression_Apply : Expression {
    public readonly DAST._IExpression _i_expr;
    public readonly Dafny.ISequence<DAST._IExpression> _i_args;
    public Expression_Apply(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._i_expr = expr;
      this._i_args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Apply(_i_expr, _i_args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Apply;
      return oth != null && object.Equals(this._i_expr, oth._i_expr) && object.Equals(this._i_args, oth._i_args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 34;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_args));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Apply";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_args);
      s += ")";
      return s;
    }
  }
  public class Expression_TypeTest : Expression {
    public readonly DAST._IExpression _i_on;
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _i_dType;
    public readonly Dafny.ISequence<Dafny.Rune> _i_variant;
    public Expression_TypeTest(DAST._IExpression @on, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dType, Dafny.ISequence<Dafny.Rune> variant) : base() {
      this._i_on = @on;
      this._i_dType = dType;
      this._i_variant = variant;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_TypeTest(_i_on, _i_dType, _i_variant);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_TypeTest;
      return oth != null && object.Equals(this._i_on, oth._i_on) && object.Equals(this._i_dType, oth._i_dType) && object.Equals(this._i_variant, oth._i_variant);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 35;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_dType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_variant));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.TypeTest";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_dType);
      s += ", ";
      s += this._i_variant.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expression_InitializationValue : Expression {
    public readonly DAST._IType _i_typ;
    public Expression_InitializationValue(DAST._IType typ) : base() {
      this._i_typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_InitializationValue(_i_typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_InitializationValue;
      return oth != null && object.Equals(this._i_typ, oth._i_typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 36;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_typ));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.InitializationValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_typ);
      s += ")";
      return s;
    }
  }
  public class Expression_BoolBoundedPool : Expression {
    public Expression_BoolBoundedPool() : base() {
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_BoolBoundedPool();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_BoolBoundedPool;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 37;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BoolBoundedPool";
      return s;
    }
  }
  public class Expression_SetBoundedPool : Expression {
    public readonly DAST._IExpression _i_of;
    public Expression_SetBoundedPool(DAST._IExpression of) : base() {
      this._i_of = of;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SetBoundedPool(_i_of);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SetBoundedPool;
      return oth != null && object.Equals(this._i_of, oth._i_of);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 38;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_of));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SetBoundedPool";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_of);
      s += ")";
      return s;
    }
  }
  public class Expression_SeqBoundedPool : Expression {
    public readonly DAST._IExpression _i_of;
    public readonly bool _i_includeDuplicates;
    public Expression_SeqBoundedPool(DAST._IExpression of, bool includeDuplicates) : base() {
      this._i_of = of;
      this._i_includeDuplicates = includeDuplicates;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqBoundedPool(_i_of, _i_includeDuplicates);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqBoundedPool;
      return oth != null && object.Equals(this._i_of, oth._i_of) && this._i_includeDuplicates == oth._i_includeDuplicates;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 39;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_of));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_includeDuplicates));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqBoundedPool";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_of);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_includeDuplicates);
      s += ")";
      return s;
    }
  }
  public class Expression_IntRange : Expression {
    public readonly DAST._IExpression _i_lo;
    public readonly DAST._IExpression _i_hi;
    public Expression_IntRange(DAST._IExpression lo, DAST._IExpression hi) : base() {
      this._i_lo = lo;
      this._i_hi = hi;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IntRange(_i_lo, _i_hi);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IntRange;
      return oth != null && object.Equals(this._i_lo, oth._i_lo) && object.Equals(this._i_hi, oth._i_hi);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 40;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_lo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_hi));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IntRange";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_lo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_hi);
      s += ")";
      return s;
    }
  }

  public interface _IUnaryOp {
    bool is_Not { get; }
    bool is_BitwiseNot { get; }
    bool is_Cardinality { get; }
    _IUnaryOp DowncastClone();
  }
  public abstract class UnaryOp : _IUnaryOp {
    public UnaryOp() {
    }
    private static readonly DAST._IUnaryOp theDefault = create_Not();
    public static DAST._IUnaryOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IUnaryOp> _TYPE = new Dafny.TypeDescriptor<DAST._IUnaryOp>(DAST.UnaryOp.Default());
    public static Dafny.TypeDescriptor<DAST._IUnaryOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUnaryOp create_Not() {
      return new UnaryOp_Not();
    }
    public static _IUnaryOp create_BitwiseNot() {
      return new UnaryOp_BitwiseNot();
    }
    public static _IUnaryOp create_Cardinality() {
      return new UnaryOp_Cardinality();
    }
    public bool is_Not { get { return this is UnaryOp_Not; } }
    public bool is_BitwiseNot { get { return this is UnaryOp_BitwiseNot; } }
    public bool is_Cardinality { get { return this is UnaryOp_Cardinality; } }
    public static System.Collections.Generic.IEnumerable<_IUnaryOp> AllSingletonConstructors {
      get {
        yield return UnaryOp.create_Not();
        yield return UnaryOp.create_BitwiseNot();
        yield return UnaryOp.create_Cardinality();
      }
    }
    public abstract _IUnaryOp DowncastClone();
  }
  public class UnaryOp_Not : UnaryOp {
    public UnaryOp_Not() : base() {
    }
    public override _IUnaryOp DowncastClone() {
      if (this is _IUnaryOp dt) { return dt; }
      return new UnaryOp_Not();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.UnaryOp_Not;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.UnaryOp.Not";
      return s;
    }
  }
  public class UnaryOp_BitwiseNot : UnaryOp {
    public UnaryOp_BitwiseNot() : base() {
    }
    public override _IUnaryOp DowncastClone() {
      if (this is _IUnaryOp dt) { return dt; }
      return new UnaryOp_BitwiseNot();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.UnaryOp_BitwiseNot;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.UnaryOp.BitwiseNot";
      return s;
    }
  }
  public class UnaryOp_Cardinality : UnaryOp {
    public UnaryOp_Cardinality() : base() {
    }
    public override _IUnaryOp DowncastClone() {
      if (this is _IUnaryOp dt) { return dt; }
      return new UnaryOp_Cardinality();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.UnaryOp_Cardinality;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.UnaryOp.Cardinality";
      return s;
    }
  }

  public interface _ILiteral {
    bool is_BoolLiteral { get; }
    bool is_IntLiteral { get; }
    bool is_DecLiteral { get; }
    bool is_StringLiteral { get; }
    bool is_CharLiteral { get; }
    bool is_Null { get; }
    bool dtor_BoolLiteral_i_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_IntLiteral_i_a0 { get; }
    DAST._IType dtor_IntLiteral_i_a1 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_i_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_i_a1 { get; }
    DAST._IType dtor_DecLiteral_i_a2 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_StringLiteral_i_a0 { get; }
    Dafny.Rune dtor_CharLiteral_i_a0 { get; }
    DAST._IType dtor_Null_i_a0 { get; }
    _ILiteral DowncastClone();
  }
  public abstract class Literal : _ILiteral {
    public Literal() {
    }
    private static readonly DAST._ILiteral theDefault = create_BoolLiteral(false);
    public static DAST._ILiteral Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._ILiteral> _TYPE = new Dafny.TypeDescriptor<DAST._ILiteral>(DAST.Literal.Default());
    public static Dafny.TypeDescriptor<DAST._ILiteral> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ILiteral create_BoolLiteral(bool _a0) {
      return new Literal_BoolLiteral(_a0);
    }
    public static _ILiteral create_IntLiteral(Dafny.ISequence<Dafny.Rune> _a0, DAST._IType _a1) {
      return new Literal_IntLiteral(_a0, _a1);
    }
    public static _ILiteral create_DecLiteral(Dafny.ISequence<Dafny.Rune> _a0, Dafny.ISequence<Dafny.Rune> _a1, DAST._IType _a2) {
      return new Literal_DecLiteral(_a0, _a1, _a2);
    }
    public static _ILiteral create_StringLiteral(Dafny.ISequence<Dafny.Rune> _a0) {
      return new Literal_StringLiteral(_a0);
    }
    public static _ILiteral create_CharLiteral(Dafny.Rune _a0) {
      return new Literal_CharLiteral(_a0);
    }
    public static _ILiteral create_Null(DAST._IType _a0) {
      return new Literal_Null(_a0);
    }
    public bool is_BoolLiteral { get { return this is Literal_BoolLiteral; } }
    public bool is_IntLiteral { get { return this is Literal_IntLiteral; } }
    public bool is_DecLiteral { get { return this is Literal_DecLiteral; } }
    public bool is_StringLiteral { get { return this is Literal_StringLiteral; } }
    public bool is_CharLiteral { get { return this is Literal_CharLiteral; } }
    public bool is_Null { get { return this is Literal_Null; } }
    public bool dtor_BoolLiteral_i_a0 {
      get {
        var d = this;
        return ((Literal_BoolLiteral)d)._i_a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_IntLiteral_i_a0 {
      get {
        var d = this;
        return ((Literal_IntLiteral)d)._i_a0;
      }
    }
    public DAST._IType dtor_IntLiteral_i_a1 {
      get {
        var d = this;
        return ((Literal_IntLiteral)d)._i_a1;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_i_a0 {
      get {
        var d = this;
        return ((Literal_DecLiteral)d)._i_a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_i_a1 {
      get {
        var d = this;
        return ((Literal_DecLiteral)d)._i_a1;
      }
    }
    public DAST._IType dtor_DecLiteral_i_a2 {
      get {
        var d = this;
        return ((Literal_DecLiteral)d)._i_a2;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_StringLiteral_i_a0 {
      get {
        var d = this;
        return ((Literal_StringLiteral)d)._i_a0;
      }
    }
    public Dafny.Rune dtor_CharLiteral_i_a0 {
      get {
        var d = this;
        return ((Literal_CharLiteral)d)._i_a0;
      }
    }
    public DAST._IType dtor_Null_i_a0 {
      get {
        var d = this;
        return ((Literal_Null)d)._i_a0;
      }
    }
    public abstract _ILiteral DowncastClone();
  }
  public class Literal_BoolLiteral : Literal {
    public readonly bool _i_a0;
    public Literal_BoolLiteral(bool _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_BoolLiteral(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_BoolLiteral;
      return oth != null && this._i_a0 == oth._i_a0;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.BoolLiteral";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Literal_IntLiteral : Literal {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public readonly DAST._IType _i_a1;
    public Literal_IntLiteral(Dafny.ISequence<Dafny.Rune> _a0, DAST._IType _a1) : base() {
      this._i_a0 = _a0;
      this._i_a1 = _a1;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_IntLiteral(_i_a0, _i_a1);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_IntLiteral;
      return oth != null && object.Equals(this._i_a0, oth._i_a0) && object.Equals(this._i_a1, oth._i_a1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.IntLiteral";
      s += "(";
      s += this._i_a0.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_a1);
      s += ")";
      return s;
    }
  }
  public class Literal_DecLiteral : Literal {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public readonly Dafny.ISequence<Dafny.Rune> _i_a1;
    public readonly DAST._IType _i_a2;
    public Literal_DecLiteral(Dafny.ISequence<Dafny.Rune> _a0, Dafny.ISequence<Dafny.Rune> _a1, DAST._IType _a2) : base() {
      this._i_a0 = _a0;
      this._i_a1 = _a1;
      this._i_a2 = _a2;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_DecLiteral(_i_a0, _i_a1, _i_a2);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_DecLiteral;
      return oth != null && object.Equals(this._i_a0, oth._i_a0) && object.Equals(this._i_a1, oth._i_a1) && object.Equals(this._i_a2, oth._i_a2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.DecLiteral";
      s += "(";
      s += this._i_a0.ToVerbatimString(true);
      s += ", ";
      s += this._i_a1.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._i_a2);
      s += ")";
      return s;
    }
  }
  public class Literal_StringLiteral : Literal {
    public readonly Dafny.ISequence<Dafny.Rune> _i_a0;
    public Literal_StringLiteral(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_StringLiteral(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_StringLiteral;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.StringLiteral";
      s += "(";
      s += this._i_a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Literal_CharLiteral : Literal {
    public readonly Dafny.Rune _i_a0;
    public Literal_CharLiteral(Dafny.Rune _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_CharLiteral(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_CharLiteral;
      return oth != null && this._i_a0 == oth._i_a0;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.CharLiteral";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
  public class Literal_Null : Literal {
    public readonly DAST._IType _i_a0;
    public Literal_Null(DAST._IType _a0) : base() {
      this._i_a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_Null(_i_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_Null;
      return oth != null && object.Equals(this._i_a0, oth._i_a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i_a0));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.Null";
      s += "(";
      s += Dafny.Helpers.ToString(this._i_a0);
      s += ")";
      return s;
    }
  }
} // end of namespace DAST