// Dafny program Dafny-compiler-rust.dfy compiled into C#
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
    Dafny.ISequence<DAST._IModuleItem> dtor_body { get; }
    _IModule DowncastClone();
  }
  public class Module : _IModule {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IModuleItem> _body;
    public Module(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IModuleItem> body) {
      this._name = name;
      this._body = body;
    }
    public _IModule DowncastClone() {
      if (this is _IModule dt) { return dt; }
      return new Module(_name, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Module;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Module.Module";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
    private static readonly DAST._IModule theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IModuleItem>.Empty);
    public static DAST._IModule Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IModule> _TYPE = new Dafny.TypeDescriptor<DAST._IModule>(DAST.Module.Default());
    public static Dafny.TypeDescriptor<DAST._IModule> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IModule create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IModuleItem> body) {
      return new Module(name, body);
    }
    public static _IModule create_Module(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IModuleItem> body) {
      return create(name, body);
    }
    public bool is_Module { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._IModuleItem> dtor_body {
      get {
        return this._body;
      }
    }
  }

  public interface _IModuleItem {
    bool is_Module { get; }
    bool is_Class { get; }
    bool is_Trait { get; }
    bool is_Newtype { get; }
    bool is_Datatype { get; }
    DAST._IModule dtor_Module_a0 { get; }
    DAST._IClass dtor_Class_a0 { get; }
    DAST._ITrait dtor_Trait_a0 { get; }
    DAST._INewtype dtor_Newtype_a0 { get; }
    DAST._IDatatype dtor_Datatype_a0 { get; }
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
    public DAST._IModule dtor_Module_a0 {
      get {
        var d = this;
        return ((ModuleItem_Module)d)._a0;
      }
    }
    public DAST._IClass dtor_Class_a0 {
      get {
        var d = this;
        return ((ModuleItem_Class)d)._a0;
      }
    }
    public DAST._ITrait dtor_Trait_a0 {
      get {
        var d = this;
        return ((ModuleItem_Trait)d)._a0;
      }
    }
    public DAST._INewtype dtor_Newtype_a0 {
      get {
        var d = this;
        return ((ModuleItem_Newtype)d)._a0;
      }
    }
    public DAST._IDatatype dtor_Datatype_a0 {
      get {
        var d = this;
        return ((ModuleItem_Datatype)d)._a0;
      }
    }
    public abstract _IModuleItem DowncastClone();
  }
  public class ModuleItem_Module : ModuleItem {
    public readonly DAST._IModule _a0;
    public ModuleItem_Module(DAST._IModule _a0) : base() {
      this._a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Module(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Module;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Module";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Class : ModuleItem {
    public readonly DAST._IClass _a0;
    public ModuleItem_Class(DAST._IClass _a0) : base() {
      this._a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Class(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Class;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Class";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Trait : ModuleItem {
    public readonly DAST._ITrait _a0;
    public ModuleItem_Trait(DAST._ITrait _a0) : base() {
      this._a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Trait(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Trait;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Newtype : ModuleItem {
    public readonly DAST._INewtype _a0;
    public ModuleItem_Newtype(DAST._INewtype _a0) : base() {
      this._a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Newtype(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Newtype;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Newtype";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class ModuleItem_Datatype : ModuleItem {
    public readonly DAST._IDatatype _a0;
    public ModuleItem_Datatype(DAST._IDatatype _a0) : base() {
      this._a0 = _a0;
    }
    public override _IModuleItem DowncastClone() {
      if (this is _IModuleItem dt) { return dt; }
      return new ModuleItem_Datatype(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ModuleItem_Datatype;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ModuleItem.Datatype";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }

  public interface _IType {
    bool is_Path { get; }
    bool is_Tuple { get; }
    bool is_Array { get; }
    bool is_Seq { get; }
    bool is_Set { get; }
    bool is_Multiset { get; }
    bool is_Map { get; }
    bool is_Arrow { get; }
    bool is_Primitive { get; }
    bool is_Passthrough { get; }
    bool is_TypeArg { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Path_a0 { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    DAST._IResolvedType dtor_resolved { get; }
    Dafny.ISequence<DAST._IType> dtor_Tuple_a0 { get; }
    DAST._IType dtor_element { get; }
    DAST._IType dtor_key { get; }
    DAST._IType dtor_value { get; }
    Dafny.ISequence<DAST._IType> dtor_args { get; }
    DAST._IType dtor_result { get; }
    DAST._IPrimitive dtor_Primitive_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Passthrough_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_TypeArg_a0 { get; }
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
    public static _IType create_Tuple(Dafny.ISequence<DAST._IType> _a0) {
      return new Type_Tuple(_a0);
    }
    public static _IType create_Array(DAST._IType element) {
      return new Type_Array(element);
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
    public bool is_Tuple { get { return this is Type_Tuple; } }
    public bool is_Array { get { return this is Type_Array; } }
    public bool is_Seq { get { return this is Type_Seq; } }
    public bool is_Set { get { return this is Type_Set; } }
    public bool is_Multiset { get { return this is Type_Multiset; } }
    public bool is_Map { get { return this is Type_Map; } }
    public bool is_Arrow { get { return this is Type_Arrow; } }
    public bool is_Primitive { get { return this is Type_Primitive; } }
    public bool is_Passthrough { get { return this is Type_Passthrough; } }
    public bool is_TypeArg { get { return this is Type_TypeArg; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Path_a0 {
      get {
        var d = this;
        return ((Type_Path)d)._a0;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        return ((Type_Path)d)._typeArgs;
      }
    }
    public DAST._IResolvedType dtor_resolved {
      get {
        var d = this;
        return ((Type_Path)d)._resolved;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_Tuple_a0 {
      get {
        var d = this;
        return ((Type_Tuple)d)._a0;
      }
    }
    public DAST._IType dtor_element {
      get {
        var d = this;
        if (d is Type_Array) { return ((Type_Array)d)._element; }
        if (d is Type_Seq) { return ((Type_Seq)d)._element; }
        if (d is Type_Set) { return ((Type_Set)d)._element; }
        return ((Type_Multiset)d)._element;
      }
    }
    public DAST._IType dtor_key {
      get {
        var d = this;
        return ((Type_Map)d)._key;
      }
    }
    public DAST._IType dtor_value {
      get {
        var d = this;
        return ((Type_Map)d)._value;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_args {
      get {
        var d = this;
        return ((Type_Arrow)d)._args;
      }
    }
    public DAST._IType dtor_result {
      get {
        var d = this;
        return ((Type_Arrow)d)._result;
      }
    }
    public DAST._IPrimitive dtor_Primitive_a0 {
      get {
        var d = this;
        return ((Type_Primitive)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_Passthrough_a0 {
      get {
        var d = this;
        return ((Type_Passthrough)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_TypeArg_a0 {
      get {
        var d = this;
        return ((Type_TypeArg)d)._a0;
      }
    }
    public abstract _IType DowncastClone();
  }
  public class Type_Path : Type {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly DAST._IResolvedType _resolved;
    public Type_Path(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0, Dafny.ISequence<DAST._IType> typeArgs, DAST._IResolvedType resolved) : base() {
      this._a0 = _a0;
      this._typeArgs = typeArgs;
      this._resolved = resolved;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Path(_a0, _typeArgs, _resolved);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Path;
      return oth != null && object.Equals(this._a0, oth._a0) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._resolved, oth._resolved);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._resolved));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Path";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._resolved);
      s += ")";
      return s;
    }
  }
  public class Type_Tuple : Type {
    public readonly Dafny.ISequence<DAST._IType> _a0;
    public Type_Tuple(Dafny.ISequence<DAST._IType> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Tuple(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Tuple;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Tuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Type_Array : Type {
    public readonly DAST._IType _element;
    public Type_Array(DAST._IType element) : base() {
      this._element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Array(_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Array;
      return oth != null && object.Equals(this._element, oth._element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._element);
      s += ")";
      return s;
    }
  }
  public class Type_Seq : Type {
    public readonly DAST._IType _element;
    public Type_Seq(DAST._IType element) : base() {
      this._element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Seq(_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Seq;
      return oth != null && object.Equals(this._element, oth._element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Seq";
      s += "(";
      s += Dafny.Helpers.ToString(this._element);
      s += ")";
      return s;
    }
  }
  public class Type_Set : Type {
    public readonly DAST._IType _element;
    public Type_Set(DAST._IType element) : base() {
      this._element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Set(_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Set;
      return oth != null && object.Equals(this._element, oth._element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Set";
      s += "(";
      s += Dafny.Helpers.ToString(this._element);
      s += ")";
      return s;
    }
  }
  public class Type_Multiset : Type {
    public readonly DAST._IType _element;
    public Type_Multiset(DAST._IType element) : base() {
      this._element = element;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Multiset(_element);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Multiset;
      return oth != null && object.Equals(this._element, oth._element);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._element));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Multiset";
      s += "(";
      s += Dafny.Helpers.ToString(this._element);
      s += ")";
      return s;
    }
  }
  public class Type_Map : Type {
    public readonly DAST._IType _key;
    public readonly DAST._IType _value;
    public Type_Map(DAST._IType key, DAST._IType @value) : base() {
      this._key = key;
      this._value = @value;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Map(_key, _value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Map;
      return oth != null && object.Equals(this._key, oth._key) && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Map";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Type_Arrow : Type {
    public readonly Dafny.ISequence<DAST._IType> _args;
    public readonly DAST._IType _result;
    public Type_Arrow(Dafny.ISequence<DAST._IType> args, DAST._IType result) : base() {
      this._args = args;
      this._result = result;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Arrow(_args, _result);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Arrow;
      return oth != null && object.Equals(this._args, oth._args) && object.Equals(this._result, oth._result);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._result));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Arrow";
      s += "(";
      s += Dafny.Helpers.ToString(this._args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._result);
      s += ")";
      return s;
    }
  }
  public class Type_Primitive : Type {
    public readonly DAST._IPrimitive _a0;
    public Type_Primitive(DAST._IPrimitive _a0) : base() {
      this._a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Primitive(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Primitive;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Primitive";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Type_Passthrough : Type {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public Type_Passthrough(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Passthrough(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Passthrough;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Passthrough";
      s += "(";
      s += this._a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Type_TypeArg : Type {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public Type_TypeArg(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TypeArg(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_TypeArg;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.TypeArg";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
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
      return (int)hash;
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
      return (int)hash;
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
      return (int)hash;
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
      return (int)hash;
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
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Primitive.Char";
      return s;
    }
  }

  public interface _IResolvedType {
    bool is_Datatype { get; }
    bool is_Trait { get; }
    bool is_Newtype { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path { get; }
    DAST._IType dtor_Newtype_a0 { get; }
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
    public static _IResolvedType create_Newtype(DAST._IType _a0) {
      return new ResolvedType_Newtype(_a0);
    }
    public bool is_Datatype { get { return this is ResolvedType_Datatype; } }
    public bool is_Trait { get { return this is ResolvedType_Trait; } }
    public bool is_Newtype { get { return this is ResolvedType_Newtype; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path {
      get {
        var d = this;
        if (d is ResolvedType_Datatype) { return ((ResolvedType_Datatype)d)._path; }
        return ((ResolvedType_Trait)d)._path;
      }
    }
    public DAST._IType dtor_Newtype_a0 {
      get {
        var d = this;
        return ((ResolvedType_Newtype)d)._a0;
      }
    }
    public abstract _IResolvedType DowncastClone();
  }
  public class ResolvedType_Datatype : ResolvedType {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _path;
    public ResolvedType_Datatype(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) : base() {
      this._path = path;
    }
    public override _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType_Datatype(_path);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType_Datatype;
      return oth != null && object.Equals(this._path, oth._path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.Datatype";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ")";
      return s;
    }
  }
  public class ResolvedType_Trait : ResolvedType {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _path;
    public ResolvedType_Trait(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) : base() {
      this._path = path;
    }
    public override _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType_Trait(_path);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType_Trait;
      return oth != null && object.Equals(this._path, oth._path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.Trait";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ")";
      return s;
    }
  }
  public class ResolvedType_Newtype : ResolvedType {
    public readonly DAST._IType _a0;
    public ResolvedType_Newtype(DAST._IType _a0) : base() {
      this._a0 = _a0;
    }
    public override _IResolvedType DowncastClone() {
      if (this is _IResolvedType dt) { return dt; }
      return new ResolvedType_Newtype(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ResolvedType_Newtype;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ResolvedType.Newtype";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }

  public interface _IIdent {
    bool is_Ident { get; }
    Dafny.ISequence<Dafny.Rune> dtor_id { get; }
  }
  public class Ident : _IIdent {
    public readonly Dafny.ISequence<Dafny.Rune> _id;
    public Ident(Dafny.ISequence<Dafny.Rune> id) {
      this._id = id;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Ident;
      return oth != null && object.Equals(this._id, oth._id);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Ident.Ident";
      s += "(";
      s += this._id.ToVerbatimString(true);
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
        return this._id;
      }
    }
  }

  public interface _IClass {
    bool is_Class { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IType> dtor_superClasses { get; }
    Dafny.ISequence<DAST._IField> dtor_fields { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    _IClass DowncastClone();
  }
  public class Class : _IClass {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly Dafny.ISequence<DAST._IType> _superClasses;
    public readonly Dafny.ISequence<DAST._IField> _fields;
    public readonly Dafny.ISequence<DAST._IMethod> _body;
    public Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body) {
      this._name = name;
      this._typeParams = typeParams;
      this._superClasses = superClasses;
      this._fields = fields;
      this._body = body;
    }
    public _IClass DowncastClone() {
      if (this is _IClass dt) { return dt; }
      return new Class(_name, _typeParams, _superClasses, _fields, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Class;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._superClasses, oth._superClasses) && object.Equals(this._fields, oth._fields) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._superClasses));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Class.Class";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._superClasses);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fields);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
    private static readonly DAST._IClass theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IField>.Empty, Dafny.Sequence<DAST._IMethod>.Empty);
    public static DAST._IClass Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IClass> _TYPE = new Dafny.TypeDescriptor<DAST._IClass>(DAST.Class.Default());
    public static Dafny.TypeDescriptor<DAST._IClass> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IClass create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body) {
      return new Class(name, typeParams, superClasses, fields, body);
    }
    public static _IClass create_Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body) {
      return create(name, typeParams, superClasses, fields, body);
    }
    public bool is_Class { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_superClasses {
      get {
        return this._superClasses;
      }
    }
    public Dafny.ISequence<DAST._IField> dtor_fields {
      get {
        return this._fields;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_body {
      get {
        return this._body;
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly Dafny.ISequence<DAST._IMethod> _body;
    public Trait(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IMethod> body) {
      this._name = name;
      this._typeParams = typeParams;
      this._body = body;
    }
    public _ITrait DowncastClone() {
      if (this is _ITrait dt) { return dt; }
      return new Trait(_name, _typeParams, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Trait;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Trait.Trait";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
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
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_body {
      get {
        return this._body;
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _enclosingModule;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly Dafny.ISequence<DAST._IDatatypeCtor> _ctors;
    public readonly Dafny.ISequence<DAST._IMethod> _body;
    public readonly bool _isCo;
    public Datatype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IDatatypeCtor> ctors, Dafny.ISequence<DAST._IMethod> body, bool isCo) {
      this._name = name;
      this._enclosingModule = enclosingModule;
      this._typeParams = typeParams;
      this._ctors = ctors;
      this._body = body;
      this._isCo = isCo;
    }
    public _IDatatype DowncastClone() {
      if (this is _IDatatype dt) { return dt; }
      return new Datatype(_name, _enclosingModule, _typeParams, _ctors, _body, _isCo);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Datatype;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._enclosingModule, oth._enclosingModule) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._ctors, oth._ctors) && object.Equals(this._body, oth._body) && this._isCo == oth._isCo;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enclosingModule));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ctors));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isCo));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Datatype.Datatype";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._enclosingModule);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ctors);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isCo);
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
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_enclosingModule {
      get {
        return this._enclosingModule;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<DAST._IDatatypeCtor> dtor_ctors {
      get {
        return this._ctors;
      }
    }
    public Dafny.ISequence<DAST._IMethod> dtor_body {
      get {
        return this._body;
      }
    }
    public bool dtor_isCo {
      get {
        return this._isCo;
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IFormal> _args;
    public readonly bool _hasAnyArgs;
    public DatatypeCtor(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IFormal> args, bool hasAnyArgs) {
      this._name = name;
      this._args = args;
      this._hasAnyArgs = hasAnyArgs;
    }
    public _IDatatypeCtor DowncastClone() {
      if (this is _IDatatypeCtor dt) { return dt; }
      return new DatatypeCtor(_name, _args, _hasAnyArgs);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.DatatypeCtor;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._args, oth._args) && this._hasAnyArgs == oth._hasAnyArgs;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hasAnyArgs));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.DatatypeCtor.DatatypeCtor";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hasAnyArgs);
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
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_args {
      get {
        return this._args;
      }
    }
    public bool dtor_hasAnyArgs {
      get {
        return this._hasAnyArgs;
      }
    }
  }

  public interface _INewtype {
    bool is_Newtype { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    DAST._IType dtor_base { get; }
    Dafny.ISequence<DAST._IStatement> dtor_witnessStmts { get; }
    DAST._IOptional<DAST._IExpression> dtor_witnessExpr { get; }
    _INewtype DowncastClone();
  }
  public class Newtype : _INewtype {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly DAST._IType _base;
    public readonly Dafny.ISequence<DAST._IStatement> _witnessStmts;
    public readonly DAST._IOptional<DAST._IExpression> _witnessExpr;
    public Newtype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, DAST._IType @base, Dafny.ISequence<DAST._IStatement> witnessStmts, DAST._IOptional<DAST._IExpression> witnessExpr) {
      this._name = name;
      this._typeParams = typeParams;
      this._base = @base;
      this._witnessStmts = witnessStmts;
      this._witnessExpr = witnessExpr;
    }
    public _INewtype DowncastClone() {
      if (this is _INewtype dt) { return dt; }
      return new Newtype(_name, _typeParams, _base, _witnessStmts, _witnessExpr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Newtype;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._base, oth._base) && object.Equals(this._witnessStmts, oth._witnessStmts) && object.Equals(this._witnessExpr, oth._witnessExpr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._witnessStmts));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._witnessExpr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Newtype.Newtype";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._base);
      s += ", ";
      s += Dafny.Helpers.ToString(this._witnessStmts);
      s += ", ";
      s += Dafny.Helpers.ToString(this._witnessExpr);
      s += ")";
      return s;
    }
    private static readonly DAST._INewtype theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, DAST.Type.Default(), Dafny.Sequence<DAST._IStatement>.Empty, DAST.Optional<DAST._IExpression>.Default());
    public static DAST._INewtype Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._INewtype> _TYPE = new Dafny.TypeDescriptor<DAST._INewtype>(DAST.Newtype.Default());
    public static Dafny.TypeDescriptor<DAST._INewtype> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INewtype create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, DAST._IType @base, Dafny.ISequence<DAST._IStatement> witnessStmts, DAST._IOptional<DAST._IExpression> witnessExpr) {
      return new Newtype(name, typeParams, @base, witnessStmts, witnessExpr);
    }
    public static _INewtype create_Newtype(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, DAST._IType @base, Dafny.ISequence<DAST._IStatement> witnessStmts, DAST._IOptional<DAST._IExpression> witnessExpr) {
      return create(name, typeParams, @base, witnessStmts, witnessExpr);
    }
    public bool is_Newtype { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public DAST._IType dtor_base {
      get {
        return this._base;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_witnessStmts {
      get {
        return this._witnessStmts;
      }
    }
    public DAST._IOptional<DAST._IExpression> dtor_witnessExpr {
      get {
        return this._witnessExpr;
      }
    }
  }

  public interface _IClassItem {
    bool is_Method { get; }
    DAST._IMethod dtor_Method_a0 { get; }
  }
  public class ClassItem : _IClassItem {
    public readonly DAST._IMethod _a0;
    public ClassItem(DAST._IMethod _a0) {
      this._a0 = _a0;
    }
    public static DAST._IMethod DowncastClone(DAST._IMethod _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as DAST.ClassItem;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.ClassItem.Method";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
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
    public DAST._IMethod dtor_Method_a0 {
      get {
        return this._a0;
      }
    }
  }

  public interface _IField {
    bool is_Field { get; }
    DAST._IFormal dtor_formal { get; }
    DAST._IOptional<DAST._IExpression> dtor_defaultValue { get; }
    _IField DowncastClone();
  }
  public class Field : _IField {
    public readonly DAST._IFormal _formal;
    public readonly DAST._IOptional<DAST._IExpression> _defaultValue;
    public Field(DAST._IFormal formal, DAST._IOptional<DAST._IExpression> defaultValue) {
      this._formal = formal;
      this._defaultValue = defaultValue;
    }
    public _IField DowncastClone() {
      if (this is _IField dt) { return dt; }
      return new Field(_formal, _defaultValue);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Field;
      return oth != null && object.Equals(this._formal, oth._formal) && object.Equals(this._defaultValue, oth._defaultValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formal));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._defaultValue));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Field.Field";
      s += "(";
      s += Dafny.Helpers.ToString(this._formal);
      s += ", ";
      s += Dafny.Helpers.ToString(this._defaultValue);
      s += ")";
      return s;
    }
    private static readonly DAST._IField theDefault = create(DAST.Formal.Default(), DAST.Optional<DAST._IExpression>.Default());
    public static DAST._IField Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IField> _TYPE = new Dafny.TypeDescriptor<DAST._IField>(DAST.Field.Default());
    public static Dafny.TypeDescriptor<DAST._IField> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IField create(DAST._IFormal formal, DAST._IOptional<DAST._IExpression> defaultValue) {
      return new Field(formal, defaultValue);
    }
    public static _IField create_Field(DAST._IFormal formal, DAST._IOptional<DAST._IExpression> defaultValue) {
      return create(formal, defaultValue);
    }
    public bool is_Field { get { return true; } }
    public DAST._IFormal dtor_formal {
      get {
        return this._formal;
      }
    }
    public DAST._IOptional<DAST._IExpression> dtor_defaultValue {
      get {
        return this._defaultValue;
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
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IType _typ;
    public Formal(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ) {
      this._name = name;
      this._typ = typ;
    }
    public _IFormal DowncastClone() {
      if (this is _IFormal dt) { return dt; }
      return new Formal(_name, _typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Formal;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typ, oth._typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Formal.Formal";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
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
        return this._name;
      }
    }
    public DAST._IType dtor_typ {
      get {
        return this._typ;
      }
    }
  }

  public interface _IMethod {
    bool is_Method { get; }
    bool dtor_isStatic { get; }
    bool dtor_hasBody { get; }
    DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_overridingPath { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IFormal> dtor_params { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    Dafny.ISequence<DAST._IType> dtor_outTypes { get; }
    DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outVars { get; }
    _IMethod DowncastClone();
  }
  public class Method : _IMethod {
    public readonly bool _isStatic;
    public readonly bool _hasBody;
    public readonly DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _overridingPath;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly Dafny.ISequence<DAST._IFormal> _params;
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public readonly Dafny.ISequence<DAST._IType> _outTypes;
    public readonly DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _outVars;
    public Method(bool isStatic, bool hasBody, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      this._isStatic = isStatic;
      this._hasBody = hasBody;
      this._overridingPath = overridingPath;
      this._name = name;
      this._typeParams = typeParams;
      this._params = @params;
      this._body = body;
      this._outTypes = outTypes;
      this._outVars = outVars;
    }
    public _IMethod DowncastClone() {
      if (this is _IMethod dt) { return dt; }
      return new Method(_isStatic, _hasBody, _overridingPath, _name, _typeParams, _params, _body, _outTypes, _outVars);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Method;
      return oth != null && this._isStatic == oth._isStatic && this._hasBody == oth._hasBody && object.Equals(this._overridingPath, oth._overridingPath) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._params, oth._params) && object.Equals(this._body, oth._body) && object.Equals(this._outTypes, oth._outTypes) && object.Equals(this._outVars, oth._outVars);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isStatic));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hasBody));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overridingPath));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._outTypes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._outVars));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Method.Method";
      s += "(";
      s += Dafny.Helpers.ToString(this._isStatic);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hasBody);
      s += ", ";
      s += Dafny.Helpers.ToString(this._overridingPath);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._params);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ", ";
      s += Dafny.Helpers.ToString(this._outTypes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._outVars);
      s += ")";
      return s;
    }
    private static readonly DAST._IMethod theDefault = create(false, false, DAST.Optional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.Default(), Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<DAST._IType>.Empty, Dafny.Sequence<DAST._IFormal>.Empty, Dafny.Sequence<DAST._IStatement>.Empty, Dafny.Sequence<DAST._IType>.Empty, DAST.Optional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.Default());
    public static DAST._IMethod Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IMethod> _TYPE = new Dafny.TypeDescriptor<DAST._IMethod>(DAST.Method.Default());
    public static Dafny.TypeDescriptor<DAST._IMethod> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMethod create(bool isStatic, bool hasBody, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      return new Method(isStatic, hasBody, overridingPath, name, typeParams, @params, body, outTypes, outVars);
    }
    public static _IMethod create_Method(bool isStatic, bool hasBody, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> overridingPath, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IFormal> @params, Dafny.ISequence<DAST._IStatement> body, Dafny.ISequence<DAST._IType> outTypes, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outVars) {
      return create(isStatic, hasBody, overridingPath, name, typeParams, @params, body, outTypes, outVars);
    }
    public bool is_Method { get { return true; } }
    public bool dtor_isStatic {
      get {
        return this._isStatic;
      }
    }
    public bool dtor_hasBody {
      get {
        return this._hasBody;
      }
    }
    public DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_overridingPath {
      get {
        return this._overridingPath;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_params {
      get {
        return this._params;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        return this._body;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_outTypes {
      get {
        return this._outTypes;
      }
    }
    public DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outVars {
      get {
        return this._outVars;
      }
    }
  }

  public interface _IOptional<T> {
    bool is_Some { get; }
    bool is_None { get; }
    T dtor_Some_a0 { get; }
    _IOptional<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Optional<T> : _IOptional<T> {
    public Optional() {
    }
    public static DAST._IOptional<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<DAST._IOptional<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<DAST._IOptional<T>>(DAST.Optional<T>.Default());
    }
    public static _IOptional<T> create_Some(T _a0) {
      return new Optional_Some<T>(_a0);
    }
    public static _IOptional<T> create_None() {
      return new Optional_None<T>();
    }
    public bool is_Some { get { return this is Optional_Some<T>; } }
    public bool is_None { get { return this is Optional_None<T>; } }
    public T dtor_Some_a0 {
      get {
        var d = this;
        return ((Optional_Some<T>)d)._a0;
      }
    }
    public abstract _IOptional<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Optional_Some<T> : Optional<T> {
    public readonly T _a0;
    public Optional_Some(T _a0) : base() {
      this._a0 = _a0;
    }
    public override _IOptional<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOptional<__T> dt) { return dt; }
      return new Optional_Some<__T>(converter0(_a0));
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Optional_Some<T>;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Optional.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Optional_None<T> : Optional<T> {
    public Optional_None() : base() {
    }
    public override _IOptional<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOptional<__T> dt) { return dt; }
      return new Optional_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Optional_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Optional.None";
      return s;
    }
  }

  public interface _IStatement {
    bool is_DeclareVar { get; }
    bool is_Assign { get; }
    bool is_If { get; }
    bool is_While { get; }
    bool is_Call { get; }
    bool is_Return { get; }
    bool is_EarlyReturn { get; }
    bool is_Halt { get; }
    bool is_Print { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    DAST._IType dtor_typ { get; }
    DAST._IOptional<DAST._IExpression> dtor_maybeValue { get; }
    DAST._IAssignLhs dtor_lhs { get; }
    DAST._IExpression dtor_value { get; }
    DAST._IExpression dtor_cond { get; }
    Dafny.ISequence<DAST._IStatement> dtor_thn { get; }
    Dafny.ISequence<DAST._IStatement> dtor_els { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    DAST._IExpression dtor_on { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outs { get; }
    DAST._IExpression dtor_expr { get; }
    DAST._IExpression dtor_Print_a0 { get; }
    _IStatement DowncastClone();
  }
  public abstract class Statement : _IStatement {
    public Statement() {
    }
    private static readonly DAST._IStatement theDefault = create_DeclareVar(Dafny.Sequence<Dafny.Rune>.Empty, DAST.Type.Default(), DAST.Optional<DAST._IExpression>.Default());
    public static DAST._IStatement Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DAST._IStatement> _TYPE = new Dafny.TypeDescriptor<DAST._IStatement>(DAST.Statement.Default());
    public static Dafny.TypeDescriptor<DAST._IStatement> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStatement create_DeclareVar(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, DAST._IOptional<DAST._IExpression> maybeValue) {
      return new Statement_DeclareVar(name, typ, maybeValue);
    }
    public static _IStatement create_Assign(DAST._IAssignLhs lhs, DAST._IExpression @value) {
      return new Statement_Assign(lhs, @value);
    }
    public static _IStatement create_If(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> thn, Dafny.ISequence<DAST._IStatement> els) {
      return new Statement_If(cond, thn, els);
    }
    public static _IStatement create_While(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_While(cond, body);
    }
    public static _IStatement create_Call(DAST._IExpression @on, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outs) {
      return new Statement_Call(@on, name, typeArgs, args, outs);
    }
    public static _IStatement create_Return(DAST._IExpression expr) {
      return new Statement_Return(expr);
    }
    public static _IStatement create_EarlyReturn() {
      return new Statement_EarlyReturn();
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
    public bool is_While { get { return this is Statement_While; } }
    public bool is_Call { get { return this is Statement_Call; } }
    public bool is_Return { get { return this is Statement_Return; } }
    public bool is_EarlyReturn { get { return this is Statement_EarlyReturn; } }
    public bool is_Halt { get { return this is Statement_Halt; } }
    public bool is_Print { get { return this is Statement_Print; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Statement_DeclareVar) { return ((Statement_DeclareVar)d)._name; }
        return ((Statement_Call)d)._name;
      }
    }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        return ((Statement_DeclareVar)d)._typ;
      }
    }
    public DAST._IOptional<DAST._IExpression> dtor_maybeValue {
      get {
        var d = this;
        return ((Statement_DeclareVar)d)._maybeValue;
      }
    }
    public DAST._IAssignLhs dtor_lhs {
      get {
        var d = this;
        return ((Statement_Assign)d)._lhs;
      }
    }
    public DAST._IExpression dtor_value {
      get {
        var d = this;
        return ((Statement_Assign)d)._value;
      }
    }
    public DAST._IExpression dtor_cond {
      get {
        var d = this;
        if (d is Statement_If) { return ((Statement_If)d)._cond; }
        return ((Statement_While)d)._cond;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_thn {
      get {
        var d = this;
        return ((Statement_If)d)._thn;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_els {
      get {
        var d = this;
        return ((Statement_If)d)._els;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        var d = this;
        return ((Statement_While)d)._body;
      }
    }
    public DAST._IExpression dtor_on {
      get {
        var d = this;
        return ((Statement_Call)d)._on;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        return ((Statement_Call)d)._typeArgs;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_args {
      get {
        var d = this;
        return ((Statement_Call)d)._args;
      }
    }
    public DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outs {
      get {
        var d = this;
        return ((Statement_Call)d)._outs;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        return ((Statement_Return)d)._expr;
      }
    }
    public DAST._IExpression dtor_Print_a0 {
      get {
        var d = this;
        return ((Statement_Print)d)._a0;
      }
    }
    public abstract _IStatement DowncastClone();
  }
  public class Statement_DeclareVar : Statement {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IType _typ;
    public readonly DAST._IOptional<DAST._IExpression> _maybeValue;
    public Statement_DeclareVar(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, DAST._IOptional<DAST._IExpression> maybeValue) : base() {
      this._name = name;
      this._typ = typ;
      this._maybeValue = maybeValue;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_DeclareVar(_name, _typ, _maybeValue);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_DeclareVar;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typ, oth._typ) && object.Equals(this._maybeValue, oth._maybeValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._maybeValue));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.DeclareVar";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
      s += ", ";
      s += Dafny.Helpers.ToString(this._maybeValue);
      s += ")";
      return s;
    }
  }
  public class Statement_Assign : Statement {
    public readonly DAST._IAssignLhs _lhs;
    public readonly DAST._IExpression _value;
    public Statement_Assign(DAST._IAssignLhs lhs, DAST._IExpression @value) : base() {
      this._lhs = lhs;
      this._value = @value;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Assign(_lhs, _value);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Assign;
      return oth != null && object.Equals(this._lhs, oth._lhs) && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lhs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Assign";
      s += "(";
      s += Dafny.Helpers.ToString(this._lhs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Statement_If : Statement {
    public readonly DAST._IExpression _cond;
    public readonly Dafny.ISequence<DAST._IStatement> _thn;
    public readonly Dafny.ISequence<DAST._IStatement> _els;
    public Statement_If(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> thn, Dafny.ISequence<DAST._IStatement> els) : base() {
      this._cond = cond;
      this._thn = thn;
      this._els = els;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_If(_cond, _thn, _els);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_If;
      return oth != null && object.Equals(this._cond, oth._cond) && object.Equals(this._thn, oth._thn) && object.Equals(this._els, oth._els);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._els));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.If";
      s += "(";
      s += Dafny.Helpers.ToString(this._cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._thn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._els);
      s += ")";
      return s;
    }
  }
  public class Statement_While : Statement {
    public readonly DAST._IExpression _cond;
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public Statement_While(DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._cond = cond;
      this._body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_While(_cond, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_While;
      return oth != null && object.Equals(this._cond, oth._cond) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.While";
      s += "(";
      s += Dafny.Helpers.ToString(this._cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Statement_Call : Statement {
    public readonly DAST._IExpression _on;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _args;
    public readonly DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _outs;
    public Statement_Call(DAST._IExpression @on, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> outs) : base() {
      this._on = @on;
      this._name = name;
      this._typeArgs = typeArgs;
      this._args = args;
      this._outs = outs;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Call(_on, _name, _typeArgs, _args, _outs);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Call;
      return oth != null && object.Equals(this._on, oth._on) && object.Equals(this._name, oth._name) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._args, oth._args) && object.Equals(this._outs, oth._outs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._outs));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ", ";
      s += Dafny.Helpers.ToString(this._outs);
      s += ")";
      return s;
    }
  }
  public class Statement_Return : Statement {
    public readonly DAST._IExpression _expr;
    public Statement_Return(DAST._IExpression expr) : base() {
      this._expr = expr;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Return(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Return;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Return";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
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
      hash = ((hash << 5) + hash) + 6;
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.EarlyReturn";
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
      hash = ((hash << 5) + hash) + 7;
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Halt";
      return s;
    }
  }
  public class Statement_Print : Statement {
    public readonly DAST._IExpression _a0;
    public Statement_Print(DAST._IExpression _a0) : base() {
      this._a0 = _a0;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Print(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Print;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Print";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }

  public interface _IAssignLhs {
    bool is_Ident { get; }
    bool is_Select { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Ident_a0 { get; }
    DAST._IExpression dtor_expr { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
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
    public bool is_Ident { get { return this is AssignLhs_Ident; } }
    public bool is_Select { get { return this is AssignLhs_Select; } }
    public Dafny.ISequence<Dafny.Rune> dtor_Ident_a0 {
      get {
        var d = this;
        return ((AssignLhs_Ident)d)._a0;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        return ((AssignLhs_Select)d)._expr;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        return ((AssignLhs_Select)d)._field;
      }
    }
    public abstract _IAssignLhs DowncastClone();
  }
  public class AssignLhs_Ident : AssignLhs {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public AssignLhs_Ident(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Ident(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Ident;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Ident";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_Select : AssignLhs {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public AssignLhs_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field) : base() {
      this._expr = expr;
      this._field = field;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Select(_expr, _field);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Select;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._field, oth._field);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += this._field.ToVerbatimString(true);
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
    bool is_SeqValue { get; }
    bool is_SetValue { get; }
    bool is_This { get; }
    bool is_Ite { get; }
    bool is_UnOp { get; }
    bool is_BinOp { get; }
    bool is_Select { get; }
    bool is_SelectFn { get; }
    bool is_TupleSelect { get; }
    bool is_Call { get; }
    bool is_Lambda { get; }
    bool is_IIFE { get; }
    bool is_Apply { get; }
    bool is_TypeTest { get; }
    bool is_InitializationValue { get; }
    DAST._ILiteral dtor_Literal_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Ident_a0 { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Companion_a0 { get; }
    Dafny.ISequence<DAST._IExpression> dtor_Tuple_a0 { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    Dafny.ISequence<DAST._IExpression> dtor_dims { get; }
    Dafny.ISequence<Dafny.Rune> dtor_variant { get; }
    bool dtor_isCo { get; }
    Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> dtor_contents { get; }
    DAST._IExpression dtor_value { get; }
    DAST._IType dtor_from { get; }
    DAST._IType dtor_typ { get; }
    Dafny.ISequence<DAST._IExpression> dtor_elements { get; }
    DAST._IExpression dtor_cond { get; }
    DAST._IExpression dtor_thn { get; }
    DAST._IExpression dtor_els { get; }
    DAST._IUnaryOp dtor_unOp { get; }
    DAST._IExpression dtor_expr { get; }
    Dafny.ISequence<Dafny.Rune> dtor_op { get; }
    DAST._IExpression dtor_left { get; }
    DAST._IExpression dtor_right { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    bool dtor_isConstant { get; }
    bool dtor_onDatatype { get; }
    bool dtor_isStatic { get; }
    BigInteger dtor_arity { get; }
    BigInteger dtor_index { get; }
    DAST._IExpression dtor_on { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<DAST._IFormal> dtor_params { get; }
    DAST._IType dtor_retType { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    DAST._IExpression dtor_iifeBody { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_dType { get; }
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
    public static _IExpression create_New(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_New(path, args);
    }
    public static _IExpression create_NewArray(Dafny.ISequence<DAST._IExpression> dims) {
      return new Expression_NewArray(dims);
    }
    public static _IExpression create_DatatypeValue(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<Dafny.Rune> variant, bool isCo, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> contents) {
      return new Expression_DatatypeValue(path, variant, isCo, contents);
    }
    public static _IExpression create_Convert(DAST._IExpression @value, DAST._IType @from, DAST._IType typ) {
      return new Expression_Convert(@value, @from, typ);
    }
    public static _IExpression create_SeqValue(Dafny.ISequence<DAST._IExpression> elements) {
      return new Expression_SeqValue(elements);
    }
    public static _IExpression create_SetValue(Dafny.ISequence<DAST._IExpression> elements) {
      return new Expression_SetValue(elements);
    }
    public static _IExpression create_This() {
      return new Expression_This();
    }
    public static _IExpression create_Ite(DAST._IExpression cond, DAST._IExpression thn, DAST._IExpression els) {
      return new Expression_Ite(cond, thn, els);
    }
    public static _IExpression create_UnOp(DAST._IUnaryOp unOp, DAST._IExpression expr) {
      return new Expression_UnOp(unOp, expr);
    }
    public static _IExpression create_BinOp(Dafny.ISequence<Dafny.Rune> op, DAST._IExpression left, DAST._IExpression right) {
      return new Expression_BinOp(op, left, right);
    }
    public static _IExpression create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant, bool onDatatype) {
      return new Expression_Select(expr, field, isConstant, onDatatype);
    }
    public static _IExpression create_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, BigInteger arity) {
      return new Expression_SelectFn(expr, field, onDatatype, isStatic, arity);
    }
    public static _IExpression create_TupleSelect(DAST._IExpression expr, BigInteger index) {
      return new Expression_TupleSelect(expr, index);
    }
    public static _IExpression create_Call(DAST._IExpression @on, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) {
      return new Expression_Call(@on, name, typeArgs, args);
    }
    public static _IExpression create_Lambda(Dafny.ISequence<DAST._IFormal> @params, DAST._IType retType, Dafny.ISequence<DAST._IStatement> body) {
      return new Expression_Lambda(@params, retType, body);
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
    public bool is_Literal { get { return this is Expression_Literal; } }
    public bool is_Ident { get { return this is Expression_Ident; } }
    public bool is_Companion { get { return this is Expression_Companion; } }
    public bool is_Tuple { get { return this is Expression_Tuple; } }
    public bool is_New { get { return this is Expression_New; } }
    public bool is_NewArray { get { return this is Expression_NewArray; } }
    public bool is_DatatypeValue { get { return this is Expression_DatatypeValue; } }
    public bool is_Convert { get { return this is Expression_Convert; } }
    public bool is_SeqValue { get { return this is Expression_SeqValue; } }
    public bool is_SetValue { get { return this is Expression_SetValue; } }
    public bool is_This { get { return this is Expression_This; } }
    public bool is_Ite { get { return this is Expression_Ite; } }
    public bool is_UnOp { get { return this is Expression_UnOp; } }
    public bool is_BinOp { get { return this is Expression_BinOp; } }
    public bool is_Select { get { return this is Expression_Select; } }
    public bool is_SelectFn { get { return this is Expression_SelectFn; } }
    public bool is_TupleSelect { get { return this is Expression_TupleSelect; } }
    public bool is_Call { get { return this is Expression_Call; } }
    public bool is_Lambda { get { return this is Expression_Lambda; } }
    public bool is_IIFE { get { return this is Expression_IIFE; } }
    public bool is_Apply { get { return this is Expression_Apply; } }
    public bool is_TypeTest { get { return this is Expression_TypeTest; } }
    public bool is_InitializationValue { get { return this is Expression_InitializationValue; } }
    public DAST._ILiteral dtor_Literal_a0 {
      get {
        var d = this;
        return ((Expression_Literal)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_Ident_a0 {
      get {
        var d = this;
        return ((Expression_Ident)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_Companion_a0 {
      get {
        var d = this;
        return ((Expression_Companion)d)._a0;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_Tuple_a0 {
      get {
        var d = this;
        return ((Expression_Tuple)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_path {
      get {
        var d = this;
        if (d is Expression_New) { return ((Expression_New)d)._path; }
        return ((Expression_DatatypeValue)d)._path;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_args {
      get {
        var d = this;
        if (d is Expression_New) { return ((Expression_New)d)._args; }
        if (d is Expression_Call) { return ((Expression_Call)d)._args; }
        return ((Expression_Apply)d)._args;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_dims {
      get {
        var d = this;
        return ((Expression_NewArray)d)._dims;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_variant {
      get {
        var d = this;
        if (d is Expression_DatatypeValue) { return ((Expression_DatatypeValue)d)._variant; }
        return ((Expression_TypeTest)d)._variant;
      }
    }
    public bool dtor_isCo {
      get {
        var d = this;
        return ((Expression_DatatypeValue)d)._isCo;
      }
    }
    public Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> dtor_contents {
      get {
        var d = this;
        return ((Expression_DatatypeValue)d)._contents;
      }
    }
    public DAST._IExpression dtor_value {
      get {
        var d = this;
        if (d is Expression_Convert) { return ((Expression_Convert)d)._value; }
        return ((Expression_IIFE)d)._value;
      }
    }
    public DAST._IType dtor_from {
      get {
        var d = this;
        return ((Expression_Convert)d)._from;
      }
    }
    public DAST._IType dtor_typ {
      get {
        var d = this;
        if (d is Expression_Convert) { return ((Expression_Convert)d)._typ; }
        if (d is Expression_IIFE) { return ((Expression_IIFE)d)._typ; }
        return ((Expression_InitializationValue)d)._typ;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_elements {
      get {
        var d = this;
        if (d is Expression_SeqValue) { return ((Expression_SeqValue)d)._elements; }
        return ((Expression_SetValue)d)._elements;
      }
    }
    public DAST._IExpression dtor_cond {
      get {
        var d = this;
        return ((Expression_Ite)d)._cond;
      }
    }
    public DAST._IExpression dtor_thn {
      get {
        var d = this;
        return ((Expression_Ite)d)._thn;
      }
    }
    public DAST._IExpression dtor_els {
      get {
        var d = this;
        return ((Expression_Ite)d)._els;
      }
    }
    public DAST._IUnaryOp dtor_unOp {
      get {
        var d = this;
        return ((Expression_UnOp)d)._unOp;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        if (d is Expression_UnOp) { return ((Expression_UnOp)d)._expr; }
        if (d is Expression_Select) { return ((Expression_Select)d)._expr; }
        if (d is Expression_SelectFn) { return ((Expression_SelectFn)d)._expr; }
        if (d is Expression_TupleSelect) { return ((Expression_TupleSelect)d)._expr; }
        return ((Expression_Apply)d)._expr;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_op {
      get {
        var d = this;
        return ((Expression_BinOp)d)._op;
      }
    }
    public DAST._IExpression dtor_left {
      get {
        var d = this;
        return ((Expression_BinOp)d)._left;
      }
    }
    public DAST._IExpression dtor_right {
      get {
        var d = this;
        return ((Expression_BinOp)d)._right;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        if (d is Expression_Select) { return ((Expression_Select)d)._field; }
        return ((Expression_SelectFn)d)._field;
      }
    }
    public bool dtor_isConstant {
      get {
        var d = this;
        return ((Expression_Select)d)._isConstant;
      }
    }
    public bool dtor_onDatatype {
      get {
        var d = this;
        if (d is Expression_Select) { return ((Expression_Select)d)._onDatatype; }
        return ((Expression_SelectFn)d)._onDatatype;
      }
    }
    public bool dtor_isStatic {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._isStatic;
      }
    }
    public BigInteger dtor_arity {
      get {
        var d = this;
        return ((Expression_SelectFn)d)._arity;
      }
    }
    public BigInteger dtor_index {
      get {
        var d = this;
        return ((Expression_TupleSelect)d)._index;
      }
    }
    public DAST._IExpression dtor_on {
      get {
        var d = this;
        if (d is Expression_Call) { return ((Expression_Call)d)._on; }
        return ((Expression_TypeTest)d)._on;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Expression_Call) { return ((Expression_Call)d)._name; }
        return ((Expression_IIFE)d)._name;
      }
    }
    public Dafny.ISequence<DAST._IType> dtor_typeArgs {
      get {
        var d = this;
        return ((Expression_Call)d)._typeArgs;
      }
    }
    public Dafny.ISequence<DAST._IFormal> dtor_params {
      get {
        var d = this;
        return ((Expression_Lambda)d)._params;
      }
    }
    public DAST._IType dtor_retType {
      get {
        var d = this;
        return ((Expression_Lambda)d)._retType;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        var d = this;
        return ((Expression_Lambda)d)._body;
      }
    }
    public DAST._IExpression dtor_iifeBody {
      get {
        var d = this;
        return ((Expression_IIFE)d)._iifeBody;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_dType {
      get {
        var d = this;
        return ((Expression_TypeTest)d)._dType;
      }
    }
    public abstract _IExpression DowncastClone();
  }
  public class Expression_Literal : Expression {
    public readonly DAST._ILiteral _a0;
    public Expression_Literal(DAST._ILiteral _a0) : base() {
      this._a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Literal(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Literal;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Literal";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Expression_Ident : Expression {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public Expression_Ident(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Ident(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Ident;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Ident";
      s += "(";
      s += this._a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expression_Companion : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0;
    public Expression_Companion(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Companion(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Companion;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Companion";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Expression_Tuple : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _a0;
    public Expression_Tuple(Dafny.ISequence<DAST._IExpression> _a0) : base() {
      this._a0 = _a0;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Tuple(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Tuple;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Tuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Expression_New : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _path;
    public readonly Dafny.ISequence<DAST._IExpression> _args;
    public Expression_New(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._path = path;
      this._args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_New(_path, _args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_New;
      return oth != null && object.Equals(this._path, oth._path) && object.Equals(this._args, oth._args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.New";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ")";
      return s;
    }
  }
  public class Expression_NewArray : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _dims;
    public Expression_NewArray(Dafny.ISequence<DAST._IExpression> dims) : base() {
      this._dims = dims;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_NewArray(_dims);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_NewArray;
      return oth != null && object.Equals(this._dims, oth._dims);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dims));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.NewArray";
      s += "(";
      s += Dafny.Helpers.ToString(this._dims);
      s += ")";
      return s;
    }
  }
  public class Expression_DatatypeValue : Expression {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _path;
    public readonly Dafny.ISequence<Dafny.Rune> _variant;
    public readonly bool _isCo;
    public readonly Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _contents;
    public Expression_DatatypeValue(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path, Dafny.ISequence<Dafny.Rune> variant, bool isCo, Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> contents) : base() {
      this._path = path;
      this._variant = variant;
      this._isCo = isCo;
      this._contents = contents;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_DatatypeValue(_path, _variant, _isCo, _contents);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_DatatypeValue;
      return oth != null && object.Equals(this._path, oth._path) && object.Equals(this._variant, oth._variant) && this._isCo == oth._isCo && object.Equals(this._contents, oth._contents);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variant));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isCo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._contents));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.DatatypeValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ", ";
      s += this._variant.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isCo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._contents);
      s += ")";
      return s;
    }
  }
  public class Expression_Convert : Expression {
    public readonly DAST._IExpression _value;
    public readonly DAST._IType _from;
    public readonly DAST._IType _typ;
    public Expression_Convert(DAST._IExpression @value, DAST._IType @from, DAST._IType typ) : base() {
      this._value = @value;
      this._from = @from;
      this._typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Convert(_value, _from, _typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Convert;
      return oth != null && object.Equals(this._value, oth._value) && object.Equals(this._from, oth._from) && object.Equals(this._typ, oth._typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._from));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Convert";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._from);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
      s += ")";
      return s;
    }
  }
  public class Expression_SeqValue : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _elements;
    public Expression_SeqValue(Dafny.ISequence<DAST._IExpression> elements) : base() {
      this._elements = elements;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SeqValue(_elements);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SeqValue;
      return oth != null && object.Equals(this._elements, oth._elements);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elements));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SeqValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._elements);
      s += ")";
      return s;
    }
  }
  public class Expression_SetValue : Expression {
    public readonly Dafny.ISequence<DAST._IExpression> _elements;
    public Expression_SetValue(Dafny.ISequence<DAST._IExpression> elements) : base() {
      this._elements = elements;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SetValue(_elements);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SetValue;
      return oth != null && object.Equals(this._elements, oth._elements);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elements));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SetValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._elements);
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
      hash = ((hash << 5) + hash) + 10;
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.This";
      return s;
    }
  }
  public class Expression_Ite : Expression {
    public readonly DAST._IExpression _cond;
    public readonly DAST._IExpression _thn;
    public readonly DAST._IExpression _els;
    public Expression_Ite(DAST._IExpression cond, DAST._IExpression thn, DAST._IExpression els) : base() {
      this._cond = cond;
      this._thn = thn;
      this._els = els;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Ite(_cond, _thn, _els);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Ite;
      return oth != null && object.Equals(this._cond, oth._cond) && object.Equals(this._thn, oth._thn) && object.Equals(this._els, oth._els);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._els));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Ite";
      s += "(";
      s += Dafny.Helpers.ToString(this._cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._thn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._els);
      s += ")";
      return s;
    }
  }
  public class Expression_UnOp : Expression {
    public readonly DAST._IUnaryOp _unOp;
    public readonly DAST._IExpression _expr;
    public Expression_UnOp(DAST._IUnaryOp unOp, DAST._IExpression expr) : base() {
      this._unOp = unOp;
      this._expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_UnOp(_unOp, _expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_UnOp;
      return oth != null && object.Equals(this._unOp, oth._unOp) && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._unOp));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.UnOp";
      s += "(";
      s += Dafny.Helpers.ToString(this._unOp);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }
  public class Expression_BinOp : Expression {
    public readonly Dafny.ISequence<Dafny.Rune> _op;
    public readonly DAST._IExpression _left;
    public readonly DAST._IExpression _right;
    public Expression_BinOp(Dafny.ISequence<Dafny.Rune> op, DAST._IExpression left, DAST._IExpression right) : base() {
      this._op = op;
      this._left = left;
      this._right = right;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_BinOp(_op, _left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_BinOp;
      return oth != null && object.Equals(this._op, oth._op) && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BinOp";
      s += "(";
      s += this._op.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class Expression_Select : Expression {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public readonly bool _isConstant;
    public readonly bool _onDatatype;
    public Expression_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant, bool onDatatype) : base() {
      this._expr = expr;
      this._field = field;
      this._isConstant = isConstant;
      this._onDatatype = onDatatype;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Select(_expr, _field, _isConstant, _onDatatype);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Select;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._field, oth._field) && this._isConstant == oth._isConstant && this._onDatatype == oth._onDatatype;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isConstant));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._onDatatype));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += this._field.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isConstant);
      s += ", ";
      s += Dafny.Helpers.ToString(this._onDatatype);
      s += ")";
      return s;
    }
  }
  public class Expression_SelectFn : Expression {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public readonly bool _onDatatype;
    public readonly bool _isStatic;
    public readonly BigInteger _arity;
    public Expression_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, BigInteger arity) : base() {
      this._expr = expr;
      this._field = field;
      this._onDatatype = onDatatype;
      this._isStatic = isStatic;
      this._arity = arity;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_SelectFn(_expr, _field, _onDatatype, _isStatic, _arity);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_SelectFn;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._field, oth._field) && this._onDatatype == oth._onDatatype && this._isStatic == oth._isStatic && this._arity == oth._arity;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._onDatatype));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isStatic));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arity));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.SelectFn";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += this._field.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._onDatatype);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isStatic);
      s += ", ";
      s += Dafny.Helpers.ToString(this._arity);
      s += ")";
      return s;
    }
  }
  public class Expression_TupleSelect : Expression {
    public readonly DAST._IExpression _expr;
    public readonly BigInteger _index;
    public Expression_TupleSelect(DAST._IExpression expr, BigInteger index) : base() {
      this._expr = expr;
      this._index = index;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_TupleSelect(_expr, _index);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_TupleSelect;
      return oth != null && object.Equals(this._expr, oth._expr) && this._index == oth._index;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._index));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.TupleSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._index);
      s += ")";
      return s;
    }
  }
  public class Expression_Call : Expression {
    public readonly DAST._IExpression _on;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<DAST._IType> _typeArgs;
    public readonly Dafny.ISequence<DAST._IExpression> _args;
    public Expression_Call(DAST._IExpression @on, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._on = @on;
      this._name = name;
      this._typeArgs = typeArgs;
      this._args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Call(_on, _name, _typeArgs, _args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Call;
      return oth != null && object.Equals(this._on, oth._on) && object.Equals(this._name, oth._name) && object.Equals(this._typeArgs, oth._typeArgs) && object.Equals(this._args, oth._args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArgs));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArgs);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ")";
      return s;
    }
  }
  public class Expression_Lambda : Expression {
    public readonly Dafny.ISequence<DAST._IFormal> _params;
    public readonly DAST._IType _retType;
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public Expression_Lambda(Dafny.ISequence<DAST._IFormal> @params, DAST._IType retType, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._params = @params;
      this._retType = retType;
      this._body = body;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Lambda(_params, _retType, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Lambda;
      return oth != null && object.Equals(this._params, oth._params) && object.Equals(this._retType, oth._retType) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Lambda";
      s += "(";
      s += Dafny.Helpers.ToString(this._params);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Expression_IIFE : Expression {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly DAST._IType _typ;
    public readonly DAST._IExpression _value;
    public readonly DAST._IExpression _iifeBody;
    public Expression_IIFE(Dafny.ISequence<Dafny.Rune> name, DAST._IType typ, DAST._IExpression @value, DAST._IExpression iifeBody) : base() {
      this._name = name;
      this._typ = typ;
      this._value = @value;
      this._iifeBody = iifeBody;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IIFE(_name, _typ, _value, _iifeBody);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IIFE;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typ, oth._typ) && object.Equals(this._value, oth._value) && object.Equals(this._iifeBody, oth._iifeBody);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._iifeBody));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IIFE";
      s += "(";
      s += Dafny.Helpers.ToString(this._name);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typ);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ", ";
      s += Dafny.Helpers.ToString(this._iifeBody);
      s += ")";
      return s;
    }
  }
  public class Expression_Apply : Expression {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<DAST._IExpression> _args;
    public Expression_Apply(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> args) : base() {
      this._expr = expr;
      this._args = args;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Apply(_expr, _args);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Apply;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._args, oth._args);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._args));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Apply";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._args);
      s += ")";
      return s;
    }
  }
  public class Expression_TypeTest : Expression {
    public readonly DAST._IExpression _on;
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _dType;
    public readonly Dafny.ISequence<Dafny.Rune> _variant;
    public Expression_TypeTest(DAST._IExpression @on, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dType, Dafny.ISequence<Dafny.Rune> variant) : base() {
      this._on = @on;
      this._dType = dType;
      this._variant = variant;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_TypeTest(_on, _dType, _variant);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_TypeTest;
      return oth != null && object.Equals(this._on, oth._on) && object.Equals(this._dType, oth._dType) && object.Equals(this._variant, oth._variant);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variant));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.TypeTest";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dType);
      s += ", ";
      s += this._variant.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expression_InitializationValue : Expression {
    public readonly DAST._IType _typ;
    public Expression_InitializationValue(DAST._IType typ) : base() {
      this._typ = typ;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_InitializationValue(_typ);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_InitializationValue;
      return oth != null && object.Equals(this._typ, oth._typ);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typ));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.InitializationValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._typ);
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
      return (int)hash;
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
      return (int)hash;
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
      return (int)hash;
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
    bool dtor_BoolLiteral_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_IntLiteral_a0 { get; }
    DAST._IType dtor_IntLiteral_a1 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a0 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a1 { get; }
    DAST._IType dtor_DecLiteral_a2 { get; }
    Dafny.ISequence<Dafny.Rune> dtor_StringLiteral_a0 { get; }
    Dafny.Rune dtor_CharLiteral_a0 { get; }
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
    public static _ILiteral create_Null() {
      return new Literal_Null();
    }
    public bool is_BoolLiteral { get { return this is Literal_BoolLiteral; } }
    public bool is_IntLiteral { get { return this is Literal_IntLiteral; } }
    public bool is_DecLiteral { get { return this is Literal_DecLiteral; } }
    public bool is_StringLiteral { get { return this is Literal_StringLiteral; } }
    public bool is_CharLiteral { get { return this is Literal_CharLiteral; } }
    public bool is_Null { get { return this is Literal_Null; } }
    public bool dtor_BoolLiteral_a0 {
      get {
        var d = this;
        return ((Literal_BoolLiteral)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_IntLiteral_a0 {
      get {
        var d = this;
        return ((Literal_IntLiteral)d)._a0;
      }
    }
    public DAST._IType dtor_IntLiteral_a1 {
      get {
        var d = this;
        return ((Literal_IntLiteral)d)._a1;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a0 {
      get {
        var d = this;
        return ((Literal_DecLiteral)d)._a0;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_DecLiteral_a1 {
      get {
        var d = this;
        return ((Literal_DecLiteral)d)._a1;
      }
    }
    public DAST._IType dtor_DecLiteral_a2 {
      get {
        var d = this;
        return ((Literal_DecLiteral)d)._a2;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_StringLiteral_a0 {
      get {
        var d = this;
        return ((Literal_StringLiteral)d)._a0;
      }
    }
    public Dafny.Rune dtor_CharLiteral_a0 {
      get {
        var d = this;
        return ((Literal_CharLiteral)d)._a0;
      }
    }
    public abstract _ILiteral DowncastClone();
  }
  public class Literal_BoolLiteral : Literal {
    public readonly bool _a0;
    public Literal_BoolLiteral(bool _a0) : base() {
      this._a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_BoolLiteral(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_BoolLiteral;
      return oth != null && this._a0 == oth._a0;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.BoolLiteral";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Literal_IntLiteral : Literal {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public readonly DAST._IType _a1;
    public Literal_IntLiteral(Dafny.ISequence<Dafny.Rune> _a0, DAST._IType _a1) : base() {
      this._a0 = _a0;
      this._a1 = _a1;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_IntLiteral(_a0, _a1);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_IntLiteral;
      return oth != null && object.Equals(this._a0, oth._a0) && object.Equals(this._a1, oth._a1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.IntLiteral";
      s += "(";
      s += this._a0.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._a1);
      s += ")";
      return s;
    }
  }
  public class Literal_DecLiteral : Literal {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public readonly Dafny.ISequence<Dafny.Rune> _a1;
    public readonly DAST._IType _a2;
    public Literal_DecLiteral(Dafny.ISequence<Dafny.Rune> _a0, Dafny.ISequence<Dafny.Rune> _a1, DAST._IType _a2) : base() {
      this._a0 = _a0;
      this._a1 = _a1;
      this._a2 = _a2;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_DecLiteral(_a0, _a1, _a2);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_DecLiteral;
      return oth != null && object.Equals(this._a0, oth._a0) && object.Equals(this._a1, oth._a1) && object.Equals(this._a2, oth._a2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a2));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.DecLiteral";
      s += "(";
      s += this._a0.ToVerbatimString(true);
      s += ", ";
      s += this._a1.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._a2);
      s += ")";
      return s;
    }
  }
  public class Literal_StringLiteral : Literal {
    public readonly Dafny.ISequence<Dafny.Rune> _a0;
    public Literal_StringLiteral(Dafny.ISequence<Dafny.Rune> _a0) : base() {
      this._a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_StringLiteral(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_StringLiteral;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.StringLiteral";
      s += "(";
      s += this._a0.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Literal_CharLiteral : Literal {
    public readonly Dafny.Rune _a0;
    public Literal_CharLiteral(Dafny.Rune _a0) : base() {
      this._a0 = _a0;
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_CharLiteral(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_CharLiteral;
      return oth != null && this._a0 == oth._a0;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.CharLiteral";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
      s += ")";
      return s;
    }
  }
  public class Literal_Null : Literal {
    public Literal_Null() : base() {
    }
    public override _ILiteral DowncastClone() {
      if (this is _ILiteral dt) { return dt; }
      return new Literal_Null();
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Literal_Null;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Literal.Null";
      return s;
    }
  }
} // end of namespace DAST
namespace DCOMP {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> natToString(BigInteger n) {
      if ((n).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0");
      } else if ((n) == (BigInteger.One)) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1");
      } else if ((n) == (new BigInteger(2))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("2");
      } else if ((n) == (new BigInteger(3))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("3");
      } else if ((n) == (new BigInteger(4))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("4");
      } else if ((n) == (new BigInteger(5))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("5");
      } else if ((n) == (new BigInteger(6))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("6");
      } else if ((n) == (new BigInteger(7))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("7");
      } else if ((n) == (new BigInteger(8))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("8");
      } else if ((n) == (new BigInteger(9))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("9");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.natToString(Dafny.Helpers.EuclideanDivision(n, new BigInteger(10))), DCOMP.__default.natToString(Dafny.Helpers.EuclideanModulus(n, new BigInteger(10))));
      }
    }
  }

  public partial class stringNat {
    private static readonly Dafny.ISequence<Dafny.Rune> Witness = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1");
    public static Dafny.ISequence<Dafny.Rune> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(DCOMP.stringNat.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class COMP {
    public COMP() {
    }
    public static Dafny.ISequence<Dafny.Rune> GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> body;
      Dafny.ISequence<Dafny.Rune> _out0;
      _out0 = DCOMP.COMP.GenModuleBody((mod).dtor_body, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
      body = _out0;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod r#"), (mod).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger i;
      i = BigInteger.Zero;
      while ((i) < (new BigInteger((body).Count))) {
        Dafny.ISequence<Dafny.Rune> generated = Dafny.Sequence<Dafny.Rune>.Empty;
        DAST._IModuleItem _source0 = (body).Select(i);
        if (_source0.is_Module) {
          DAST._IModule __mcc_h0 = _source0.dtor_Module_a0;
          DAST._IModule m = __mcc_h0;
          Dafny.ISequence<Dafny.Rune> _out1;
          _out1 = DCOMP.COMP.GenModule(m, containingPath);
          generated = _out1;
        } else if (_source0.is_Class) {
          DAST._IClass __mcc_h1 = _source0.dtor_Class_a0;
          DAST._IClass c = __mcc_h1;
          Dafny.ISequence<Dafny.Rune> _out2;
          _out2 = DCOMP.COMP.GenClass(c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name)));
          generated = _out2;
        } else if (_source0.is_Trait) {
          DAST._ITrait __mcc_h2 = _source0.dtor_Trait_a0;
          DAST._ITrait t = __mcc_h2;
          Dafny.ISequence<Dafny.Rune> _out3;
          _out3 = DCOMP.COMP.GenTrait(t, containingPath);
          generated = _out3;
        } else if (_source0.is_Newtype) {
          DAST._INewtype __mcc_h3 = _source0.dtor_Newtype_a0;
          DAST._INewtype _10_n = __mcc_h3;
          Dafny.ISequence<Dafny.Rune> _out4;
          _out4 = DCOMP.COMP.GenNewtype(_10_n);
          generated = _out4;
        } else {
          DAST._IDatatype _11___mcc_h4 = _source0.dtor_Datatype_a0;
          DAST._IDatatype _12_d = _11___mcc_h4;
          Dafny.ISequence<Dafny.Rune> _out5;
          _out5 = DCOMP.COMP.GenDatatype(_12_d);
          generated = _out5;
        }
        if ((i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, generated);
        i = (i) + (BigInteger.One);
      }
      return s;
    }
    public static void GenTypeParameters(Dafny.ISequence<DAST._IType> @params, out Dafny.ISet<DAST._IType> typeParamsSet, out Dafny.ISequence<Dafny.Rune> typeParams, out Dafny.ISequence<Dafny.Rune> constrainedTypeParams) {
      typeParamsSet = Dafny.Set<DAST._IType>.Empty;
      typeParams = Dafny.Sequence<Dafny.Rune>.Empty;
      constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Empty;
      typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _13_tpI;
      _13_tpI = BigInteger.Zero;
      if ((new BigInteger((@params).Count)).Sign == 1) {
        typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_13_tpI) < (new BigInteger((@params).Count))) {
          DAST._IType _14_tp;
          _14_tp = (@params).Select(_13_tpI);
          typeParamsSet = Dafny.Set<DAST._IType>.Union(typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_14_tp));
          Dafny.ISequence<Dafny.Rune> _15_genTp;
          Dafny.ISequence<Dafny.Rune> _out6;
          _out6 = DCOMP.COMP.GenType(_14_tp, false, false);
          _15_genTp = _out6;
          typeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(typeParams, _15_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(constrainedTypeParams, _15_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<")), _15_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> + Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, "));
          _13_tpI = (_13_tpI) + (BigInteger.One);
        }
        typeParams = Dafny.Sequence<Dafny.Rune>.Concat(typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        constrainedTypeParams = Dafny.Sequence<Dafny.Rune>.Concat(constrainedTypeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _16_typeParamsSet;
      Dafny.ISequence<Dafny.Rune> _17_typeParams;
      Dafny.ISequence<Dafny.Rune> _18_constrainedTypeParams;
      Dafny.ISet<DAST._IType> _out7;
      Dafny.ISequence<Dafny.Rune> _out8;
      Dafny.ISequence<Dafny.Rune> _out9;
      DCOMP.COMP.GenTypeParameters((c).dtor_typeParams, out _out7, out _out8, out _out9);
      _16_typeParamsSet = _out7;
      _17_typeParams = _out8;
      _18_constrainedTypeParams = _out9;
      Dafny.ISequence<Dafny.Rune> _19_fields;
      _19_fields = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Dafny.ISequence<Dafny.Rune> _20_fieldInits;
      _20_fieldInits = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _21_fieldI;
      _21_fieldI = BigInteger.Zero;
      while ((_21_fieldI) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _22_field;
        _22_field = ((c).dtor_fields).Select(_21_fieldI);
        Dafny.ISequence<Dafny.Rune> _23_fieldType;
        Dafny.ISequence<Dafny.Rune> _out10;
        _out10 = DCOMP.COMP.GenType(((_22_field).dtor_formal).dtor_typ, false, false);
        _23_fieldType = _out10;
        _19_fields = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_19_fields, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub r#")), ((_22_field).dtor_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::std::cell::RefCell<")), _23_fieldType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">,\n"));
        DAST._IOptional<DAST._IExpression> _source1 = (_22_field).dtor_defaultValue;
        if (_source1.is_Some) {
          DAST._IExpression _24___mcc_h0 = _source1.dtor_Some_a0;
          DAST._IExpression _25_e = _24___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _26_eStr;
            bool _27___v1;
            bool _28___v2;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _29___v3;
            Dafny.ISequence<Dafny.Rune> _out11;
            bool _out12;
            bool _out13;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out14;
            DCOMP.COMP.GenExpr(_25_e, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out11, out _out12, out _out13, out _out14);
            _26_eStr = _out11;
            _27___v1 = _out12;
            _28___v2 = _out13;
            _29___v3 = _out14;
            _20_fieldInits = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_20_fieldInits, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), ((_22_field).dtor_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::std::cell::RefCell::new(")), _26_eStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("),\n"));
          }
        } else {
          {
            _20_fieldInits = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_20_fieldInits, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), ((_22_field).dtor_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::std::cell::RefCell::new(::std::default::Default::default()),\n"));
          }
        }
        _21_fieldI = (_21_fieldI) + (BigInteger.One);
      }
      BigInteger _30_typeParamI;
      _30_typeParamI = BigInteger.Zero;
      while ((_30_typeParamI) < (new BigInteger(((c).dtor_typeParams).Count))) {
        Dafny.ISequence<Dafny.Rune> _31_tpeGen;
        Dafny.ISequence<Dafny.Rune> _out15;
        _out15 = DCOMP.COMP.GenType(((c).dtor_typeParams).Select(_30_typeParamI), false, false);
        _31_tpeGen = _out15;
        _19_fields = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_19_fields, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_")), DCOMP.__default.natToString(_30_typeParamI)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::std::marker::PhantomData<")), _31_tpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">,\n"));
        _20_fieldInits = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_20_fieldInits, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_")), DCOMP.__default.natToString(_30_typeParamI)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::std::marker::PhantomData,\n"));
        _30_typeParamI = (_30_typeParamI) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub struct r#"), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _19_fields), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      Dafny.ISequence<Dafny.Rune> _32_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _33_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out16;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out17;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(path)), Dafny.Set<DAST._IType>.FromElements(), out _out16, out _out17);
      _32_implBody = _out16;
      _33_traitBodies = _out17;
      _32_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn new() -> Self {\n"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _20_fieldInits), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n}\n")), _32_implBody);
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _32_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _34_i;
        _34_i = BigInteger.Zero;
        while ((_34_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _35_superClass;
          _35_superClass = ((c).dtor_superClasses).Select(_34_i);
          DAST._IType _source2 = _35_superClass;
          if (_source2.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _36___mcc_h1 = _source2.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _37___mcc_h2 = _source2.dtor_typeArgs;
            DAST._IResolvedType _38___mcc_h3 = _source2.dtor_resolved;
            DAST._IResolvedType _source3 = _38___mcc_h3;
            if (_source3.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _39___mcc_h7 = _source3.dtor_path;
            } else if (_source3.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _40___mcc_h9 = _source3.dtor_path;
              Dafny.ISequence<DAST._IType> _41_typeArgs = _37___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _42_traitPath = _36___mcc_h1;
              {
                Dafny.ISequence<Dafny.Rune> _43_pathStr;
                Dafny.ISequence<Dafny.Rune> _out18;
                _out18 = DCOMP.COMP.GenPath(_42_traitPath);
                _43_pathStr = _out18;
                Dafny.ISequence<Dafny.Rune> _44_typeArgs;
                Dafny.ISequence<Dafny.Rune> _out19;
                _out19 = DCOMP.COMP.GenTypeArgs(_41_typeArgs, false, false);
                _44_typeArgs = _out19;
                Dafny.ISequence<Dafny.Rune> _45_body;
                _45_body = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                if ((_33_traitBodies).Contains(_42_traitPath)) {
                  _45_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(_33_traitBodies, _42_traitPath);
                }
                Dafny.ISequence<Dafny.Rune> _46_genSelfPath;
                Dafny.ISequence<Dafny.Rune> _out20;
                _out20 = DCOMP.COMP.GenPath(path);
                _46_genSelfPath = _out20;
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nimpl ")), _43_pathStr), _44_typeArgs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" for ::std::rc::Rc<")), _46_genSelfPath), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> {\n")), _45_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
              }
            } else {
              DAST._IType _47___mcc_h11 = _source3.dtor_Newtype_a0;
            }
          } else if (_source2.is_Tuple) {
            Dafny.ISequence<DAST._IType> _48___mcc_h13 = _source2.dtor_Tuple_a0;
          } else if (_source2.is_Array) {
            DAST._IType _49___mcc_h15 = _source2.dtor_element;
          } else if (_source2.is_Seq) {
            DAST._IType _50___mcc_h17 = _source2.dtor_element;
          } else if (_source2.is_Set) {
            DAST._IType _51___mcc_h19 = _source2.dtor_element;
          } else if (_source2.is_Multiset) {
            DAST._IType _52___mcc_h21 = _source2.dtor_element;
          } else if (_source2.is_Map) {
            DAST._IType _53___mcc_h23 = _source2.dtor_key;
            DAST._IType _54___mcc_h24 = _source2.dtor_value;
          } else if (_source2.is_Arrow) {
            Dafny.ISequence<DAST._IType> _55___mcc_h27 = _source2.dtor_args;
            DAST._IType _56___mcc_h28 = _source2.dtor_result;
          } else if (_source2.is_Primitive) {
            DAST._IPrimitive _57___mcc_h31 = _source2.dtor_Primitive_a0;
          } else if (_source2.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _58___mcc_h33 = _source2.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _59___mcc_h35 = _source2.dtor_TypeArg_a0;
          }
          _34_i = (_34_i) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.Rune> _60_defaultImpl;
      _60_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      _60_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_60_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n"));
      _60_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_60_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()\n"));
      _60_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_60_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      _60_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_60_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      Dafny.ISequence<Dafny.Rune> _61_printImpl;
      _61_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n"));
      _61_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_61_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(__fmt_print_formatter, \"r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((new BigInteger(((c).dtor_fields).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"));
      BigInteger _62_i;
      _62_i = BigInteger.Zero;
      while ((_62_i) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _63_field;
        _63_field = ((c).dtor_fields).Select(_62_i);
        if ((_62_i).Sign == 1) {
          _61_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \", \")?;"));
        }
        _61_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_61_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(::std::ops::Deref::deref(&(self.r#")), ((_63_field).dtor_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow())), __fmt_print_formatter, false)?;"));
        _62_i = (_62_i) + (BigInteger.One);
      }
      _61_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \")\")?;\nOk(())\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _64_ptrPartialEqImpl;
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::cmp::PartialEq for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_64_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn eq(&self, other: &Self) -> bool {\n"));
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_64_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)"));
      _64_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_64_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _60_defaultImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _61_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _64_ptrPartialEqImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _65_typeParamsSet;
      _65_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<Dafny.Rune> _66_typeParams;
      _66_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _67_tpI;
      _67_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        _66_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_67_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _68_tp;
          _68_tp = ((t).dtor_typeParams).Select(_67_tpI);
          _65_typeParamsSet = Dafny.Set<DAST._IType>.Union(_65_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_68_tp));
          Dafny.ISequence<Dafny.Rune> _69_genTp;
          Dafny.ISequence<Dafny.Rune> _out21;
          _out21 = DCOMP.COMP.GenType(_68_tp, false, false);
          _69_genTp = _out21;
          _66_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_66_typeParams, _69_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          _67_tpI = (_67_tpI) + (BigInteger.One);
        }
        _66_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(_66_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _70_fullPath;
      _70_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<Dafny.Rune> _71_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _72___v6;
      Dafny.ISequence<Dafny.Rune> _out22;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out23;
      DCOMP.COMP.GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_70_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_70_fullPath)), _65_typeParamsSet, out _out22, out _out23);
      _71_implBody = _out22;
      _72___v6 = _out23;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub trait r#"), (t).dtor_name), _66_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _71_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenNewtype(DAST._INewtype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _73_typeParamsSet;
      Dafny.ISequence<Dafny.Rune> _74_typeParams;
      Dafny.ISequence<Dafny.Rune> _75_constrainedTypeParams;
      Dafny.ISet<DAST._IType> _out24;
      Dafny.ISequence<Dafny.Rune> _out25;
      Dafny.ISequence<Dafny.Rune> _out26;
      DCOMP.COMP.GenTypeParameters((c).dtor_typeParams, out _out24, out _out25, out _out26);
      _73_typeParamsSet = _out24;
      _74_typeParams = _out25;
      _75_constrainedTypeParams = _out26;
      Dafny.ISequence<Dafny.Rune> _76_underlyingType;
      Dafny.ISequence<Dafny.Rune> _out27;
      _out27 = DCOMP.COMP.GenType((c).dtor_base, false, false);
      _76_underlyingType = _out27;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]\n#[repr(transparent)]\npub struct r#"), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(pub ")), _76_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _75_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyErasable for r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Erased = ")), _76_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn erase(&self) -> &Self::Erased {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn erase_owned(self) -> Self::Erased {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.0\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _75_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<")), _76_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase(x: &")), _76_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> &Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe { &*(x as *const ")), _76_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as *const r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") }\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase_owned(x: ")), _76_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(x)\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _75_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase(x: &r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> &Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase_owned(x: r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _75_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n"));
      DAST._IOptional<DAST._IExpression> _source4 = (c).dtor_witnessExpr;
      if (_source4.is_Some) {
        DAST._IExpression _77___mcc_h0 = _source4.dtor_Some_a0;
        DAST._IExpression _78_e = _77___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _79_eStr;
          bool _80___v7;
          bool _81___v8;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _82___v9;
          Dafny.ISequence<Dafny.Rune> _out28;
          bool _out29;
          bool _out30;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out31;
          DCOMP.COMP.GenExpr(_78_e, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out28, out _out29, out _out30, out _out31);
          _79_eStr = _out28;
          _80___v7 = _out29;
          _81___v8 = _out30;
          _82___v9 = _out31;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _79_eStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
        }
      } else {
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())\n"));
        }
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _75_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _74_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, __fmt_print_formatter, in_seq)\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenDatatype(DAST._IDatatype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _83_typeParamsSet;
      Dafny.ISequence<Dafny.Rune> _84_typeParams;
      Dafny.ISequence<Dafny.Rune> _85_constrainedTypeParams;
      Dafny.ISet<DAST._IType> _out32;
      Dafny.ISequence<Dafny.Rune> _out33;
      Dafny.ISequence<Dafny.Rune> _out34;
      DCOMP.COMP.GenTypeParameters((c).dtor_typeParams, out _out32, out _out33, out _out34);
      _83_typeParamsSet = _out32;
      _84_typeParams = _out33;
      _85_constrainedTypeParams = _out34;
      Dafny.ISequence<Dafny.Rune> _86_ctors;
      _86_ctors = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _87_i;
      _87_i = BigInteger.Zero;
      while ((_87_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _88_ctor;
        _88_ctor = ((c).dtor_ctors).Select(_87_i);
        Dafny.ISequence<Dafny.Rune> _89_ctorBody;
        _89_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_88_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        BigInteger _90_j;
        _90_j = BigInteger.Zero;
        while ((_90_j) < (new BigInteger(((_88_ctor).dtor_args).Count))) {
          DAST._IFormal _91_formal;
          _91_formal = ((_88_ctor).dtor_args).Select(_90_j);
          Dafny.ISequence<Dafny.Rune> _92_formalType;
          Dafny.ISequence<Dafny.Rune> _out35;
          _out35 = DCOMP.COMP.GenType((_91_formal).dtor_typ, false, false);
          _92_formalType = _out35;
          if ((c).dtor_isCo) {
            _89_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_89_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_91_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper<")), _92_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">, "));
          } else {
            _89_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_89_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_91_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _92_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          _90_j = (_90_j) + (BigInteger.One);
        }
        _89_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(_89_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        _86_ctors = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_86_ctors, _89_ctorBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
        _87_i = (_87_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _93_selfPath;
      _93_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _94_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _95_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out37;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_93_selfPath)), _83_typeParamsSet, out _out36, out _out37);
      _94_implBody = _out36;
      _95_traitBodies = _out37;
      _87_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _96_emittedFields;
      _96_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_87_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _97_ctor;
        _97_ctor = ((c).dtor_ctors).Select(_87_i);
        BigInteger _98_j;
        _98_j = BigInteger.Zero;
        while ((_98_j) < (new BigInteger(((_97_ctor).dtor_args).Count))) {
          DAST._IFormal _99_formal;
          _99_formal = ((_97_ctor).dtor_args).Select(_98_j);
          if (!((_96_emittedFields).Contains((_99_formal).dtor_name))) {
            _96_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_96_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_99_formal).dtor_name));
            Dafny.ISequence<Dafny.Rune> _100_formalType;
            Dafny.ISequence<Dafny.Rune> _out38;
            _out38 = DCOMP.COMP.GenType((_99_formal).dtor_typ, false, false);
            _100_formalType = _out38;
            Dafny.ISequence<Dafny.Rune> _101_methodBody;
            _101_methodBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n");
            BigInteger _102_k;
            _102_k = BigInteger.Zero;
            while ((_102_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _103_ctor2;
              _103_ctor2 = ((c).dtor_ctors).Select(_102_k);
              Dafny.ISequence<Dafny.Rune> _104_ctorMatch;
              _104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_103_ctor2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              BigInteger _105_l;
              _105_l = BigInteger.Zero;
              bool _106_hasMatchingField;
              _106_hasMatchingField = false;
              while ((_105_l) < (new BigInteger(((_103_ctor2).dtor_args).Count))) {
                DAST._IFormal _107_formal2;
                _107_formal2 = ((_103_ctor2).dtor_args).Select(_105_l);
                if (((_99_formal).dtor_name).Equals((_107_formal2).dtor_name)) {
                  _106_hasMatchingField = true;
                }
                _104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_104_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_107_formal2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _105_l = (_105_l) + (BigInteger.One);
              }
              if (_106_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_104_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ::std::ops::Deref::deref(&")), (_99_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0),\n"));
                } else {
                  _104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_104_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ")), (_99_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
                }
              } else {
                _104_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_104_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => panic!(\"field does not exist on this variant\"),\n"));
              }
              _101_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_101_methodBody, _104_ctorMatch);
              _102_k = (_102_k) + (BigInteger.One);
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _101_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_101_methodBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..) => panic!(),\n"));
            }
            _101_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_101_methodBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _94_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_94_implBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#")), (_99_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&self) -> &")), _100_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _101_methodBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
          }
          _98_j = (_98_j) + (BigInteger.One);
        }
        _87_i = (_87_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _86_ctors = Dafny.Sequence<Dafny.Rune>.Concat(_86_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant("));
        BigInteger _108_typeI;
        _108_typeI = BigInteger.Zero;
        while ((_108_typeI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          if ((_108_typeI).Sign == 1) {
            _86_ctors = Dafny.Sequence<Dafny.Rune>.Concat(_86_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _109_genTp;
          Dafny.ISequence<Dafny.Rune> _out39;
          _out39 = DCOMP.COMP.GenType(((c).dtor_typeParams).Select(_108_typeI), false, false);
          _109_genTp = _out39;
          _86_ctors = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_86_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData::<")), _109_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          _108_typeI = (_108_typeI) + (BigInteger.One);
        }
        _86_ctors = Dafny.Sequence<Dafny.Rune>.Concat(_86_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      Dafny.ISequence<Dafny.Rune> _110_enumBody;
      _110_enumBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]\npub enum r#"), (c).dtor_name), _84_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _86_ctors), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _85_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" r#")), (c).dtor_name), _84_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _94_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      Dafny.ISequence<Dafny.Rune> _111_identEraseImpls;
      _111_identEraseImpls = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _85_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyErasable for r#")), (c).dtor_name), _84_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Erased = Self;\nfn erase(&self) -> &Self::Erased { self }\nfn erase_owned(self) -> Self::Erased { self }}\n"));
      _111_identEraseImpls = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_111_identEraseImpls, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _85_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<r#")), (c).dtor_name), _84_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _84_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn unerase(x: &Self) -> &Self { x }\nfn unerase_owned(x: Self) -> Self { x }}\n"));
      Dafny.ISequence<Dafny.Rune> _112_printImpl;
      _112_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _85_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _84_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n"));
      _87_i = BigInteger.Zero;
      while ((_87_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _113_ctor;
        _113_ctor = ((c).dtor_ctors).Select(_87_i);
        Dafny.ISequence<Dafny.Rune> _114_ctorMatch;
        _114_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_113_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _115_modulePrefix;
        _115_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _116_printRhs;
        _116_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(__fmt_print_formatter, \""), _115_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (_113_ctor).dtor_name), (((_113_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?;")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"))));
        BigInteger _117_j;
        _117_j = BigInteger.Zero;
        while ((_117_j) < (new BigInteger(((_113_ctor).dtor_args).Count))) {
          DAST._IFormal _118_formal;
          _118_formal = ((_113_ctor).dtor_args).Select(_117_j);
          _114_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_114_ctorMatch, (_118_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_117_j).Sign == 1) {
            _116_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_116_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \", \")?;"));
          }
          _116_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_116_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(")), (_118_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", __fmt_print_formatter, false)?;"));
          _117_j = (_117_j) + (BigInteger.One);
        }
        _114_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_114_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_113_ctor).dtor_hasAnyArgs) {
          _116_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_116_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \")\")?;"));
        }
        _116_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_116_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nOk(())"));
        _112_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_112_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _114_ctorMatch), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" => {\n")), _116_printRhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
        _87_i = (_87_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _112_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_112_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..) => {panic!()\n}\n"));
      }
      _112_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_112_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _119_defaultImpl;
      _119_defaultImpl = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _119_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _85_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _84_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
        _87_i = BigInteger.Zero;
        while ((_87_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _120_formal;
          _120_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_87_i);
          _119_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_119_defaultImpl, (_120_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": std::default::Default::default(),\n"));
          _87_i = (_87_i) + (BigInteger.One);
        }
        _119_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_119_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_110_enumBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _111_identEraseImpls), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _112_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _119_defaultImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((new BigInteger((p).Count)).Sign == 0) {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        return s;
      } else {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super::");
        BigInteger _121_i;
        _121_i = BigInteger.Zero;
        while ((_121_i) < (new BigInteger((p).Count))) {
          if ((_121_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), ((p).Select(_121_i)));
          _121_i = (_121_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((args).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _122_i;
        _122_i = BigInteger.Zero;
        while ((_122_i) < (new BigInteger((args).Count))) {
          if ((_122_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _123_genTp;
          Dafny.ISequence<Dafny.Rune> _out40;
          _out40 = DCOMP.COMP.GenType((args).Select(_122_i), inBinding, inFn);
          _123_genTp = _out40;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _123_genTp);
          _122_i = (_122_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenType(DAST._IType c, bool inBinding, bool inFn) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      DAST._IType _source5 = c;
      if (_source5.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _124___mcc_h0 = _source5.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _125___mcc_h1 = _source5.dtor_typeArgs;
        DAST._IResolvedType _126___mcc_h2 = _source5.dtor_resolved;
        DAST._IResolvedType _127_resolved = _126___mcc_h2;
        Dafny.ISequence<DAST._IType> _128_args = _125___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _129_p = _124___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _out41;
          _out41 = DCOMP.COMP.GenPath(_129_p);
          s = _out41;
          Dafny.ISequence<Dafny.Rune> _130_typeArgs;
          Dafny.ISequence<Dafny.Rune> _out42;
          _out42 = DCOMP.COMP.GenTypeArgs(_128_args, inBinding, inFn);
          _130_typeArgs = _out42;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _130_typeArgs);
          DAST._IResolvedType _source6 = _127_resolved;
          if (_source6.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _131___mcc_h16 = _source6.dtor_path;
            {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            }
          } else if (_source6.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _132___mcc_h18 = _source6.dtor_path;
            {
              if (inBinding) {
                s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_");
              } else {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              }
            }
          } else {
            DAST._IType _133___mcc_h20 = _source6.dtor_Newtype_a0;
            DAST._IResolvedType _134_Primitive = _127_resolved;
          }
        }
      } else if (_source5.is_Tuple) {
        Dafny.ISequence<DAST._IType> _135___mcc_h3 = _source5.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _136_types = _135___mcc_h3;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          BigInteger _137_i;
          _137_i = BigInteger.Zero;
          while ((_137_i) < (new BigInteger((_136_types).Count))) {
            if ((_137_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _138_generated;
            Dafny.ISequence<Dafny.Rune> _out43;
            _out43 = DCOMP.COMP.GenType((_136_types).Select(_137_i), inBinding, inFn);
            _138_generated = _out43;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _138_generated), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            _137_i = (_137_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else if (_source5.is_Array) {
        DAST._IType _139___mcc_h4 = _source5.dtor_element;
        DAST._IType _140_element = _139___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _141_elemStr;
          Dafny.ISequence<Dafny.Rune> _out44;
          _out44 = DCOMP.COMP.GenType(_140_element, inBinding, inFn);
          _141_elemStr = _out44;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::vec::Vec<"), _141_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Seq) {
        DAST._IType _142___mcc_h5 = _source5.dtor_element;
        DAST._IType _143_element = _142___mcc_h5;
        {
          Dafny.ISequence<Dafny.Rune> _144_elemStr;
          Dafny.ISequence<Dafny.Rune> _out45;
          _out45 = DCOMP.COMP.GenType(_143_element, inBinding, inFn);
          _144_elemStr = _out45;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::vec::Vec<"), _144_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Set) {
        DAST._IType _145___mcc_h6 = _source5.dtor_element;
        DAST._IType _146_element = _145___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _147_elemStr;
          Dafny.ISequence<Dafny.Rune> _out46;
          _out46 = DCOMP.COMP.GenType(_146_element, inBinding, inFn);
          _147_elemStr = _out46;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashSet<"), _147_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Multiset) {
        DAST._IType _148___mcc_h7 = _source5.dtor_element;
        DAST._IType _149_element = _148___mcc_h7;
        {
          Dafny.ISequence<Dafny.Rune> _150_elemStr;
          Dafny.ISequence<Dafny.Rune> _out47;
          _out47 = DCOMP.COMP.GenType(_149_element, inBinding, inFn);
          _150_elemStr = _out47;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _150_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", u64>"));
        }
      } else if (_source5.is_Map) {
        DAST._IType _151___mcc_h8 = _source5.dtor_key;
        DAST._IType _152___mcc_h9 = _source5.dtor_value;
        DAST._IType _153_value = _152___mcc_h9;
        DAST._IType _154_key = _151___mcc_h8;
        {
          Dafny.ISequence<Dafny.Rune> _155_keyStr;
          Dafny.ISequence<Dafny.Rune> _out48;
          _out48 = DCOMP.COMP.GenType(_154_key, inBinding, inFn);
          _155_keyStr = _out48;
          Dafny.ISequence<Dafny.Rune> _156_valueStr;
          Dafny.ISequence<Dafny.Rune> _out49;
          _out49 = DCOMP.COMP.GenType(_153_value, inBinding, inFn);
          _156_valueStr = _out49;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _155_keyStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _156_valueStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Arrow) {
        Dafny.ISequence<DAST._IType> _157___mcc_h10 = _source5.dtor_args;
        DAST._IType _158___mcc_h11 = _source5.dtor_result;
        DAST._IType _159_result = _158___mcc_h11;
        Dafny.ISequence<DAST._IType> _160_args = _157___mcc_h10;
        {
          if (inBinding) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<_>");
          } else {
            if (inFn) {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<::std::boxed::Box<dyn ::std::ops::Fn(");
            } else {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<impl ::std::ops::Fn(");
            }
            BigInteger _161_i;
            _161_i = BigInteger.Zero;
            while ((_161_i) < (new BigInteger((_160_args).Count))) {
              if ((_161_i).Sign == 1) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _162_generated;
              Dafny.ISequence<Dafny.Rune> _out50;
              _out50 = DCOMP.COMP.GenType((_160_args).Select(_161_i), inBinding, true);
              _162_generated = _out50;
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), _162_generated);
              _161_i = (_161_i) + (BigInteger.One);
            }
            Dafny.ISequence<Dafny.Rune> _163_resultType;
            Dafny.ISequence<Dafny.Rune> _out51;
            _out51 = DCOMP.COMP.GenType(_159_result, inBinding, inFn);
            _163_resultType = _out51;
            if (inFn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _163_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + 'static>>"));
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _163_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + Clone + 'static>"));
            }
          }
        }
      } else if (_source5.is_Primitive) {
        DAST._IPrimitive _164___mcc_h12 = _source5.dtor_Primitive_a0;
        DAST._IPrimitive _165_p = _164___mcc_h12;
        {
          DAST._IPrimitive _source7 = _165_p;
          if (_source7.is_Int) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt");
          } else if (_source7.is_Real) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational");
          } else if (_source7.is_String) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Vec<char>");
          } else if (_source7.is_Bool) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool");
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char");
          }
        }
      } else if (_source5.is_Passthrough) {
        Dafny.ISequence<Dafny.Rune> _166___mcc_h13 = _source5.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _167_v = _166___mcc_h13;
        s = _167_v;
      } else {
        Dafny.ISequence<Dafny.Rune> _168___mcc_h14 = _source5.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source8 = _168___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _169___mcc_h15 = _source8;
        Dafny.ISequence<Dafny.Rune> _170_name = _169___mcc_h15;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _170_name);
      }
      return s;
    }
    public static void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<Dafny.Rune> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> traitBodies) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _171_i;
      _171_i = BigInteger.Zero;
      while ((_171_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source9 = (body).Select(_171_i);
        DAST._IMethod _172___mcc_h0 = _source9;
        DAST._IMethod _173_m = _172___mcc_h0;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source10 = (_173_m).dtor_overridingPath;
          if (_source10.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _174___mcc_h1 = _source10.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _175_p = _174___mcc_h1;
            {
              Dafny.ISequence<Dafny.Rune> _176_existing;
              _176_existing = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              if ((traitBodies).Contains(_175_p)) {
                _176_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(traitBodies, _175_p);
              }
              if ((new BigInteger((_176_existing).Count)).Sign == 1) {
                _176_existing = Dafny.Sequence<Dafny.Rune>.Concat(_176_existing, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
              }
              Dafny.ISequence<Dafny.Rune> _177_genMethod;
              Dafny.ISequence<Dafny.Rune> _out52;
              _out52 = DCOMP.COMP.GenMethod(_173_m, true, enclosingType, enclosingTypeParams);
              _177_genMethod = _out52;
              _176_existing = Dafny.Sequence<Dafny.Rune>.Concat(_176_existing, _177_genMethod);
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>(_175_p, _176_existing)));
            }
          } else {
            {
              Dafny.ISequence<Dafny.Rune> _178_generated;
              Dafny.ISequence<Dafny.Rune> _out53;
              _out53 = DCOMP.COMP.GenMethod(_173_m, forTrait, enclosingType, enclosingTypeParams);
              _178_generated = _out53;
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, _178_generated);
            }
          }
        }
        if ((new BigInteger((s).Count)).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        _171_i = (_171_i) + (BigInteger.One);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GenParams(Dafny.ISequence<DAST._IFormal> @params) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _179_i;
      _179_i = BigInteger.Zero;
      while ((_179_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _180_param;
        _180_param = (@params).Select(_179_i);
        Dafny.ISequence<Dafny.Rune> _181_paramType;
        Dafny.ISequence<Dafny.Rune> _out54;
        _out54 = DCOMP.COMP.GenType((_180_param).dtor_typ, false, false);
        _181_paramType = _out54;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_180_param).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _181_paramType);
        if ((_179_i) < ((new BigInteger((@params).Count)) - (BigInteger.One))) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        _179_i = (_179_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _182_params;
      Dafny.ISequence<Dafny.Rune> _out55;
      _out55 = DCOMP.COMP.GenParams((m).dtor_params);
      _182_params = _out55;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _183_paramNames;
      _183_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _184_paramI;
      _184_paramI = BigInteger.Zero;
      while ((_184_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _183_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_183_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_184_paramI)).dtor_name));
        _184_paramI = (_184_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _182_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _182_params);
        } else {
          Dafny.ISequence<Dafny.Rune> _185_enclosingTypeString;
          Dafny.ISequence<Dafny.Rune> _out56;
          _out56 = DCOMP.COMP.GenType(enclosingType, false, false);
          _185_enclosingTypeString = _out56;
          _182_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self: &"), _185_enclosingTypeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _182_params);
        }
      }
      Dafny.ISequence<Dafny.Rune> _186_retType;
      _186_retType = (((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      BigInteger _187_typeI;
      _187_typeI = BigInteger.Zero;
      while ((_187_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        if ((_187_typeI).Sign == 1) {
          _186_retType = Dafny.Sequence<Dafny.Rune>.Concat(_186_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        Dafny.ISequence<Dafny.Rune> _188_typeString;
        Dafny.ISequence<Dafny.Rune> _out57;
        _out57 = DCOMP.COMP.GenType(((m).dtor_outTypes).Select(_187_typeI), false, false);
        _188_typeString = _out57;
        _186_retType = Dafny.Sequence<Dafny.Rune>.Concat(_186_retType, _188_typeString);
        _187_typeI = (_187_typeI) + (BigInteger.One);
      }
      if ((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) {
        _186_retType = Dafny.Sequence<Dafny.Rune>.Concat(_186_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      if (forTrait) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn r#"), (m).dtor_name);
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#"), (m).dtor_name);
      }
      Dafny.ISequence<DAST._IType> _189_typeParamsFiltered;
      _189_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _190_typeParamI;
      _190_typeParamI = BigInteger.Zero;
      while ((_190_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _191_typeParam;
        _191_typeParam = ((m).dtor_typeParams).Select(_190_typeParamI);
        if (!((enclosingTypeParams).Contains(_191_typeParam))) {
          _189_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_189_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_191_typeParam));
        }
        _190_typeParamI = (_190_typeParamI) + (BigInteger.One);
      }
      if ((new BigInteger((_189_typeParamsFiltered).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _192_i;
        _192_i = BigInteger.Zero;
        while ((_192_i) < (new BigInteger((_189_typeParamsFiltered).Count))) {
          if ((_192_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _193_typeString;
          Dafny.ISequence<Dafny.Rune> _out58;
          _out58 = DCOMP.COMP.GenType((_189_typeParamsFiltered).Select(_192_i), false, false);
          _193_typeString = _out58;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _193_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<")), _193_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> + Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _192_i = (_192_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _182_params), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _186_retType);
      if ((m).dtor_hasBody) {
        Dafny.ISequence<Dafny.Rune> _194_earlyReturn;
        _194_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return;");
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source11 = (m).dtor_outVars;
        if (_source11.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _195___mcc_h0 = _source11.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _196_outVars = _195___mcc_h0;
          {
            _194_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return (");
            BigInteger _197_outI;
            _197_outI = BigInteger.Zero;
            while ((_197_outI) < (new BigInteger((_196_outVars).Count))) {
              if ((_197_outI).Sign == 1) {
                _194_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_194_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _198_outVar;
              _198_outVar = (_196_outVars).Select(_197_outI);
              _194_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_194_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_198_outVar));
              _197_outI = (_197_outI) + (BigInteger.One);
            }
            _194_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_194_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
          }
        } else {
        }
        Dafny.ISequence<Dafny.Rune> _199_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _200___v12;
        Dafny.ISequence<Dafny.Rune> _out59;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
        DCOMP.COMP.GenStmts((m).dtor_body, _183_paramNames, true, _194_earlyReturn, out _out59, out _out60);
        _199_body = _out59;
        _200___v12 = _out60;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source12 = (m).dtor_outVars;
        if (_source12.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _201___mcc_h1 = _source12.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _202_outVars = _201___mcc_h1;
          {
            _199_body = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_199_body, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _194_earlyReturn);
          }
        } else {
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _199_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      }
      return s;
    }
    public static void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, Dafny.ISequence<Dafny.Rune> earlyReturn, out Dafny.ISequence<Dafny.Rune> generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _203_i;
      _203_i = BigInteger.Zero;
      while ((_203_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _204_stmt;
        _204_stmt = (stmts).Select(_203_i);
        Dafny.ISequence<Dafny.Rune> _205_stmtString;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _206_recIdents;
        Dafny.ISequence<Dafny.Rune> _out61;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out62;
        DCOMP.COMP.GenStmt(_204_stmt, @params, (isLast) && ((_203_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out61, out _out62);
        _205_stmtString = _out61;
        _206_recIdents = _out62;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _206_recIdents);
        if ((_203_i).Sign == 1) {
          generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, _205_stmtString);
        _203_i = (_203_i) + (BigInteger.One);
      }
    }
    public static void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source13 = lhs;
      if (_source13.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _207___mcc_h0 = _source13.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source14 = _207___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _208___mcc_h1 = _source14;
        Dafny.ISequence<Dafny.Rune> _209_id = _208___mcc_h1;
        {
          if ((@params).Contains(_209_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*r#"), _209_id);
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _209_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_209_id);
          needsIIFE = false;
        }
      } else {
        DAST._IExpression _210___mcc_h2 = _source13.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _211___mcc_h3 = _source13.dtor_field;
        Dafny.ISequence<Dafny.Rune> _212_field = _211___mcc_h3;
        DAST._IExpression _213_on = _210___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _214_onExpr;
          bool _215_onOwned;
          bool _216_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _217_recIdents;
          Dafny.ISequence<Dafny.Rune> _out63;
          bool _out64;
          bool _out65;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
          DCOMP.COMP.GenExpr(_213_on, @params, false, out _out63, out _out64, out _out65, out _out66);
          _214_onExpr = _out63;
          _215_onOwned = _out64;
          _216_onErased = _out65;
          _217_recIdents = _out66;
          if (!(_216_onErased)) {
            Dafny.ISequence<Dafny.Rune> _218_eraseFn;
            _218_eraseFn = ((_215_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _214_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _218_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _214_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), _214_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _212_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut())"));
          readIdents = _217_recIdents;
          needsIIFE = true;
        }
      }
    }
    public static void GenStmt(DAST._IStatement stmt, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, Dafny.ISequence<Dafny.Rune> earlyReturn, out Dafny.ISequence<Dafny.Rune> generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IStatement _source15 = stmt;
      if (_source15.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _219___mcc_h0 = _source15.dtor_name;
        DAST._IType _220___mcc_h1 = _source15.dtor_typ;
        DAST._IOptional<DAST._IExpression> _221___mcc_h2 = _source15.dtor_maybeValue;
        DAST._IOptional<DAST._IExpression> _source16 = _221___mcc_h2;
        if (_source16.is_Some) {
          DAST._IExpression _222___mcc_h3 = _source16.dtor_Some_a0;
          DAST._IExpression _223_expression = _222___mcc_h3;
          DAST._IType _224_typ = _220___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _225_name = _219___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _226_expr;
            bool _227___v13;
            bool _228_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _229_recIdents;
            Dafny.ISequence<Dafny.Rune> _out67;
            bool _out68;
            bool _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            DCOMP.COMP.GenExpr(_223_expression, @params, true, out _out67, out _out68, out _out69, out _out70);
            _226_expr = _out67;
            _227___v13 = _out68;
            _228_recErased = _out69;
            _229_recIdents = _out70;
            if (_228_recErased) {
              _226_expr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _226_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            Dafny.ISequence<Dafny.Rune> _230_typeString;
            Dafny.ISequence<Dafny.Rune> _out71;
            _out71 = DCOMP.COMP.GenType(_224_typ, true, false);
            _230_typeString = _out71;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _225_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _230_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _226_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = _229_recIdents;
          }
        } else {
          DAST._IType _231_typ = _220___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _232_name = _219___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _233_typeString;
            Dafny.ISequence<Dafny.Rune> _out72;
            _out72 = DCOMP.COMP.GenType(_231_typ, true, false);
            _233_typeString = _out72;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _232_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _233_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source15.is_Assign) {
        DAST._IAssignLhs _234___mcc_h4 = _source15.dtor_lhs;
        DAST._IExpression _235___mcc_h5 = _source15.dtor_value;
        DAST._IExpression _236_expression = _235___mcc_h5;
        DAST._IAssignLhs _237_lhs = _234___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _238_lhsGen;
          bool _239_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _240_recIdents;
          Dafny.ISequence<Dafny.Rune> _out73;
          bool _out74;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out75;
          DCOMP.COMP.GenAssignLhs(_237_lhs, @params, out _out73, out _out74, out _out75);
          _238_lhsGen = _out73;
          _239_needsIIFE = _out74;
          _240_recIdents = _out75;
          Dafny.ISequence<Dafny.Rune> _241_exprGen;
          bool _242___v14;
          bool _243_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _244_exprIdents;
          Dafny.ISequence<Dafny.Rune> _out76;
          bool _out77;
          bool _out78;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out79;
          DCOMP.COMP.GenExpr(_236_expression, @params, true, out _out76, out _out77, out _out78, out _out79);
          _241_exprGen = _out76;
          _242___v14 = _out77;
          _243_exprErased = _out78;
          _244_exprIdents = _out79;
          if (_243_exprErased) {
            _241_exprGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _241_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (_239_needsIIFE) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ let __rhs = "), _241_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; ")), _238_lhsGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = __rhs; }"));
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_238_lhsGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _241_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_240_recIdents, _244_exprIdents);
        }
      } else if (_source15.is_If) {
        DAST._IExpression _245___mcc_h6 = _source15.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _246___mcc_h7 = _source15.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _247___mcc_h8 = _source15.dtor_els;
        Dafny.ISequence<DAST._IStatement> _248_els = _247___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _249_thn = _246___mcc_h7;
        DAST._IExpression _250_cond = _245___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _251_condString;
          bool _252___v15;
          bool _253_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _254_recIdents;
          Dafny.ISequence<Dafny.Rune> _out80;
          bool _out81;
          bool _out82;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out83;
          DCOMP.COMP.GenExpr(_250_cond, @params, true, out _out80, out _out81, out _out82, out _out83);
          _251_condString = _out80;
          _252___v15 = _out81;
          _253_condErased = _out82;
          _254_recIdents = _out83;
          if (!(_253_condErased)) {
            _251_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _251_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _254_recIdents;
          Dafny.ISequence<Dafny.Rune> _255_thnString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _256_thnIdents;
          Dafny.ISequence<Dafny.Rune> _out84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out85;
          DCOMP.COMP.GenStmts(_249_thn, @params, isLast, earlyReturn, out _out84, out _out85);
          _255_thnString = _out84;
          _256_thnIdents = _out85;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _256_thnIdents);
          Dafny.ISequence<Dafny.Rune> _257_elsString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _258_elsIdents;
          Dafny.ISequence<Dafny.Rune> _out86;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out87;
          DCOMP.COMP.GenStmts(_248_els, @params, isLast, earlyReturn, out _out86, out _out87);
          _257_elsString = _out86;
          _258_elsIdents = _out87;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _258_elsIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), _251_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _255_thnString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _257_elsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_While) {
        DAST._IExpression _259___mcc_h9 = _source15.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _260___mcc_h10 = _source15.dtor_body;
        Dafny.ISequence<DAST._IStatement> _261_body = _260___mcc_h10;
        DAST._IExpression _262_cond = _259___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _263_condString;
          bool _264___v16;
          bool _265_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _266_recIdents;
          Dafny.ISequence<Dafny.Rune> _out88;
          bool _out89;
          bool _out90;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
          DCOMP.COMP.GenExpr(_262_cond, @params, true, out _out88, out _out89, out _out90, out _out91);
          _263_condString = _out88;
          _264___v16 = _out89;
          _265_condErased = _out90;
          _266_recIdents = _out91;
          if (!(_265_condErased)) {
            _263_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase("), _263_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _266_recIdents;
          Dafny.ISequence<Dafny.Rune> _267_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _268_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out92;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out93;
          DCOMP.COMP.GenStmts(_261_body, @params, false, earlyReturn, out _out92, out _out93);
          _267_bodyString = _out92;
          _268_bodyIdents = _out93;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _268_bodyIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), _263_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _267_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_Call) {
        DAST._IExpression _269___mcc_h11 = _source15.dtor_on;
        Dafny.ISequence<Dafny.Rune> _270___mcc_h12 = _source15.dtor_name;
        Dafny.ISequence<DAST._IType> _271___mcc_h13 = _source15.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _272___mcc_h14 = _source15.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _273___mcc_h15 = _source15.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _274_maybeOutVars = _273___mcc_h15;
        Dafny.ISequence<DAST._IExpression> _275_args = _272___mcc_h14;
        Dafny.ISequence<DAST._IType> _276_typeArgs = _271___mcc_h13;
        Dafny.ISequence<Dafny.Rune> _277_name = _270___mcc_h12;
        DAST._IExpression _278_on = _269___mcc_h11;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _279_typeArgString;
          _279_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_276_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _280_typeI;
            _280_typeI = BigInteger.Zero;
            _279_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_280_typeI) < (new BigInteger((_276_typeArgs).Count))) {
              if ((_280_typeI).Sign == 1) {
                _279_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_279_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _281_typeString;
              Dafny.ISequence<Dafny.Rune> _out94;
              _out94 = DCOMP.COMP.GenType((_276_typeArgs).Select(_280_typeI), false, false);
              _281_typeString = _out94;
              _279_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_279_typeArgString, _281_typeString);
              _280_typeI = (_280_typeI) + (BigInteger.One);
            }
            _279_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_279_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _282_argString;
          _282_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _283_i;
          _283_i = BigInteger.Zero;
          while ((_283_i) < (new BigInteger((_275_args).Count))) {
            if ((_283_i).Sign == 1) {
              _282_argString = Dafny.Sequence<Dafny.Rune>.Concat(_282_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _284_argExpr;
            bool _285_isOwned;
            bool _286_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _287_argIdents;
            Dafny.ISequence<Dafny.Rune> _out95;
            bool _out96;
            bool _out97;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out98;
            DCOMP.COMP.GenExpr((_275_args).Select(_283_i), @params, false, out _out95, out _out96, out _out97, out _out98);
            _284_argExpr = _out95;
            _285_isOwned = _out96;
            _286_argErased = _out97;
            _287_argIdents = _out98;
            if (_285_isOwned) {
              _284_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _284_argExpr);
            }
            _282_argString = Dafny.Sequence<Dafny.Rune>.Concat(_282_argString, _284_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _287_argIdents);
            _283_i = (_283_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _288_enclosingString;
          bool _289___v17;
          bool _290___v18;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _291_enclosingIdents;
          Dafny.ISequence<Dafny.Rune> _out99;
          bool _out100;
          bool _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          DCOMP.COMP.GenExpr(_278_on, @params, false, out _out99, out _out100, out _out101, out _out102);
          _288_enclosingString = _out99;
          _289___v17 = _out100;
          _290___v18 = _out101;
          _291_enclosingIdents = _out102;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _291_enclosingIdents);
          DAST._IExpression _source17 = _278_on;
          if (_source17.is_Literal) {
            DAST._ILiteral _292___mcc_h18 = _source17.dtor_Literal_a0;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _293___mcc_h20 = _source17.dtor_Ident_a0;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _294___mcc_h22 = _source17.dtor_Companion_a0;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_288_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source17.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _295___mcc_h24 = _source17.dtor_Tuple_a0;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _296___mcc_h26 = _source17.dtor_path;
            Dafny.ISequence<DAST._IExpression> _297___mcc_h27 = _source17.dtor_args;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _298___mcc_h30 = _source17.dtor_dims;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _299___mcc_h32 = _source17.dtor_path;
            Dafny.ISequence<Dafny.Rune> _300___mcc_h33 = _source17.dtor_variant;
            bool _301___mcc_h34 = _source17.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _302___mcc_h35 = _source17.dtor_contents;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Convert) {
            DAST._IExpression _303___mcc_h40 = _source17.dtor_value;
            DAST._IType _304___mcc_h41 = _source17.dtor_from;
            DAST._IType _305___mcc_h42 = _source17.dtor_typ;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _306___mcc_h46 = _source17.dtor_elements;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _307___mcc_h48 = _source17.dtor_elements;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_This) {
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Ite) {
            DAST._IExpression _308___mcc_h50 = _source17.dtor_cond;
            DAST._IExpression _309___mcc_h51 = _source17.dtor_thn;
            DAST._IExpression _310___mcc_h52 = _source17.dtor_els;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_UnOp) {
            DAST._IUnaryOp _311___mcc_h56 = _source17.dtor_unOp;
            DAST._IExpression _312___mcc_h57 = _source17.dtor_expr;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _313___mcc_h60 = _source17.dtor_op;
            DAST._IExpression _314___mcc_h61 = _source17.dtor_left;
            DAST._IExpression _315___mcc_h62 = _source17.dtor_right;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Select) {
            DAST._IExpression _316___mcc_h66 = _source17.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _317___mcc_h67 = _source17.dtor_field;
            bool _318___mcc_h68 = _source17.dtor_isConstant;
            bool _319___mcc_h69 = _source17.dtor_onDatatype;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SelectFn) {
            DAST._IExpression _320___mcc_h74 = _source17.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _321___mcc_h75 = _source17.dtor_field;
            bool _322___mcc_h76 = _source17.dtor_onDatatype;
            bool _323___mcc_h77 = _source17.dtor_isStatic;
            BigInteger _324___mcc_h78 = _source17.dtor_arity;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_TupleSelect) {
            DAST._IExpression _325___mcc_h84 = _source17.dtor_expr;
            BigInteger _326___mcc_h85 = _source17.dtor_index;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Call) {
            DAST._IExpression _327___mcc_h88 = _source17.dtor_on;
            Dafny.ISequence<Dafny.Rune> _328___mcc_h89 = _source17.dtor_name;
            Dafny.ISequence<DAST._IType> _329___mcc_h90 = _source17.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _330___mcc_h91 = _source17.dtor_args;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _331___mcc_h96 = _source17.dtor_params;
            DAST._IType _332___mcc_h97 = _source17.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _333___mcc_h98 = _source17.dtor_body;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _334___mcc_h102 = _source17.dtor_name;
            DAST._IType _335___mcc_h103 = _source17.dtor_typ;
            DAST._IExpression _336___mcc_h104 = _source17.dtor_value;
            DAST._IExpression _337___mcc_h105 = _source17.dtor_iifeBody;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Apply) {
            DAST._IExpression _338___mcc_h110 = _source17.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _339___mcc_h111 = _source17.dtor_args;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_TypeTest) {
            DAST._IExpression _340___mcc_h114 = _source17.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _341___mcc_h115 = _source17.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _342___mcc_h116 = _source17.dtor_variant;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _343___mcc_h120 = _source17.dtor_typ;
            {
              _288_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _344_receiver;
          _344_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source18 = _274_maybeOutVars;
          if (_source18.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _345___mcc_h122 = _source18.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _346_outVars = _345___mcc_h122;
            {
              if ((new BigInteger((_346_outVars).Count)) > (BigInteger.One)) {
                _344_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _347_outI;
              _347_outI = BigInteger.Zero;
              while ((_347_outI) < (new BigInteger((_346_outVars).Count))) {
                if ((_347_outI).Sign == 1) {
                  _344_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_344_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _348_outVar;
                _348_outVar = (_346_outVars).Select(_347_outI);
                _344_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_344_receiver, (_348_outVar));
                _347_outI = (_347_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_346_outVars).Count)) > (BigInteger.One)) {
                _344_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_344_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_344_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_344_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _288_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _277_name), _279_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _282_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source15.is_Return) {
        DAST._IExpression _349___mcc_h16 = _source15.dtor_expr;
        DAST._IExpression _350_expr = _349___mcc_h16;
        {
          Dafny.ISequence<Dafny.Rune> _351_exprString;
          bool _352___v21;
          bool _353_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _354_recIdents;
          Dafny.ISequence<Dafny.Rune> _out103;
          bool _out104;
          bool _out105;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out106;
          DCOMP.COMP.GenExpr(_350_expr, @params, true, out _out103, out _out104, out _out105, out _out106);
          _351_exprString = _out103;
          _352___v21 = _out104;
          _353_recErased = _out105;
          _354_recIdents = _out106;
          _351_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _351_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _354_recIdents;
          if (isLast) {
            generated = _351_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _351_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source15.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source15.is_Halt) {
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else {
        DAST._IExpression _355___mcc_h17 = _source15.dtor_Print_a0;
        DAST._IExpression _356_e = _355___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _357_printedExpr;
          bool _358_isOwned;
          bool _359___v22;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _360_recIdents;
          Dafny.ISequence<Dafny.Rune> _out107;
          bool _out108;
          bool _out109;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
          DCOMP.COMP.GenExpr(_356_e, @params, false, out _out107, out _out108, out _out109, out _out110);
          _357_printedExpr = _out107;
          _358_isOwned = _out108;
          _359___v22 = _out109;
          _360_recIdents = _out110;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_358_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _357_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _360_recIdents;
        }
      }
    }
    public static void GenExpr(DAST._IExpression e, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool mustOwn, out Dafny.ISequence<Dafny.Rune> s, out bool isOwned, out bool isErased, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      isOwned = false;
      isErased = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source19 = e;
      if (_source19.is_Literal) {
        DAST._ILiteral _361___mcc_h0 = _source19.dtor_Literal_a0;
        DAST._ILiteral _source20 = _361___mcc_h0;
        if (_source20.is_BoolLiteral) {
          bool _362___mcc_h1 = _source20.dtor_BoolLiteral_a0;
          if ((_362___mcc_h1) == (false)) {
            {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false");
              isOwned = true;
              isErased = true;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          } else {
            {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true");
              isOwned = true;
              isErased = true;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
          }
        } else if (_source20.is_IntLiteral) {
          Dafny.ISequence<Dafny.Rune> _363___mcc_h2 = _source20.dtor_IntLiteral_a0;
          DAST._IType _364___mcc_h3 = _source20.dtor_IntLiteral_a1;
          DAST._IType _365_t = _364___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _366_i = _363___mcc_h2;
          {
            DAST._IType _source21 = _365_t;
            if (_source21.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _367___mcc_h60 = _source21.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _368___mcc_h61 = _source21.dtor_typeArgs;
              DAST._IResolvedType _369___mcc_h62 = _source21.dtor_resolved;
              {
                s = _366_i;
              }
            } else if (_source21.is_Tuple) {
              Dafny.ISequence<DAST._IType> _370___mcc_h66 = _source21.dtor_Tuple_a0;
              {
                s = _366_i;
              }
            } else if (_source21.is_Array) {
              DAST._IType _371___mcc_h68 = _source21.dtor_element;
              {
                s = _366_i;
              }
            } else if (_source21.is_Seq) {
              DAST._IType _372___mcc_h70 = _source21.dtor_element;
              {
                s = _366_i;
              }
            } else if (_source21.is_Set) {
              DAST._IType _373___mcc_h72 = _source21.dtor_element;
              {
                s = _366_i;
              }
            } else if (_source21.is_Multiset) {
              DAST._IType _374___mcc_h74 = _source21.dtor_element;
              {
                s = _366_i;
              }
            } else if (_source21.is_Map) {
              DAST._IType _375___mcc_h76 = _source21.dtor_key;
              DAST._IType _376___mcc_h77 = _source21.dtor_value;
              {
                s = _366_i;
              }
            } else if (_source21.is_Arrow) {
              Dafny.ISequence<DAST._IType> _377___mcc_h80 = _source21.dtor_args;
              DAST._IType _378___mcc_h81 = _source21.dtor_result;
              {
                s = _366_i;
              }
            } else if (_source21.is_Primitive) {
              DAST._IPrimitive _379___mcc_h84 = _source21.dtor_Primitive_a0;
              DAST._IPrimitive _source22 = _379___mcc_h84;
              if (_source22.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _366_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source22.is_Real) {
                {
                  s = _366_i;
                }
              } else if (_source22.is_String) {
                {
                  s = _366_i;
                }
              } else if (_source22.is_Bool) {
                {
                  s = _366_i;
                }
              } else {
                {
                  s = _366_i;
                }
              }
            } else if (_source21.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _380___mcc_h86 = _source21.dtor_Passthrough_a0;
              {
                s = _366_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _381___mcc_h88 = _source21.dtor_TypeArg_a0;
              {
                s = _366_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _382___mcc_h4 = _source20.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _383___mcc_h5 = _source20.dtor_DecLiteral_a1;
          DAST._IType _384___mcc_h6 = _source20.dtor_DecLiteral_a2;
          DAST._IType _385_t = _384___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _386_d = _383___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _387_n = _382___mcc_h4;
          {
            DAST._IType _source23 = _385_t;
            if (_source23.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _388___mcc_h90 = _source23.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _389___mcc_h91 = _source23.dtor_typeArgs;
              DAST._IResolvedType _390___mcc_h92 = _source23.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Tuple) {
              Dafny.ISequence<DAST._IType> _391___mcc_h96 = _source23.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Array) {
              DAST._IType _392___mcc_h98 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Seq) {
              DAST._IType _393___mcc_h100 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Set) {
              DAST._IType _394___mcc_h102 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Multiset) {
              DAST._IType _395___mcc_h104 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Map) {
              DAST._IType _396___mcc_h106 = _source23.dtor_key;
              DAST._IType _397___mcc_h107 = _source23.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Arrow) {
              Dafny.ISequence<DAST._IType> _398___mcc_h110 = _source23.dtor_args;
              DAST._IType _399___mcc_h111 = _source23.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Primitive) {
              DAST._IPrimitive _400___mcc_h114 = _source23.dtor_Primitive_a0;
              DAST._IPrimitive _source24 = _400___mcc_h114;
              if (_source24.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source24.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _387_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source24.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source24.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source23.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _401___mcc_h116 = _source23.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _402___mcc_h118 = _source23.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_387_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _386_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _403___mcc_h7 = _source20.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _404_l = _403___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _404_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_CharLiteral) {
          Dafny.Rune _405___mcc_h8 = _source20.dtor_CharLiteral_a0;
          Dafny.Rune _406_c = _405___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_406_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else {
          {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None");
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source19.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _407___mcc_h9 = _source19.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _408_name = _407___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _408_name);
          if (!((@params).Contains(_408_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_408_name);
        }
      } else if (_source19.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _409___mcc_h10 = _source19.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _410_path = _409___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out111;
          _out111 = DCOMP.COMP.GenPath(_410_path);
          s = _out111;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source19.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _411___mcc_h11 = _source19.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _412_values = _411___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _413_i;
          _413_i = BigInteger.Zero;
          bool _414_allErased;
          _414_allErased = true;
          while ((_413_i) < (new BigInteger((_412_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _415___v25;
            bool _416___v26;
            bool _417_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _418___v27;
            Dafny.ISequence<Dafny.Rune> _out112;
            bool _out113;
            bool _out114;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
            DCOMP.COMP.GenExpr((_412_values).Select(_413_i), @params, true, out _out112, out _out113, out _out114, out _out115);
            _415___v25 = _out112;
            _416___v26 = _out113;
            _417_isErased = _out114;
            _418___v27 = _out115;
            _414_allErased = (_414_allErased) && (_417_isErased);
            _413_i = (_413_i) + (BigInteger.One);
          }
          _413_i = BigInteger.Zero;
          while ((_413_i) < (new BigInteger((_412_values).Count))) {
            if ((_413_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _419_recursiveGen;
            bool _420___v28;
            bool _421_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _422_recIdents;
            Dafny.ISequence<Dafny.Rune> _out116;
            bool _out117;
            bool _out118;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
            DCOMP.COMP.GenExpr((_412_values).Select(_413_i), @params, true, out _out116, out _out117, out _out118, out _out119);
            _419_recursiveGen = _out116;
            _420___v28 = _out117;
            _421_isErased = _out118;
            _422_recIdents = _out119;
            if ((_421_isErased) && (!(_414_allErased))) {
              _419_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _419_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _419_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _422_recIdents);
            _413_i = (_413_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _414_allErased;
        }
      } else if (_source19.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _423___mcc_h12 = _source19.dtor_path;
        Dafny.ISequence<DAST._IExpression> _424___mcc_h13 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _425_args = _424___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _426_path = _423___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _427_path;
          Dafny.ISequence<Dafny.Rune> _out120;
          _out120 = DCOMP.COMP.GenPath(_426_path);
          _427_path = _out120;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _427_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _428_i;
          _428_i = BigInteger.Zero;
          while ((_428_i) < (new BigInteger((_425_args).Count))) {
            if ((_428_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _429_recursiveGen;
            bool _430___v29;
            bool _431_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _432_recIdents;
            Dafny.ISequence<Dafny.Rune> _out121;
            bool _out122;
            bool _out123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
            DCOMP.COMP.GenExpr((_425_args).Select(_428_i), @params, true, out _out121, out _out122, out _out123, out _out124);
            _429_recursiveGen = _out121;
            _430___v29 = _out122;
            _431_isErased = _out123;
            _432_recIdents = _out124;
            if (_431_isErased) {
              _429_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _429_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _429_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _432_recIdents);
            _428_i = (_428_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _433___mcc_h14 = _source19.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _434_dims = _433___mcc_h14;
        {
          BigInteger _435_i;
          _435_i = (new BigInteger((_434_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_435_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _436_recursiveGen;
            bool _437___v30;
            bool _438_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _439_recIdents;
            Dafny.ISequence<Dafny.Rune> _out125;
            bool _out126;
            bool _out127;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
            DCOMP.COMP.GenExpr((_434_dims).Select(_435_i), @params, true, out _out125, out _out126, out _out127, out _out128);
            _436_recursiveGen = _out125;
            _437___v30 = _out126;
            _438_isErased = _out127;
            _439_recIdents = _out128;
            if (!(_438_isErased)) {
              _436_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _436_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _436_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _439_recIdents);
            _435_i = (_435_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _440___mcc_h15 = _source19.dtor_path;
        Dafny.ISequence<Dafny.Rune> _441___mcc_h16 = _source19.dtor_variant;
        bool _442___mcc_h17 = _source19.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _443___mcc_h18 = _source19.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _444_values = _443___mcc_h18;
        bool _445_isCo = _442___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _446_variant = _441___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _447_path = _440___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _448_path;
          Dafny.ISequence<Dafny.Rune> _out129;
          _out129 = DCOMP.COMP.GenPath(_447_path);
          _448_path = _out129;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _448_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _446_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _449_i;
          _449_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_449_i) < (new BigInteger((_444_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_444_values).Select(_449_i);
            Dafny.ISequence<Dafny.Rune> _450_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _451_value = _let_tmp_rhs0.dtor__1;
            if ((_449_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_445_isCo) {
              Dafny.ISequence<Dafny.Rune> _452_recursiveGen;
              bool _453___v31;
              bool _454_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _455_recIdents;
              Dafny.ISequence<Dafny.Rune> _out130;
              bool _out131;
              bool _out132;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out133;
              DCOMP.COMP.GenExpr(_451_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out130, out _out131, out _out132, out _out133);
              _452_recursiveGen = _out130;
              _453___v31 = _out131;
              _454_isErased = _out132;
              _455_recIdents = _out133;
              if (!(_454_isErased)) {
                _452_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _452_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _452_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _452_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _455_recIdents);
              Dafny.ISequence<Dafny.Rune> _456_allReadCloned;
              _456_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_455_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _457_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_455_recIdents).Elements) {
                  _457_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_455_recIdents).Contains(_457_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1091)");
              after__ASSIGN_SUCH_THAT_0:;
                _456_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_456_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _457_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _457_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _455_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_455_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_457_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _450_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _456_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _452_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _458_recursiveGen;
              bool _459___v32;
              bool _460_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _461_recIdents;
              Dafny.ISequence<Dafny.Rune> _out134;
              bool _out135;
              bool _out136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
              DCOMP.COMP.GenExpr(_451_value, @params, true, out _out134, out _out135, out _out136, out _out137);
              _458_recursiveGen = _out134;
              _459___v32 = _out135;
              _460_isErased = _out136;
              _461_recIdents = _out137;
              if (!(_460_isErased)) {
                _458_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _458_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _458_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _458_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _450_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _458_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _461_recIdents);
            }
            _449_i = (_449_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_Convert) {
        DAST._IExpression _462___mcc_h19 = _source19.dtor_value;
        DAST._IType _463___mcc_h20 = _source19.dtor_from;
        DAST._IType _464___mcc_h21 = _source19.dtor_typ;
        DAST._IType _465_toTpe = _464___mcc_h21;
        DAST._IType _466_fromTpe = _463___mcc_h20;
        DAST._IExpression _467_expr = _462___mcc_h19;
        {
          if (object.Equals(_466_fromTpe, _465_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _468_recursiveGen;
            bool _469_recOwned;
            bool _470_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _471_recIdents;
            Dafny.ISequence<Dafny.Rune> _out138;
            bool _out139;
            bool _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out138, out _out139, out _out140, out _out141);
            _468_recursiveGen = _out138;
            _469_recOwned = _out139;
            _470_recErased = _out140;
            _471_recIdents = _out141;
            s = _468_recursiveGen;
            isOwned = _469_recOwned;
            isErased = _470_recErased;
            readIdents = _471_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source25 = _System.Tuple2<DAST._IType, DAST._IType>.create(_466_fromTpe, _465_toTpe);
            DAST._IType _472___mcc_h120 = _source25.dtor__0;
            DAST._IType _473___mcc_h121 = _source25.dtor__1;
            DAST._IType _source26 = _472___mcc_h120;
            if (_source26.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _474___mcc_h124 = _source26.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _475___mcc_h125 = _source26.dtor_typeArgs;
              DAST._IResolvedType _476___mcc_h126 = _source26.dtor_resolved;
              DAST._IResolvedType _source27 = _476___mcc_h126;
              if (_source27.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _477___mcc_h133 = _source27.dtor_path;
                DAST._IType _source28 = _473___mcc_h121;
                if (_source28.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _478___mcc_h136 = _source28.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _479___mcc_h137 = _source28.dtor_typeArgs;
                  DAST._IResolvedType _480___mcc_h138 = _source28.dtor_resolved;
                  DAST._IResolvedType _source29 = _480___mcc_h138;
                  if (_source29.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _481___mcc_h142 = _source29.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _482_recursiveGen;
                      bool _483_recOwned;
                      bool _484_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _485_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out142;
                      bool _out143;
                      bool _out144;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out145;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out142, out _out143, out _out144, out _out145);
                      _482_recursiveGen = _out142;
                      _483_recOwned = _out143;
                      _484_recErased = _out144;
                      _485_recIdents = _out145;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _482_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _483_recOwned;
                      isErased = _484_recErased;
                      readIdents = _485_recIdents;
                    }
                  } else if (_source29.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _486___mcc_h144 = _source29.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _487_recursiveGen;
                      bool _488_recOwned;
                      bool _489_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _490_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out146;
                      bool _out147;
                      bool _out148;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out146, out _out147, out _out148, out _out149);
                      _487_recursiveGen = _out146;
                      _488_recOwned = _out147;
                      _489_recErased = _out148;
                      _490_recIdents = _out149;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _487_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _488_recOwned;
                      isErased = _489_recErased;
                      readIdents = _490_recIdents;
                    }
                  } else {
                    DAST._IType _491___mcc_h146 = _source29.dtor_Newtype_a0;
                    DAST._IType _492_b = _491___mcc_h146;
                    {
                      if (object.Equals(_466_fromTpe, _492_b)) {
                        Dafny.ISequence<Dafny.Rune> _493_recursiveGen;
                        bool _494_recOwned;
                        bool _495_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _496_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out150;
                        bool _out151;
                        bool _out152;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out150, out _out151, out _out152, out _out153);
                        _493_recursiveGen = _out150;
                        _494_recOwned = _out151;
                        _495_recErased = _out152;
                        _496_recIdents = _out153;
                        Dafny.ISequence<Dafny.Rune> _497_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out154;
                        _out154 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _497_rhsType = _out154;
                        Dafny.ISequence<Dafny.Rune> _498_uneraseFn;
                        _498_uneraseFn = ((_494_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _497_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _498_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _493_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _494_recOwned;
                        isErased = false;
                        readIdents = _496_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out155;
                        bool _out156;
                        bool _out157;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out158;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _492_b), _492_b, _465_toTpe), @params, mustOwn, out _out155, out _out156, out _out157, out _out158);
                        s = _out155;
                        isOwned = _out156;
                        isErased = _out157;
                        readIdents = _out158;
                      }
                    }
                  }
                } else if (_source28.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _499___mcc_h148 = _source28.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _500_recursiveGen;
                    bool _501_recOwned;
                    bool _502_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _503_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out159;
                    bool _out160;
                    bool _out161;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out159, out _out160, out _out161, out _out162);
                    _500_recursiveGen = _out159;
                    _501_recOwned = _out160;
                    _502_recErased = _out161;
                    _503_recIdents = _out162;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _500_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _501_recOwned;
                    isErased = _502_recErased;
                    readIdents = _503_recIdents;
                  }
                } else if (_source28.is_Array) {
                  DAST._IType _504___mcc_h150 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _505_recursiveGen;
                    bool _506_recOwned;
                    bool _507_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _508_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out163;
                    bool _out164;
                    bool _out165;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out163, out _out164, out _out165, out _out166);
                    _505_recursiveGen = _out163;
                    _506_recOwned = _out164;
                    _507_recErased = _out165;
                    _508_recIdents = _out166;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _505_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _506_recOwned;
                    isErased = _507_recErased;
                    readIdents = _508_recIdents;
                  }
                } else if (_source28.is_Seq) {
                  DAST._IType _509___mcc_h152 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _510_recursiveGen;
                    bool _511_recOwned;
                    bool _512_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _513_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out167;
                    bool _out168;
                    bool _out169;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out170;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out167, out _out168, out _out169, out _out170);
                    _510_recursiveGen = _out167;
                    _511_recOwned = _out168;
                    _512_recErased = _out169;
                    _513_recIdents = _out170;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _510_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _511_recOwned;
                    isErased = _512_recErased;
                    readIdents = _513_recIdents;
                  }
                } else if (_source28.is_Set) {
                  DAST._IType _514___mcc_h154 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _515_recursiveGen;
                    bool _516_recOwned;
                    bool _517_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _518_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out171;
                    bool _out172;
                    bool _out173;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out171, out _out172, out _out173, out _out174);
                    _515_recursiveGen = _out171;
                    _516_recOwned = _out172;
                    _517_recErased = _out173;
                    _518_recIdents = _out174;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _515_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _516_recOwned;
                    isErased = _517_recErased;
                    readIdents = _518_recIdents;
                  }
                } else if (_source28.is_Multiset) {
                  DAST._IType _519___mcc_h156 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _520_recursiveGen;
                    bool _521_recOwned;
                    bool _522_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _523_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out175;
                    bool _out176;
                    bool _out177;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out175, out _out176, out _out177, out _out178);
                    _520_recursiveGen = _out175;
                    _521_recOwned = _out176;
                    _522_recErased = _out177;
                    _523_recIdents = _out178;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _520_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _521_recOwned;
                    isErased = _522_recErased;
                    readIdents = _523_recIdents;
                  }
                } else if (_source28.is_Map) {
                  DAST._IType _524___mcc_h158 = _source28.dtor_key;
                  DAST._IType _525___mcc_h159 = _source28.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _526_recursiveGen;
                    bool _527_recOwned;
                    bool _528_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _529_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out179;
                    bool _out180;
                    bool _out181;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out182;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out179, out _out180, out _out181, out _out182);
                    _526_recursiveGen = _out179;
                    _527_recOwned = _out180;
                    _528_recErased = _out181;
                    _529_recIdents = _out182;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _526_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _527_recOwned;
                    isErased = _528_recErased;
                    readIdents = _529_recIdents;
                  }
                } else if (_source28.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _530___mcc_h162 = _source28.dtor_args;
                  DAST._IType _531___mcc_h163 = _source28.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _532_recursiveGen;
                    bool _533_recOwned;
                    bool _534_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _535_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out183;
                    bool _out184;
                    bool _out185;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out186;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out183, out _out184, out _out185, out _out186);
                    _532_recursiveGen = _out183;
                    _533_recOwned = _out184;
                    _534_recErased = _out185;
                    _535_recIdents = _out186;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _532_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _533_recOwned;
                    isErased = _534_recErased;
                    readIdents = _535_recIdents;
                  }
                } else if (_source28.is_Primitive) {
                  DAST._IPrimitive _536___mcc_h166 = _source28.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _537_recursiveGen;
                    bool _538_recOwned;
                    bool _539_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _540_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out187;
                    bool _out188;
                    bool _out189;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out187, out _out188, out _out189, out _out190);
                    _537_recursiveGen = _out187;
                    _538_recOwned = _out188;
                    _539_recErased = _out189;
                    _540_recIdents = _out190;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _537_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _538_recOwned;
                    isErased = _539_recErased;
                    readIdents = _540_recIdents;
                  }
                } else if (_source28.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _541___mcc_h168 = _source28.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _542_recursiveGen;
                    bool _543_recOwned;
                    bool _544_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _545_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out191;
                    bool _out192;
                    bool _out193;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out191, out _out192, out _out193, out _out194);
                    _542_recursiveGen = _out191;
                    _543_recOwned = _out192;
                    _544_recErased = _out193;
                    _545_recIdents = _out194;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _542_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _543_recOwned;
                    isErased = _544_recErased;
                    readIdents = _545_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _546___mcc_h170 = _source28.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _547_recursiveGen;
                    bool _548_recOwned;
                    bool _549_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _550_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out195;
                    bool _out196;
                    bool _out197;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out195, out _out196, out _out197, out _out198);
                    _547_recursiveGen = _out195;
                    _548_recOwned = _out196;
                    _549_recErased = _out197;
                    _550_recIdents = _out198;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _547_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _548_recOwned;
                    isErased = _549_recErased;
                    readIdents = _550_recIdents;
                  }
                }
              } else if (_source27.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _551___mcc_h172 = _source27.dtor_path;
                DAST._IType _source30 = _473___mcc_h121;
                if (_source30.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _552___mcc_h175 = _source30.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _553___mcc_h176 = _source30.dtor_typeArgs;
                  DAST._IResolvedType _554___mcc_h177 = _source30.dtor_resolved;
                  DAST._IResolvedType _source31 = _554___mcc_h177;
                  if (_source31.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _555___mcc_h181 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _556_recursiveGen;
                      bool _557_recOwned;
                      bool _558_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _559_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out199;
                      bool _out200;
                      bool _out201;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out202;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out199, out _out200, out _out201, out _out202);
                      _556_recursiveGen = _out199;
                      _557_recOwned = _out200;
                      _558_recErased = _out201;
                      _559_recIdents = _out202;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _556_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _557_recOwned;
                      isErased = _558_recErased;
                      readIdents = _559_recIdents;
                    }
                  } else if (_source31.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _560___mcc_h183 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _561_recursiveGen;
                      bool _562_recOwned;
                      bool _563_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _564_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out203;
                      bool _out204;
                      bool _out205;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out206;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out203, out _out204, out _out205, out _out206);
                      _561_recursiveGen = _out203;
                      _562_recOwned = _out204;
                      _563_recErased = _out205;
                      _564_recIdents = _out206;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _561_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _562_recOwned;
                      isErased = _563_recErased;
                      readIdents = _564_recIdents;
                    }
                  } else {
                    DAST._IType _565___mcc_h185 = _source31.dtor_Newtype_a0;
                    DAST._IType _566_b = _565___mcc_h185;
                    {
                      if (object.Equals(_466_fromTpe, _566_b)) {
                        Dafny.ISequence<Dafny.Rune> _567_recursiveGen;
                        bool _568_recOwned;
                        bool _569_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _570_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out207;
                        bool _out208;
                        bool _out209;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out210;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out207, out _out208, out _out209, out _out210);
                        _567_recursiveGen = _out207;
                        _568_recOwned = _out208;
                        _569_recErased = _out209;
                        _570_recIdents = _out210;
                        Dafny.ISequence<Dafny.Rune> _571_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out211;
                        _out211 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _571_rhsType = _out211;
                        Dafny.ISequence<Dafny.Rune> _572_uneraseFn;
                        _572_uneraseFn = ((_568_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _571_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _572_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _567_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _568_recOwned;
                        isErased = false;
                        readIdents = _570_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out212;
                        bool _out213;
                        bool _out214;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out215;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _566_b), _566_b, _465_toTpe), @params, mustOwn, out _out212, out _out213, out _out214, out _out215);
                        s = _out212;
                        isOwned = _out213;
                        isErased = _out214;
                        readIdents = _out215;
                      }
                    }
                  }
                } else if (_source30.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _573___mcc_h187 = _source30.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _574_recursiveGen;
                    bool _575_recOwned;
                    bool _576_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _577_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out216;
                    bool _out217;
                    bool _out218;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out219;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out216, out _out217, out _out218, out _out219);
                    _574_recursiveGen = _out216;
                    _575_recOwned = _out217;
                    _576_recErased = _out218;
                    _577_recIdents = _out219;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _575_recOwned;
                    isErased = _576_recErased;
                    readIdents = _577_recIdents;
                  }
                } else if (_source30.is_Array) {
                  DAST._IType _578___mcc_h189 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _579_recursiveGen;
                    bool _580_recOwned;
                    bool _581_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _582_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out220;
                    bool _out221;
                    bool _out222;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out223;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out220, out _out221, out _out222, out _out223);
                    _579_recursiveGen = _out220;
                    _580_recOwned = _out221;
                    _581_recErased = _out222;
                    _582_recIdents = _out223;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _579_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _580_recOwned;
                    isErased = _581_recErased;
                    readIdents = _582_recIdents;
                  }
                } else if (_source30.is_Seq) {
                  DAST._IType _583___mcc_h191 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _584_recursiveGen;
                    bool _585_recOwned;
                    bool _586_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _587_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out224;
                    bool _out225;
                    bool _out226;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out224, out _out225, out _out226, out _out227);
                    _584_recursiveGen = _out224;
                    _585_recOwned = _out225;
                    _586_recErased = _out226;
                    _587_recIdents = _out227;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _584_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _585_recOwned;
                    isErased = _586_recErased;
                    readIdents = _587_recIdents;
                  }
                } else if (_source30.is_Set) {
                  DAST._IType _588___mcc_h193 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _589_recursiveGen;
                    bool _590_recOwned;
                    bool _591_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _592_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out228;
                    bool _out229;
                    bool _out230;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out228, out _out229, out _out230, out _out231);
                    _589_recursiveGen = _out228;
                    _590_recOwned = _out229;
                    _591_recErased = _out230;
                    _592_recIdents = _out231;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _589_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _590_recOwned;
                    isErased = _591_recErased;
                    readIdents = _592_recIdents;
                  }
                } else if (_source30.is_Multiset) {
                  DAST._IType _593___mcc_h195 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _594_recursiveGen;
                    bool _595_recOwned;
                    bool _596_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _597_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out232;
                    bool _out233;
                    bool _out234;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out235;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out232, out _out233, out _out234, out _out235);
                    _594_recursiveGen = _out232;
                    _595_recOwned = _out233;
                    _596_recErased = _out234;
                    _597_recIdents = _out235;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _594_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _595_recOwned;
                    isErased = _596_recErased;
                    readIdents = _597_recIdents;
                  }
                } else if (_source30.is_Map) {
                  DAST._IType _598___mcc_h197 = _source30.dtor_key;
                  DAST._IType _599___mcc_h198 = _source30.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _600_recursiveGen;
                    bool _601_recOwned;
                    bool _602_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _603_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out236;
                    bool _out237;
                    bool _out238;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out239;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out236, out _out237, out _out238, out _out239);
                    _600_recursiveGen = _out236;
                    _601_recOwned = _out237;
                    _602_recErased = _out238;
                    _603_recIdents = _out239;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _600_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _601_recOwned;
                    isErased = _602_recErased;
                    readIdents = _603_recIdents;
                  }
                } else if (_source30.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _604___mcc_h201 = _source30.dtor_args;
                  DAST._IType _605___mcc_h202 = _source30.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _606_recursiveGen;
                    bool _607_recOwned;
                    bool _608_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _609_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out240;
                    bool _out241;
                    bool _out242;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out243;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out240, out _out241, out _out242, out _out243);
                    _606_recursiveGen = _out240;
                    _607_recOwned = _out241;
                    _608_recErased = _out242;
                    _609_recIdents = _out243;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _606_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _607_recOwned;
                    isErased = _608_recErased;
                    readIdents = _609_recIdents;
                  }
                } else if (_source30.is_Primitive) {
                  DAST._IPrimitive _610___mcc_h205 = _source30.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _611_recursiveGen;
                    bool _612_recOwned;
                    bool _613_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _614_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out244;
                    bool _out245;
                    bool _out246;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out247;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out244, out _out245, out _out246, out _out247);
                    _611_recursiveGen = _out244;
                    _612_recOwned = _out245;
                    _613_recErased = _out246;
                    _614_recIdents = _out247;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _611_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _612_recOwned;
                    isErased = _613_recErased;
                    readIdents = _614_recIdents;
                  }
                } else if (_source30.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _615___mcc_h207 = _source30.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _616_recursiveGen;
                    bool _617_recOwned;
                    bool _618_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _619_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out248;
                    bool _out249;
                    bool _out250;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out251;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out248, out _out249, out _out250, out _out251);
                    _616_recursiveGen = _out248;
                    _617_recOwned = _out249;
                    _618_recErased = _out250;
                    _619_recIdents = _out251;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _616_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _617_recOwned;
                    isErased = _618_recErased;
                    readIdents = _619_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _620___mcc_h209 = _source30.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _621_recursiveGen;
                    bool _622_recOwned;
                    bool _623_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _624_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out252;
                    bool _out253;
                    bool _out254;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out255;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out252, out _out253, out _out254, out _out255);
                    _621_recursiveGen = _out252;
                    _622_recOwned = _out253;
                    _623_recErased = _out254;
                    _624_recIdents = _out255;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _621_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _622_recOwned;
                    isErased = _623_recErased;
                    readIdents = _624_recIdents;
                  }
                }
              } else {
                DAST._IType _625___mcc_h211 = _source27.dtor_Newtype_a0;
                DAST._IType _source32 = _473___mcc_h121;
                if (_source32.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _626___mcc_h214 = _source32.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _627___mcc_h215 = _source32.dtor_typeArgs;
                  DAST._IResolvedType _628___mcc_h216 = _source32.dtor_resolved;
                  DAST._IResolvedType _source33 = _628___mcc_h216;
                  if (_source33.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _629___mcc_h223 = _source33.dtor_path;
                    DAST._IType _630_b = _625___mcc_h211;
                    {
                      if (object.Equals(_630_b, _465_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _631_recursiveGen;
                        bool _632_recOwned;
                        bool _633_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _634_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out256;
                        bool _out257;
                        bool _out258;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out259;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out256, out _out257, out _out258, out _out259);
                        _631_recursiveGen = _out256;
                        _632_recOwned = _out257;
                        _633_recErased = _out258;
                        _634_recIdents = _out259;
                        Dafny.ISequence<Dafny.Rune> _635_uneraseFn;
                        _635_uneraseFn = ((_632_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _635_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _631_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _632_recOwned;
                        isErased = true;
                        readIdents = _634_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out260;
                        bool _out261;
                        bool _out262;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out263;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _630_b), _630_b, _465_toTpe), @params, mustOwn, out _out260, out _out261, out _out262, out _out263);
                        s = _out260;
                        isOwned = _out261;
                        isErased = _out262;
                        readIdents = _out263;
                      }
                    }
                  } else if (_source33.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _636___mcc_h226 = _source33.dtor_path;
                    DAST._IType _637_b = _625___mcc_h211;
                    {
                      if (object.Equals(_637_b, _465_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _638_recursiveGen;
                        bool _639_recOwned;
                        bool _640_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _641_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out264;
                        bool _out265;
                        bool _out266;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out264, out _out265, out _out266, out _out267);
                        _638_recursiveGen = _out264;
                        _639_recOwned = _out265;
                        _640_recErased = _out266;
                        _641_recIdents = _out267;
                        Dafny.ISequence<Dafny.Rune> _642_uneraseFn;
                        _642_uneraseFn = ((_639_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _642_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _638_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _639_recOwned;
                        isErased = true;
                        readIdents = _641_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out268;
                        bool _out269;
                        bool _out270;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _637_b), _637_b, _465_toTpe), @params, mustOwn, out _out268, out _out269, out _out270, out _out271);
                        s = _out268;
                        isOwned = _out269;
                        isErased = _out270;
                        readIdents = _out271;
                      }
                    }
                  } else {
                    DAST._IType _643___mcc_h229 = _source33.dtor_Newtype_a0;
                    DAST._IType _644_b = _643___mcc_h229;
                    {
                      if (object.Equals(_466_fromTpe, _644_b)) {
                        Dafny.ISequence<Dafny.Rune> _645_recursiveGen;
                        bool _646_recOwned;
                        bool _647_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _648_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out272;
                        bool _out273;
                        bool _out274;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out272, out _out273, out _out274, out _out275);
                        _645_recursiveGen = _out272;
                        _646_recOwned = _out273;
                        _647_recErased = _out274;
                        _648_recIdents = _out275;
                        Dafny.ISequence<Dafny.Rune> _649_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out276;
                        _out276 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _649_rhsType = _out276;
                        Dafny.ISequence<Dafny.Rune> _650_uneraseFn;
                        _650_uneraseFn = ((_646_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _649_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _650_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _645_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _646_recOwned;
                        isErased = false;
                        readIdents = _648_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out277;
                        bool _out278;
                        bool _out279;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _644_b), _644_b, _465_toTpe), @params, mustOwn, out _out277, out _out278, out _out279, out _out280);
                        s = _out277;
                        isOwned = _out278;
                        isErased = _out279;
                        readIdents = _out280;
                      }
                    }
                  }
                } else if (_source32.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _651___mcc_h232 = _source32.dtor_Tuple_a0;
                  DAST._IType _652_b = _625___mcc_h211;
                  {
                    if (object.Equals(_652_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _653_recursiveGen;
                      bool _654_recOwned;
                      bool _655_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _656_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out281;
                      bool _out282;
                      bool _out283;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out284;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out281, out _out282, out _out283, out _out284);
                      _653_recursiveGen = _out281;
                      _654_recOwned = _out282;
                      _655_recErased = _out283;
                      _656_recIdents = _out284;
                      Dafny.ISequence<Dafny.Rune> _657_uneraseFn;
                      _657_uneraseFn = ((_654_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _657_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _653_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _654_recOwned;
                      isErased = true;
                      readIdents = _656_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out285;
                      bool _out286;
                      bool _out287;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _652_b), _652_b, _465_toTpe), @params, mustOwn, out _out285, out _out286, out _out287, out _out288);
                      s = _out285;
                      isOwned = _out286;
                      isErased = _out287;
                      readIdents = _out288;
                    }
                  }
                } else if (_source32.is_Array) {
                  DAST._IType _658___mcc_h235 = _source32.dtor_element;
                  DAST._IType _659_b = _625___mcc_h211;
                  {
                    if (object.Equals(_659_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _660_recursiveGen;
                      bool _661_recOwned;
                      bool _662_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _663_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out289;
                      bool _out290;
                      bool _out291;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out292;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out289, out _out290, out _out291, out _out292);
                      _660_recursiveGen = _out289;
                      _661_recOwned = _out290;
                      _662_recErased = _out291;
                      _663_recIdents = _out292;
                      Dafny.ISequence<Dafny.Rune> _664_uneraseFn;
                      _664_uneraseFn = ((_661_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _664_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _660_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _661_recOwned;
                      isErased = true;
                      readIdents = _663_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out293;
                      bool _out294;
                      bool _out295;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out296;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _659_b), _659_b, _465_toTpe), @params, mustOwn, out _out293, out _out294, out _out295, out _out296);
                      s = _out293;
                      isOwned = _out294;
                      isErased = _out295;
                      readIdents = _out296;
                    }
                  }
                } else if (_source32.is_Seq) {
                  DAST._IType _665___mcc_h238 = _source32.dtor_element;
                  DAST._IType _666_b = _625___mcc_h211;
                  {
                    if (object.Equals(_666_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _667_recursiveGen;
                      bool _668_recOwned;
                      bool _669_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _670_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out297;
                      bool _out298;
                      bool _out299;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out300;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out297, out _out298, out _out299, out _out300);
                      _667_recursiveGen = _out297;
                      _668_recOwned = _out298;
                      _669_recErased = _out299;
                      _670_recIdents = _out300;
                      Dafny.ISequence<Dafny.Rune> _671_uneraseFn;
                      _671_uneraseFn = ((_668_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _671_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _667_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _668_recOwned;
                      isErased = true;
                      readIdents = _670_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out301;
                      bool _out302;
                      bool _out303;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out304;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _666_b), _666_b, _465_toTpe), @params, mustOwn, out _out301, out _out302, out _out303, out _out304);
                      s = _out301;
                      isOwned = _out302;
                      isErased = _out303;
                      readIdents = _out304;
                    }
                  }
                } else if (_source32.is_Set) {
                  DAST._IType _672___mcc_h241 = _source32.dtor_element;
                  DAST._IType _673_b = _625___mcc_h211;
                  {
                    if (object.Equals(_673_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _674_recursiveGen;
                      bool _675_recOwned;
                      bool _676_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _677_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out305;
                      bool _out306;
                      bool _out307;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out305, out _out306, out _out307, out _out308);
                      _674_recursiveGen = _out305;
                      _675_recOwned = _out306;
                      _676_recErased = _out307;
                      _677_recIdents = _out308;
                      Dafny.ISequence<Dafny.Rune> _678_uneraseFn;
                      _678_uneraseFn = ((_675_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _678_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _674_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _675_recOwned;
                      isErased = true;
                      readIdents = _677_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out309;
                      bool _out310;
                      bool _out311;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _673_b), _673_b, _465_toTpe), @params, mustOwn, out _out309, out _out310, out _out311, out _out312);
                      s = _out309;
                      isOwned = _out310;
                      isErased = _out311;
                      readIdents = _out312;
                    }
                  }
                } else if (_source32.is_Multiset) {
                  DAST._IType _679___mcc_h244 = _source32.dtor_element;
                  DAST._IType _680_b = _625___mcc_h211;
                  {
                    if (object.Equals(_680_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _681_recursiveGen;
                      bool _682_recOwned;
                      bool _683_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _684_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out313;
                      bool _out314;
                      bool _out315;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out316;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out313, out _out314, out _out315, out _out316);
                      _681_recursiveGen = _out313;
                      _682_recOwned = _out314;
                      _683_recErased = _out315;
                      _684_recIdents = _out316;
                      Dafny.ISequence<Dafny.Rune> _685_uneraseFn;
                      _685_uneraseFn = ((_682_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _685_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _681_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _682_recOwned;
                      isErased = true;
                      readIdents = _684_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out317;
                      bool _out318;
                      bool _out319;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _680_b), _680_b, _465_toTpe), @params, mustOwn, out _out317, out _out318, out _out319, out _out320);
                      s = _out317;
                      isOwned = _out318;
                      isErased = _out319;
                      readIdents = _out320;
                    }
                  }
                } else if (_source32.is_Map) {
                  DAST._IType _686___mcc_h247 = _source32.dtor_key;
                  DAST._IType _687___mcc_h248 = _source32.dtor_value;
                  DAST._IType _688_b = _625___mcc_h211;
                  {
                    if (object.Equals(_688_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _689_recursiveGen;
                      bool _690_recOwned;
                      bool _691_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _692_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out321;
                      bool _out322;
                      bool _out323;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out321, out _out322, out _out323, out _out324);
                      _689_recursiveGen = _out321;
                      _690_recOwned = _out322;
                      _691_recErased = _out323;
                      _692_recIdents = _out324;
                      Dafny.ISequence<Dafny.Rune> _693_uneraseFn;
                      _693_uneraseFn = ((_690_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _693_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _689_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _690_recOwned;
                      isErased = true;
                      readIdents = _692_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out325;
                      bool _out326;
                      bool _out327;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out328;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _688_b), _688_b, _465_toTpe), @params, mustOwn, out _out325, out _out326, out _out327, out _out328);
                      s = _out325;
                      isOwned = _out326;
                      isErased = _out327;
                      readIdents = _out328;
                    }
                  }
                } else if (_source32.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _694___mcc_h253 = _source32.dtor_args;
                  DAST._IType _695___mcc_h254 = _source32.dtor_result;
                  DAST._IType _696_b = _625___mcc_h211;
                  {
                    if (object.Equals(_696_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _697_recursiveGen;
                      bool _698_recOwned;
                      bool _699_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _700_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out329;
                      bool _out330;
                      bool _out331;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out332;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out329, out _out330, out _out331, out _out332);
                      _697_recursiveGen = _out329;
                      _698_recOwned = _out330;
                      _699_recErased = _out331;
                      _700_recIdents = _out332;
                      Dafny.ISequence<Dafny.Rune> _701_uneraseFn;
                      _701_uneraseFn = ((_698_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _701_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _697_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _698_recOwned;
                      isErased = true;
                      readIdents = _700_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out333;
                      bool _out334;
                      bool _out335;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _696_b), _696_b, _465_toTpe), @params, mustOwn, out _out333, out _out334, out _out335, out _out336);
                      s = _out333;
                      isOwned = _out334;
                      isErased = _out335;
                      readIdents = _out336;
                    }
                  }
                } else if (_source32.is_Primitive) {
                  DAST._IPrimitive _702___mcc_h259 = _source32.dtor_Primitive_a0;
                  DAST._IType _703_b = _625___mcc_h211;
                  {
                    if (object.Equals(_703_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _704_recursiveGen;
                      bool _705_recOwned;
                      bool _706_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _707_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out337;
                      bool _out338;
                      bool _out339;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out340;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out337, out _out338, out _out339, out _out340);
                      _704_recursiveGen = _out337;
                      _705_recOwned = _out338;
                      _706_recErased = _out339;
                      _707_recIdents = _out340;
                      Dafny.ISequence<Dafny.Rune> _708_uneraseFn;
                      _708_uneraseFn = ((_705_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _708_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _704_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _705_recOwned;
                      isErased = true;
                      readIdents = _707_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out341;
                      bool _out342;
                      bool _out343;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _703_b), _703_b, _465_toTpe), @params, mustOwn, out _out341, out _out342, out _out343, out _out344);
                      s = _out341;
                      isOwned = _out342;
                      isErased = _out343;
                      readIdents = _out344;
                    }
                  }
                } else if (_source32.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _709___mcc_h262 = _source32.dtor_Passthrough_a0;
                  DAST._IType _710_b = _625___mcc_h211;
                  {
                    if (object.Equals(_710_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _711_recursiveGen;
                      bool _712_recOwned;
                      bool _713_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _714_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out345;
                      bool _out346;
                      bool _out347;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out345, out _out346, out _out347, out _out348);
                      _711_recursiveGen = _out345;
                      _712_recOwned = _out346;
                      _713_recErased = _out347;
                      _714_recIdents = _out348;
                      Dafny.ISequence<Dafny.Rune> _715_uneraseFn;
                      _715_uneraseFn = ((_712_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _715_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _711_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _712_recOwned;
                      isErased = true;
                      readIdents = _714_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out349;
                      bool _out350;
                      bool _out351;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _710_b), _710_b, _465_toTpe), @params, mustOwn, out _out349, out _out350, out _out351, out _out352);
                      s = _out349;
                      isOwned = _out350;
                      isErased = _out351;
                      readIdents = _out352;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _716___mcc_h265 = _source32.dtor_TypeArg_a0;
                  DAST._IType _717_b = _625___mcc_h211;
                  {
                    if (object.Equals(_717_b, _465_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _718_recursiveGen;
                      bool _719_recOwned;
                      bool _720_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _721_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out353;
                      bool _out354;
                      bool _out355;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out356;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out353, out _out354, out _out355, out _out356);
                      _718_recursiveGen = _out353;
                      _719_recOwned = _out354;
                      _720_recErased = _out355;
                      _721_recIdents = _out356;
                      Dafny.ISequence<Dafny.Rune> _722_uneraseFn;
                      _722_uneraseFn = ((_719_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _722_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _718_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _719_recOwned;
                      isErased = true;
                      readIdents = _721_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out357;
                      bool _out358;
                      bool _out359;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out360;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _717_b), _717_b, _465_toTpe), @params, mustOwn, out _out357, out _out358, out _out359, out _out360);
                      s = _out357;
                      isOwned = _out358;
                      isErased = _out359;
                      readIdents = _out360;
                    }
                  }
                }
              }
            } else if (_source26.is_Tuple) {
              Dafny.ISequence<DAST._IType> _723___mcc_h268 = _source26.dtor_Tuple_a0;
              DAST._IType _source34 = _473___mcc_h121;
              if (_source34.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _724___mcc_h271 = _source34.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _725___mcc_h272 = _source34.dtor_typeArgs;
                DAST._IResolvedType _726___mcc_h273 = _source34.dtor_resolved;
                DAST._IResolvedType _source35 = _726___mcc_h273;
                if (_source35.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _727___mcc_h277 = _source35.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _728_recursiveGen;
                    bool _729_recOwned;
                    bool _730_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _731_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out361;
                    bool _out362;
                    bool _out363;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out361, out _out362, out _out363, out _out364);
                    _728_recursiveGen = _out361;
                    _729_recOwned = _out362;
                    _730_recErased = _out363;
                    _731_recIdents = _out364;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _728_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _729_recOwned;
                    isErased = _730_recErased;
                    readIdents = _731_recIdents;
                  }
                } else if (_source35.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _732___mcc_h279 = _source35.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _733_recursiveGen;
                    bool _734_recOwned;
                    bool _735_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _736_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out365;
                    bool _out366;
                    bool _out367;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out368;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out365, out _out366, out _out367, out _out368);
                    _733_recursiveGen = _out365;
                    _734_recOwned = _out366;
                    _735_recErased = _out367;
                    _736_recIdents = _out368;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _733_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _734_recOwned;
                    isErased = _735_recErased;
                    readIdents = _736_recIdents;
                  }
                } else {
                  DAST._IType _737___mcc_h281 = _source35.dtor_Newtype_a0;
                  DAST._IType _738_b = _737___mcc_h281;
                  {
                    if (object.Equals(_466_fromTpe, _738_b)) {
                      Dafny.ISequence<Dafny.Rune> _739_recursiveGen;
                      bool _740_recOwned;
                      bool _741_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _742_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out369;
                      bool _out370;
                      bool _out371;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out369, out _out370, out _out371, out _out372);
                      _739_recursiveGen = _out369;
                      _740_recOwned = _out370;
                      _741_recErased = _out371;
                      _742_recIdents = _out372;
                      Dafny.ISequence<Dafny.Rune> _743_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out373;
                      _out373 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _743_rhsType = _out373;
                      Dafny.ISequence<Dafny.Rune> _744_uneraseFn;
                      _744_uneraseFn = ((_740_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _743_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _744_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _739_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _740_recOwned;
                      isErased = false;
                      readIdents = _742_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out374;
                      bool _out375;
                      bool _out376;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out377;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _738_b), _738_b, _465_toTpe), @params, mustOwn, out _out374, out _out375, out _out376, out _out377);
                      s = _out374;
                      isOwned = _out375;
                      isErased = _out376;
                      readIdents = _out377;
                    }
                  }
                }
              } else if (_source34.is_Tuple) {
                Dafny.ISequence<DAST._IType> _745___mcc_h283 = _source34.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _746_recursiveGen;
                  bool _747_recOwned;
                  bool _748_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _749_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out378;
                  bool _out379;
                  bool _out380;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out381;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out378, out _out379, out _out380, out _out381);
                  _746_recursiveGen = _out378;
                  _747_recOwned = _out379;
                  _748_recErased = _out380;
                  _749_recIdents = _out381;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _746_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _747_recOwned;
                  isErased = _748_recErased;
                  readIdents = _749_recIdents;
                }
              } else if (_source34.is_Array) {
                DAST._IType _750___mcc_h285 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _751_recursiveGen;
                  bool _752_recOwned;
                  bool _753_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _754_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out382;
                  bool _out383;
                  bool _out384;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out382, out _out383, out _out384, out _out385);
                  _751_recursiveGen = _out382;
                  _752_recOwned = _out383;
                  _753_recErased = _out384;
                  _754_recIdents = _out385;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _751_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _752_recOwned;
                  isErased = _753_recErased;
                  readIdents = _754_recIdents;
                }
              } else if (_source34.is_Seq) {
                DAST._IType _755___mcc_h287 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _756_recursiveGen;
                  bool _757_recOwned;
                  bool _758_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _759_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out386;
                  bool _out387;
                  bool _out388;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out386, out _out387, out _out388, out _out389);
                  _756_recursiveGen = _out386;
                  _757_recOwned = _out387;
                  _758_recErased = _out388;
                  _759_recIdents = _out389;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _756_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _757_recOwned;
                  isErased = _758_recErased;
                  readIdents = _759_recIdents;
                }
              } else if (_source34.is_Set) {
                DAST._IType _760___mcc_h289 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _761_recursiveGen;
                  bool _762_recOwned;
                  bool _763_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _764_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out390;
                  bool _out391;
                  bool _out392;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out393;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out390, out _out391, out _out392, out _out393);
                  _761_recursiveGen = _out390;
                  _762_recOwned = _out391;
                  _763_recErased = _out392;
                  _764_recIdents = _out393;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _761_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _762_recOwned;
                  isErased = _763_recErased;
                  readIdents = _764_recIdents;
                }
              } else if (_source34.is_Multiset) {
                DAST._IType _765___mcc_h291 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _766_recursiveGen;
                  bool _767_recOwned;
                  bool _768_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _769_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out394;
                  bool _out395;
                  bool _out396;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out394, out _out395, out _out396, out _out397);
                  _766_recursiveGen = _out394;
                  _767_recOwned = _out395;
                  _768_recErased = _out396;
                  _769_recIdents = _out397;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _766_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _767_recOwned;
                  isErased = _768_recErased;
                  readIdents = _769_recIdents;
                }
              } else if (_source34.is_Map) {
                DAST._IType _770___mcc_h293 = _source34.dtor_key;
                DAST._IType _771___mcc_h294 = _source34.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _772_recursiveGen;
                  bool _773_recOwned;
                  bool _774_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _775_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out398;
                  bool _out399;
                  bool _out400;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out401;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out398, out _out399, out _out400, out _out401);
                  _772_recursiveGen = _out398;
                  _773_recOwned = _out399;
                  _774_recErased = _out400;
                  _775_recIdents = _out401;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _772_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _773_recOwned;
                  isErased = _774_recErased;
                  readIdents = _775_recIdents;
                }
              } else if (_source34.is_Arrow) {
                Dafny.ISequence<DAST._IType> _776___mcc_h297 = _source34.dtor_args;
                DAST._IType _777___mcc_h298 = _source34.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _778_recursiveGen;
                  bool _779_recOwned;
                  bool _780_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _781_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out402;
                  bool _out403;
                  bool _out404;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out405;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out402, out _out403, out _out404, out _out405);
                  _778_recursiveGen = _out402;
                  _779_recOwned = _out403;
                  _780_recErased = _out404;
                  _781_recIdents = _out405;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _778_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _779_recOwned;
                  isErased = _780_recErased;
                  readIdents = _781_recIdents;
                }
              } else if (_source34.is_Primitive) {
                DAST._IPrimitive _782___mcc_h301 = _source34.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _783_recursiveGen;
                  bool _784_recOwned;
                  bool _785_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _786_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out406;
                  bool _out407;
                  bool _out408;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out406, out _out407, out _out408, out _out409);
                  _783_recursiveGen = _out406;
                  _784_recOwned = _out407;
                  _785_recErased = _out408;
                  _786_recIdents = _out409;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _783_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _784_recOwned;
                  isErased = _785_recErased;
                  readIdents = _786_recIdents;
                }
              } else if (_source34.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _787___mcc_h303 = _source34.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _788_recursiveGen;
                  bool _789_recOwned;
                  bool _790_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _791_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out410;
                  bool _out411;
                  bool _out412;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out413;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out410, out _out411, out _out412, out _out413);
                  _788_recursiveGen = _out410;
                  _789_recOwned = _out411;
                  _790_recErased = _out412;
                  _791_recIdents = _out413;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _788_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _789_recOwned;
                  isErased = _790_recErased;
                  readIdents = _791_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _792___mcc_h305 = _source34.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _793_recursiveGen;
                  bool _794_recOwned;
                  bool _795_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _796_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out414;
                  bool _out415;
                  bool _out416;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out417;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out414, out _out415, out _out416, out _out417);
                  _793_recursiveGen = _out414;
                  _794_recOwned = _out415;
                  _795_recErased = _out416;
                  _796_recIdents = _out417;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _793_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _794_recOwned;
                  isErased = _795_recErased;
                  readIdents = _796_recIdents;
                }
              }
            } else if (_source26.is_Array) {
              DAST._IType _797___mcc_h307 = _source26.dtor_element;
              DAST._IType _source36 = _473___mcc_h121;
              if (_source36.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _798___mcc_h310 = _source36.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _799___mcc_h311 = _source36.dtor_typeArgs;
                DAST._IResolvedType _800___mcc_h312 = _source36.dtor_resolved;
                DAST._IResolvedType _source37 = _800___mcc_h312;
                if (_source37.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _801___mcc_h316 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _802_recursiveGen;
                    bool _803_recOwned;
                    bool _804_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _805_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out418;
                    bool _out419;
                    bool _out420;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out418, out _out419, out _out420, out _out421);
                    _802_recursiveGen = _out418;
                    _803_recOwned = _out419;
                    _804_recErased = _out420;
                    _805_recIdents = _out421;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _802_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _803_recOwned;
                    isErased = _804_recErased;
                    readIdents = _805_recIdents;
                  }
                } else if (_source37.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _806___mcc_h318 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _807_recursiveGen;
                    bool _808_recOwned;
                    bool _809_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _810_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out422;
                    bool _out423;
                    bool _out424;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out425;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out422, out _out423, out _out424, out _out425);
                    _807_recursiveGen = _out422;
                    _808_recOwned = _out423;
                    _809_recErased = _out424;
                    _810_recIdents = _out425;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _807_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _808_recOwned;
                    isErased = _809_recErased;
                    readIdents = _810_recIdents;
                  }
                } else {
                  DAST._IType _811___mcc_h320 = _source37.dtor_Newtype_a0;
                  DAST._IType _812_b = _811___mcc_h320;
                  {
                    if (object.Equals(_466_fromTpe, _812_b)) {
                      Dafny.ISequence<Dafny.Rune> _813_recursiveGen;
                      bool _814_recOwned;
                      bool _815_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _816_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out426;
                      bool _out427;
                      bool _out428;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out426, out _out427, out _out428, out _out429);
                      _813_recursiveGen = _out426;
                      _814_recOwned = _out427;
                      _815_recErased = _out428;
                      _816_recIdents = _out429;
                      Dafny.ISequence<Dafny.Rune> _817_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out430;
                      _out430 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _817_rhsType = _out430;
                      Dafny.ISequence<Dafny.Rune> _818_uneraseFn;
                      _818_uneraseFn = ((_814_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _817_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _818_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _813_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _814_recOwned;
                      isErased = false;
                      readIdents = _816_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out431;
                      bool _out432;
                      bool _out433;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out434;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _812_b), _812_b, _465_toTpe), @params, mustOwn, out _out431, out _out432, out _out433, out _out434);
                      s = _out431;
                      isOwned = _out432;
                      isErased = _out433;
                      readIdents = _out434;
                    }
                  }
                }
              } else if (_source36.is_Tuple) {
                Dafny.ISequence<DAST._IType> _819___mcc_h322 = _source36.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _820_recursiveGen;
                  bool _821_recOwned;
                  bool _822_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _823_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out435;
                  bool _out436;
                  bool _out437;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out438;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out435, out _out436, out _out437, out _out438);
                  _820_recursiveGen = _out435;
                  _821_recOwned = _out436;
                  _822_recErased = _out437;
                  _823_recIdents = _out438;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _820_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _821_recOwned;
                  isErased = _822_recErased;
                  readIdents = _823_recIdents;
                }
              } else if (_source36.is_Array) {
                DAST._IType _824___mcc_h324 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _825_recursiveGen;
                  bool _826_recOwned;
                  bool _827_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _828_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out439;
                  bool _out440;
                  bool _out441;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out439, out _out440, out _out441, out _out442);
                  _825_recursiveGen = _out439;
                  _826_recOwned = _out440;
                  _827_recErased = _out441;
                  _828_recIdents = _out442;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _825_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _826_recOwned;
                  isErased = _827_recErased;
                  readIdents = _828_recIdents;
                }
              } else if (_source36.is_Seq) {
                DAST._IType _829___mcc_h326 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _830_recursiveGen;
                  bool _831_recOwned;
                  bool _832_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _833_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out443;
                  bool _out444;
                  bool _out445;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out446;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out443, out _out444, out _out445, out _out446);
                  _830_recursiveGen = _out443;
                  _831_recOwned = _out444;
                  _832_recErased = _out445;
                  _833_recIdents = _out446;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _830_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _831_recOwned;
                  isErased = _832_recErased;
                  readIdents = _833_recIdents;
                }
              } else if (_source36.is_Set) {
                DAST._IType _834___mcc_h328 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _835_recursiveGen;
                  bool _836_recOwned;
                  bool _837_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _838_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out447;
                  bool _out448;
                  bool _out449;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out447, out _out448, out _out449, out _out450);
                  _835_recursiveGen = _out447;
                  _836_recOwned = _out448;
                  _837_recErased = _out449;
                  _838_recIdents = _out450;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _835_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _836_recOwned;
                  isErased = _837_recErased;
                  readIdents = _838_recIdents;
                }
              } else if (_source36.is_Multiset) {
                DAST._IType _839___mcc_h330 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _840_recursiveGen;
                  bool _841_recOwned;
                  bool _842_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _843_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out451;
                  bool _out452;
                  bool _out453;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out451, out _out452, out _out453, out _out454);
                  _840_recursiveGen = _out451;
                  _841_recOwned = _out452;
                  _842_recErased = _out453;
                  _843_recIdents = _out454;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _840_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _841_recOwned;
                  isErased = _842_recErased;
                  readIdents = _843_recIdents;
                }
              } else if (_source36.is_Map) {
                DAST._IType _844___mcc_h332 = _source36.dtor_key;
                DAST._IType _845___mcc_h333 = _source36.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _846_recursiveGen;
                  bool _847_recOwned;
                  bool _848_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _849_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out455;
                  bool _out456;
                  bool _out457;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out455, out _out456, out _out457, out _out458);
                  _846_recursiveGen = _out455;
                  _847_recOwned = _out456;
                  _848_recErased = _out457;
                  _849_recIdents = _out458;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _846_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _847_recOwned;
                  isErased = _848_recErased;
                  readIdents = _849_recIdents;
                }
              } else if (_source36.is_Arrow) {
                Dafny.ISequence<DAST._IType> _850___mcc_h336 = _source36.dtor_args;
                DAST._IType _851___mcc_h337 = _source36.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _852_recursiveGen;
                  bool _853_recOwned;
                  bool _854_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _855_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out459;
                  bool _out460;
                  bool _out461;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out462;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out459, out _out460, out _out461, out _out462);
                  _852_recursiveGen = _out459;
                  _853_recOwned = _out460;
                  _854_recErased = _out461;
                  _855_recIdents = _out462;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _852_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _853_recOwned;
                  isErased = _854_recErased;
                  readIdents = _855_recIdents;
                }
              } else if (_source36.is_Primitive) {
                DAST._IPrimitive _856___mcc_h340 = _source36.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _857_recursiveGen;
                  bool _858_recOwned;
                  bool _859_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _860_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out463;
                  bool _out464;
                  bool _out465;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out463, out _out464, out _out465, out _out466);
                  _857_recursiveGen = _out463;
                  _858_recOwned = _out464;
                  _859_recErased = _out465;
                  _860_recIdents = _out466;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _857_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _858_recOwned;
                  isErased = _859_recErased;
                  readIdents = _860_recIdents;
                }
              } else if (_source36.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _861___mcc_h342 = _source36.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _862_recursiveGen;
                  bool _863_recOwned;
                  bool _864_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _865_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out467;
                  bool _out468;
                  bool _out469;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out467, out _out468, out _out469, out _out470);
                  _862_recursiveGen = _out467;
                  _863_recOwned = _out468;
                  _864_recErased = _out469;
                  _865_recIdents = _out470;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _862_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _863_recOwned;
                  isErased = _864_recErased;
                  readIdents = _865_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _866___mcc_h344 = _source36.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _867_recursiveGen;
                  bool _868_recOwned;
                  bool _869_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _870_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out471;
                  bool _out472;
                  bool _out473;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out471, out _out472, out _out473, out _out474);
                  _867_recursiveGen = _out471;
                  _868_recOwned = _out472;
                  _869_recErased = _out473;
                  _870_recIdents = _out474;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _867_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _868_recOwned;
                  isErased = _869_recErased;
                  readIdents = _870_recIdents;
                }
              }
            } else if (_source26.is_Seq) {
              DAST._IType _871___mcc_h346 = _source26.dtor_element;
              DAST._IType _source38 = _473___mcc_h121;
              if (_source38.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _872___mcc_h349 = _source38.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _873___mcc_h350 = _source38.dtor_typeArgs;
                DAST._IResolvedType _874___mcc_h351 = _source38.dtor_resolved;
                DAST._IResolvedType _source39 = _874___mcc_h351;
                if (_source39.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _875___mcc_h355 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _876_recursiveGen;
                    bool _877_recOwned;
                    bool _878_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _879_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out475;
                    bool _out476;
                    bool _out477;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out475, out _out476, out _out477, out _out478);
                    _876_recursiveGen = _out475;
                    _877_recOwned = _out476;
                    _878_recErased = _out477;
                    _879_recIdents = _out478;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _877_recOwned;
                    isErased = _878_recErased;
                    readIdents = _879_recIdents;
                  }
                } else if (_source39.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _880___mcc_h357 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _881_recursiveGen;
                    bool _882_recOwned;
                    bool _883_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _884_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out479;
                    bool _out480;
                    bool _out481;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out479, out _out480, out _out481, out _out482);
                    _881_recursiveGen = _out479;
                    _882_recOwned = _out480;
                    _883_recErased = _out481;
                    _884_recIdents = _out482;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _881_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _882_recOwned;
                    isErased = _883_recErased;
                    readIdents = _884_recIdents;
                  }
                } else {
                  DAST._IType _885___mcc_h359 = _source39.dtor_Newtype_a0;
                  DAST._IType _886_b = _885___mcc_h359;
                  {
                    if (object.Equals(_466_fromTpe, _886_b)) {
                      Dafny.ISequence<Dafny.Rune> _887_recursiveGen;
                      bool _888_recOwned;
                      bool _889_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _890_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out483;
                      bool _out484;
                      bool _out485;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out486;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out483, out _out484, out _out485, out _out486);
                      _887_recursiveGen = _out483;
                      _888_recOwned = _out484;
                      _889_recErased = _out485;
                      _890_recIdents = _out486;
                      Dafny.ISequence<Dafny.Rune> _891_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out487;
                      _out487 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _891_rhsType = _out487;
                      Dafny.ISequence<Dafny.Rune> _892_uneraseFn;
                      _892_uneraseFn = ((_888_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _891_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _892_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _887_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _888_recOwned;
                      isErased = false;
                      readIdents = _890_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out488;
                      bool _out489;
                      bool _out490;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out491;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _886_b), _886_b, _465_toTpe), @params, mustOwn, out _out488, out _out489, out _out490, out _out491);
                      s = _out488;
                      isOwned = _out489;
                      isErased = _out490;
                      readIdents = _out491;
                    }
                  }
                }
              } else if (_source38.is_Tuple) {
                Dafny.ISequence<DAST._IType> _893___mcc_h361 = _source38.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _894_recursiveGen;
                  bool _895_recOwned;
                  bool _896_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _897_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out492;
                  bool _out493;
                  bool _out494;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out492, out _out493, out _out494, out _out495);
                  _894_recursiveGen = _out492;
                  _895_recOwned = _out493;
                  _896_recErased = _out494;
                  _897_recIdents = _out495;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _894_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _895_recOwned;
                  isErased = _896_recErased;
                  readIdents = _897_recIdents;
                }
              } else if (_source38.is_Array) {
                DAST._IType _898___mcc_h363 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _899_recursiveGen;
                  bool _900_recOwned;
                  bool _901_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _902_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out496;
                  bool _out497;
                  bool _out498;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out496, out _out497, out _out498, out _out499);
                  _899_recursiveGen = _out496;
                  _900_recOwned = _out497;
                  _901_recErased = _out498;
                  _902_recIdents = _out499;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _899_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _900_recOwned;
                  isErased = _901_recErased;
                  readIdents = _902_recIdents;
                }
              } else if (_source38.is_Seq) {
                DAST._IType _903___mcc_h365 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _904_recursiveGen;
                  bool _905_recOwned;
                  bool _906_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _907_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out500;
                  bool _out501;
                  bool _out502;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out503;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out500, out _out501, out _out502, out _out503);
                  _904_recursiveGen = _out500;
                  _905_recOwned = _out501;
                  _906_recErased = _out502;
                  _907_recIdents = _out503;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _904_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _905_recOwned;
                  isErased = _906_recErased;
                  readIdents = _907_recIdents;
                }
              } else if (_source38.is_Set) {
                DAST._IType _908___mcc_h367 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _909_recursiveGen;
                  bool _910_recOwned;
                  bool _911_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _912_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out504;
                  bool _out505;
                  bool _out506;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out507;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out504, out _out505, out _out506, out _out507);
                  _909_recursiveGen = _out504;
                  _910_recOwned = _out505;
                  _911_recErased = _out506;
                  _912_recIdents = _out507;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _909_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _910_recOwned;
                  isErased = _911_recErased;
                  readIdents = _912_recIdents;
                }
              } else if (_source38.is_Multiset) {
                DAST._IType _913___mcc_h369 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _914_recursiveGen;
                  bool _915_recOwned;
                  bool _916_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _917_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out508;
                  bool _out509;
                  bool _out510;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out508, out _out509, out _out510, out _out511);
                  _914_recursiveGen = _out508;
                  _915_recOwned = _out509;
                  _916_recErased = _out510;
                  _917_recIdents = _out511;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _914_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _915_recOwned;
                  isErased = _916_recErased;
                  readIdents = _917_recIdents;
                }
              } else if (_source38.is_Map) {
                DAST._IType _918___mcc_h371 = _source38.dtor_key;
                DAST._IType _919___mcc_h372 = _source38.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _920_recursiveGen;
                  bool _921_recOwned;
                  bool _922_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _923_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out512;
                  bool _out513;
                  bool _out514;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out515;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out512, out _out513, out _out514, out _out515);
                  _920_recursiveGen = _out512;
                  _921_recOwned = _out513;
                  _922_recErased = _out514;
                  _923_recIdents = _out515;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _920_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _921_recOwned;
                  isErased = _922_recErased;
                  readIdents = _923_recIdents;
                }
              } else if (_source38.is_Arrow) {
                Dafny.ISequence<DAST._IType> _924___mcc_h375 = _source38.dtor_args;
                DAST._IType _925___mcc_h376 = _source38.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _926_recursiveGen;
                  bool _927_recOwned;
                  bool _928_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _929_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out516;
                  bool _out517;
                  bool _out518;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out516, out _out517, out _out518, out _out519);
                  _926_recursiveGen = _out516;
                  _927_recOwned = _out517;
                  _928_recErased = _out518;
                  _929_recIdents = _out519;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _926_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _927_recOwned;
                  isErased = _928_recErased;
                  readIdents = _929_recIdents;
                }
              } else if (_source38.is_Primitive) {
                DAST._IPrimitive _930___mcc_h379 = _source38.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _931_recursiveGen;
                  bool _932_recOwned;
                  bool _933_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _934_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out520;
                  bool _out521;
                  bool _out522;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out523;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out520, out _out521, out _out522, out _out523);
                  _931_recursiveGen = _out520;
                  _932_recOwned = _out521;
                  _933_recErased = _out522;
                  _934_recIdents = _out523;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _931_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _932_recOwned;
                  isErased = _933_recErased;
                  readIdents = _934_recIdents;
                }
              } else if (_source38.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _935___mcc_h381 = _source38.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _936_recursiveGen;
                  bool _937_recOwned;
                  bool _938_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _939_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out524;
                  bool _out525;
                  bool _out526;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out527;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out524, out _out525, out _out526, out _out527);
                  _936_recursiveGen = _out524;
                  _937_recOwned = _out525;
                  _938_recErased = _out526;
                  _939_recIdents = _out527;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _936_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _937_recOwned;
                  isErased = _938_recErased;
                  readIdents = _939_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _940___mcc_h383 = _source38.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _941_recursiveGen;
                  bool _942_recOwned;
                  bool _943_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _944_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out528;
                  bool _out529;
                  bool _out530;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out531;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out528, out _out529, out _out530, out _out531);
                  _941_recursiveGen = _out528;
                  _942_recOwned = _out529;
                  _943_recErased = _out530;
                  _944_recIdents = _out531;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _941_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _942_recOwned;
                  isErased = _943_recErased;
                  readIdents = _944_recIdents;
                }
              }
            } else if (_source26.is_Set) {
              DAST._IType _945___mcc_h385 = _source26.dtor_element;
              DAST._IType _source40 = _473___mcc_h121;
              if (_source40.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _946___mcc_h388 = _source40.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _947___mcc_h389 = _source40.dtor_typeArgs;
                DAST._IResolvedType _948___mcc_h390 = _source40.dtor_resolved;
                DAST._IResolvedType _source41 = _948___mcc_h390;
                if (_source41.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _949___mcc_h394 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _950_recursiveGen;
                    bool _951_recOwned;
                    bool _952_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _953_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out532;
                    bool _out533;
                    bool _out534;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out532, out _out533, out _out534, out _out535);
                    _950_recursiveGen = _out532;
                    _951_recOwned = _out533;
                    _952_recErased = _out534;
                    _953_recIdents = _out535;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _950_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _951_recOwned;
                    isErased = _952_recErased;
                    readIdents = _953_recIdents;
                  }
                } else if (_source41.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _954___mcc_h396 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _955_recursiveGen;
                    bool _956_recOwned;
                    bool _957_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _958_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out536;
                    bool _out537;
                    bool _out538;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out539;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out536, out _out537, out _out538, out _out539);
                    _955_recursiveGen = _out536;
                    _956_recOwned = _out537;
                    _957_recErased = _out538;
                    _958_recIdents = _out539;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _955_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _956_recOwned;
                    isErased = _957_recErased;
                    readIdents = _958_recIdents;
                  }
                } else {
                  DAST._IType _959___mcc_h398 = _source41.dtor_Newtype_a0;
                  DAST._IType _960_b = _959___mcc_h398;
                  {
                    if (object.Equals(_466_fromTpe, _960_b)) {
                      Dafny.ISequence<Dafny.Rune> _961_recursiveGen;
                      bool _962_recOwned;
                      bool _963_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _964_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out540;
                      bool _out541;
                      bool _out542;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out543;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out540, out _out541, out _out542, out _out543);
                      _961_recursiveGen = _out540;
                      _962_recOwned = _out541;
                      _963_recErased = _out542;
                      _964_recIdents = _out543;
                      Dafny.ISequence<Dafny.Rune> _965_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out544;
                      _out544 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _965_rhsType = _out544;
                      Dafny.ISequence<Dafny.Rune> _966_uneraseFn;
                      _966_uneraseFn = ((_962_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _965_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _966_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _961_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _962_recOwned;
                      isErased = false;
                      readIdents = _964_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out545;
                      bool _out546;
                      bool _out547;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out548;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _960_b), _960_b, _465_toTpe), @params, mustOwn, out _out545, out _out546, out _out547, out _out548);
                      s = _out545;
                      isOwned = _out546;
                      isErased = _out547;
                      readIdents = _out548;
                    }
                  }
                }
              } else if (_source40.is_Tuple) {
                Dafny.ISequence<DAST._IType> _967___mcc_h400 = _source40.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _968_recursiveGen;
                  bool _969_recOwned;
                  bool _970_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _971_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out549;
                  bool _out550;
                  bool _out551;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out549, out _out550, out _out551, out _out552);
                  _968_recursiveGen = _out549;
                  _969_recOwned = _out550;
                  _970_recErased = _out551;
                  _971_recIdents = _out552;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _968_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _969_recOwned;
                  isErased = _970_recErased;
                  readIdents = _971_recIdents;
                }
              } else if (_source40.is_Array) {
                DAST._IType _972___mcc_h402 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _973_recursiveGen;
                  bool _974_recOwned;
                  bool _975_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _976_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out553;
                  bool _out554;
                  bool _out555;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out553, out _out554, out _out555, out _out556);
                  _973_recursiveGen = _out553;
                  _974_recOwned = _out554;
                  _975_recErased = _out555;
                  _976_recIdents = _out556;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _973_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _974_recOwned;
                  isErased = _975_recErased;
                  readIdents = _976_recIdents;
                }
              } else if (_source40.is_Seq) {
                DAST._IType _977___mcc_h404 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _978_recursiveGen;
                  bool _979_recOwned;
                  bool _980_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _981_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out557;
                  bool _out558;
                  bool _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out557, out _out558, out _out559, out _out560);
                  _978_recursiveGen = _out557;
                  _979_recOwned = _out558;
                  _980_recErased = _out559;
                  _981_recIdents = _out560;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _978_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _979_recOwned;
                  isErased = _980_recErased;
                  readIdents = _981_recIdents;
                }
              } else if (_source40.is_Set) {
                DAST._IType _982___mcc_h406 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _983_recursiveGen;
                  bool _984_recOwned;
                  bool _985_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _986_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out561;
                  bool _out562;
                  bool _out563;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out564;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out561, out _out562, out _out563, out _out564);
                  _983_recursiveGen = _out561;
                  _984_recOwned = _out562;
                  _985_recErased = _out563;
                  _986_recIdents = _out564;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _983_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _984_recOwned;
                  isErased = _985_recErased;
                  readIdents = _986_recIdents;
                }
              } else if (_source40.is_Multiset) {
                DAST._IType _987___mcc_h408 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _988_recursiveGen;
                  bool _989_recOwned;
                  bool _990_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _991_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out565;
                  bool _out566;
                  bool _out567;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out565, out _out566, out _out567, out _out568);
                  _988_recursiveGen = _out565;
                  _989_recOwned = _out566;
                  _990_recErased = _out567;
                  _991_recIdents = _out568;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _988_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _989_recOwned;
                  isErased = _990_recErased;
                  readIdents = _991_recIdents;
                }
              } else if (_source40.is_Map) {
                DAST._IType _992___mcc_h410 = _source40.dtor_key;
                DAST._IType _993___mcc_h411 = _source40.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _994_recursiveGen;
                  bool _995_recOwned;
                  bool _996_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _997_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out569;
                  bool _out570;
                  bool _out571;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out572;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out569, out _out570, out _out571, out _out572);
                  _994_recursiveGen = _out569;
                  _995_recOwned = _out570;
                  _996_recErased = _out571;
                  _997_recIdents = _out572;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _994_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _995_recOwned;
                  isErased = _996_recErased;
                  readIdents = _997_recIdents;
                }
              } else if (_source40.is_Arrow) {
                Dafny.ISequence<DAST._IType> _998___mcc_h414 = _source40.dtor_args;
                DAST._IType _999___mcc_h415 = _source40.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1000_recursiveGen;
                  bool _1001_recOwned;
                  bool _1002_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1003_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out573;
                  bool _out574;
                  bool _out575;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out576;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out573, out _out574, out _out575, out _out576);
                  _1000_recursiveGen = _out573;
                  _1001_recOwned = _out574;
                  _1002_recErased = _out575;
                  _1003_recIdents = _out576;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1000_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1001_recOwned;
                  isErased = _1002_recErased;
                  readIdents = _1003_recIdents;
                }
              } else if (_source40.is_Primitive) {
                DAST._IPrimitive _1004___mcc_h418 = _source40.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1005_recursiveGen;
                  bool _1006_recOwned;
                  bool _1007_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1008_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out577;
                  bool _out578;
                  bool _out579;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out577, out _out578, out _out579, out _out580);
                  _1005_recursiveGen = _out577;
                  _1006_recOwned = _out578;
                  _1007_recErased = _out579;
                  _1008_recIdents = _out580;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1005_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1006_recOwned;
                  isErased = _1007_recErased;
                  readIdents = _1008_recIdents;
                }
              } else if (_source40.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1009___mcc_h420 = _source40.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1010_recursiveGen;
                  bool _1011_recOwned;
                  bool _1012_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1013_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out581;
                  bool _out582;
                  bool _out583;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out584;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out581, out _out582, out _out583, out _out584);
                  _1010_recursiveGen = _out581;
                  _1011_recOwned = _out582;
                  _1012_recErased = _out583;
                  _1013_recIdents = _out584;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1010_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1011_recOwned;
                  isErased = _1012_recErased;
                  readIdents = _1013_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1014___mcc_h422 = _source40.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1015_recursiveGen;
                  bool _1016_recOwned;
                  bool _1017_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1018_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out585;
                  bool _out586;
                  bool _out587;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out588;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out585, out _out586, out _out587, out _out588);
                  _1015_recursiveGen = _out585;
                  _1016_recOwned = _out586;
                  _1017_recErased = _out587;
                  _1018_recIdents = _out588;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1015_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1016_recOwned;
                  isErased = _1017_recErased;
                  readIdents = _1018_recIdents;
                }
              }
            } else if (_source26.is_Multiset) {
              DAST._IType _1019___mcc_h424 = _source26.dtor_element;
              DAST._IType _source42 = _473___mcc_h121;
              if (_source42.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1020___mcc_h427 = _source42.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1021___mcc_h428 = _source42.dtor_typeArgs;
                DAST._IResolvedType _1022___mcc_h429 = _source42.dtor_resolved;
                DAST._IResolvedType _source43 = _1022___mcc_h429;
                if (_source43.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1023___mcc_h433 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1024_recursiveGen;
                    bool _1025_recOwned;
                    bool _1026_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1027_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out589;
                    bool _out590;
                    bool _out591;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out589, out _out590, out _out591, out _out592);
                    _1024_recursiveGen = _out589;
                    _1025_recOwned = _out590;
                    _1026_recErased = _out591;
                    _1027_recIdents = _out592;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1024_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1025_recOwned;
                    isErased = _1026_recErased;
                    readIdents = _1027_recIdents;
                  }
                } else if (_source43.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1028___mcc_h435 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1029_recursiveGen;
                    bool _1030_recOwned;
                    bool _1031_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1032_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out593;
                    bool _out594;
                    bool _out595;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out596;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out593, out _out594, out _out595, out _out596);
                    _1029_recursiveGen = _out593;
                    _1030_recOwned = _out594;
                    _1031_recErased = _out595;
                    _1032_recIdents = _out596;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1029_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1030_recOwned;
                    isErased = _1031_recErased;
                    readIdents = _1032_recIdents;
                  }
                } else {
                  DAST._IType _1033___mcc_h437 = _source43.dtor_Newtype_a0;
                  DAST._IType _1034_b = _1033___mcc_h437;
                  {
                    if (object.Equals(_466_fromTpe, _1034_b)) {
                      Dafny.ISequence<Dafny.Rune> _1035_recursiveGen;
                      bool _1036_recOwned;
                      bool _1037_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1038_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out597;
                      bool _out598;
                      bool _out599;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out600;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out597, out _out598, out _out599, out _out600);
                      _1035_recursiveGen = _out597;
                      _1036_recOwned = _out598;
                      _1037_recErased = _out599;
                      _1038_recIdents = _out600;
                      Dafny.ISequence<Dafny.Rune> _1039_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out601;
                      _out601 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _1039_rhsType = _out601;
                      Dafny.ISequence<Dafny.Rune> _1040_uneraseFn;
                      _1040_uneraseFn = ((_1036_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1039_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1040_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1035_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1036_recOwned;
                      isErased = false;
                      readIdents = _1038_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out602;
                      bool _out603;
                      bool _out604;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1034_b), _1034_b, _465_toTpe), @params, mustOwn, out _out602, out _out603, out _out604, out _out605);
                      s = _out602;
                      isOwned = _out603;
                      isErased = _out604;
                      readIdents = _out605;
                    }
                  }
                }
              } else if (_source42.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1041___mcc_h439 = _source42.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1042_recursiveGen;
                  bool _1043_recOwned;
                  bool _1044_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1045_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out606;
                  bool _out607;
                  bool _out608;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out606, out _out607, out _out608, out _out609);
                  _1042_recursiveGen = _out606;
                  _1043_recOwned = _out607;
                  _1044_recErased = _out608;
                  _1045_recIdents = _out609;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1042_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1043_recOwned;
                  isErased = _1044_recErased;
                  readIdents = _1045_recIdents;
                }
              } else if (_source42.is_Array) {
                DAST._IType _1046___mcc_h441 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1047_recursiveGen;
                  bool _1048_recOwned;
                  bool _1049_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1050_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out610;
                  bool _out611;
                  bool _out612;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out610, out _out611, out _out612, out _out613);
                  _1047_recursiveGen = _out610;
                  _1048_recOwned = _out611;
                  _1049_recErased = _out612;
                  _1050_recIdents = _out613;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1047_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1048_recOwned;
                  isErased = _1049_recErased;
                  readIdents = _1050_recIdents;
                }
              } else if (_source42.is_Seq) {
                DAST._IType _1051___mcc_h443 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1052_recursiveGen;
                  bool _1053_recOwned;
                  bool _1054_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1055_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out614;
                  bool _out615;
                  bool _out616;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out614, out _out615, out _out616, out _out617);
                  _1052_recursiveGen = _out614;
                  _1053_recOwned = _out615;
                  _1054_recErased = _out616;
                  _1055_recIdents = _out617;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1052_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1053_recOwned;
                  isErased = _1054_recErased;
                  readIdents = _1055_recIdents;
                }
              } else if (_source42.is_Set) {
                DAST._IType _1056___mcc_h445 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1057_recursiveGen;
                  bool _1058_recOwned;
                  bool _1059_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1060_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out618;
                  bool _out619;
                  bool _out620;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out621;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out618, out _out619, out _out620, out _out621);
                  _1057_recursiveGen = _out618;
                  _1058_recOwned = _out619;
                  _1059_recErased = _out620;
                  _1060_recIdents = _out621;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1057_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1058_recOwned;
                  isErased = _1059_recErased;
                  readIdents = _1060_recIdents;
                }
              } else if (_source42.is_Multiset) {
                DAST._IType _1061___mcc_h447 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1062_recursiveGen;
                  bool _1063_recOwned;
                  bool _1064_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1065_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out622;
                  bool _out623;
                  bool _out624;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out622, out _out623, out _out624, out _out625);
                  _1062_recursiveGen = _out622;
                  _1063_recOwned = _out623;
                  _1064_recErased = _out624;
                  _1065_recIdents = _out625;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1062_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1063_recOwned;
                  isErased = _1064_recErased;
                  readIdents = _1065_recIdents;
                }
              } else if (_source42.is_Map) {
                DAST._IType _1066___mcc_h449 = _source42.dtor_key;
                DAST._IType _1067___mcc_h450 = _source42.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1068_recursiveGen;
                  bool _1069_recOwned;
                  bool _1070_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1071_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out626;
                  bool _out627;
                  bool _out628;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out629;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out626, out _out627, out _out628, out _out629);
                  _1068_recursiveGen = _out626;
                  _1069_recOwned = _out627;
                  _1070_recErased = _out628;
                  _1071_recIdents = _out629;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1068_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1069_recOwned;
                  isErased = _1070_recErased;
                  readIdents = _1071_recIdents;
                }
              } else if (_source42.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1072___mcc_h453 = _source42.dtor_args;
                DAST._IType _1073___mcc_h454 = _source42.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1074_recursiveGen;
                  bool _1075_recOwned;
                  bool _1076_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1077_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out630;
                  bool _out631;
                  bool _out632;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out633;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out630, out _out631, out _out632, out _out633);
                  _1074_recursiveGen = _out630;
                  _1075_recOwned = _out631;
                  _1076_recErased = _out632;
                  _1077_recIdents = _out633;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1074_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1075_recOwned;
                  isErased = _1076_recErased;
                  readIdents = _1077_recIdents;
                }
              } else if (_source42.is_Primitive) {
                DAST._IPrimitive _1078___mcc_h457 = _source42.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1079_recursiveGen;
                  bool _1080_recOwned;
                  bool _1081_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1082_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out634;
                  bool _out635;
                  bool _out636;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out634, out _out635, out _out636, out _out637);
                  _1079_recursiveGen = _out634;
                  _1080_recOwned = _out635;
                  _1081_recErased = _out636;
                  _1082_recIdents = _out637;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1079_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1080_recOwned;
                  isErased = _1081_recErased;
                  readIdents = _1082_recIdents;
                }
              } else if (_source42.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1083___mcc_h459 = _source42.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1084_recursiveGen;
                  bool _1085_recOwned;
                  bool _1086_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1087_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out638;
                  bool _out639;
                  bool _out640;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out641;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out638, out _out639, out _out640, out _out641);
                  _1084_recursiveGen = _out638;
                  _1085_recOwned = _out639;
                  _1086_recErased = _out640;
                  _1087_recIdents = _out641;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1084_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1085_recOwned;
                  isErased = _1086_recErased;
                  readIdents = _1087_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1088___mcc_h461 = _source42.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1089_recursiveGen;
                  bool _1090_recOwned;
                  bool _1091_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1092_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out642;
                  bool _out643;
                  bool _out644;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out642, out _out643, out _out644, out _out645);
                  _1089_recursiveGen = _out642;
                  _1090_recOwned = _out643;
                  _1091_recErased = _out644;
                  _1092_recIdents = _out645;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1089_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1090_recOwned;
                  isErased = _1091_recErased;
                  readIdents = _1092_recIdents;
                }
              }
            } else if (_source26.is_Map) {
              DAST._IType _1093___mcc_h463 = _source26.dtor_key;
              DAST._IType _1094___mcc_h464 = _source26.dtor_value;
              DAST._IType _source44 = _473___mcc_h121;
              if (_source44.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1095___mcc_h469 = _source44.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1096___mcc_h470 = _source44.dtor_typeArgs;
                DAST._IResolvedType _1097___mcc_h471 = _source44.dtor_resolved;
                DAST._IResolvedType _source45 = _1097___mcc_h471;
                if (_source45.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1098___mcc_h475 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1099_recursiveGen;
                    bool _1100_recOwned;
                    bool _1101_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1102_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out646;
                    bool _out647;
                    bool _out648;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out646, out _out647, out _out648, out _out649);
                    _1099_recursiveGen = _out646;
                    _1100_recOwned = _out647;
                    _1101_recErased = _out648;
                    _1102_recIdents = _out649;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1099_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1100_recOwned;
                    isErased = _1101_recErased;
                    readIdents = _1102_recIdents;
                  }
                } else if (_source45.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1103___mcc_h477 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1104_recursiveGen;
                    bool _1105_recOwned;
                    bool _1106_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1107_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out650;
                    bool _out651;
                    bool _out652;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out653;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out650, out _out651, out _out652, out _out653);
                    _1104_recursiveGen = _out650;
                    _1105_recOwned = _out651;
                    _1106_recErased = _out652;
                    _1107_recIdents = _out653;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1104_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1105_recOwned;
                    isErased = _1106_recErased;
                    readIdents = _1107_recIdents;
                  }
                } else {
                  DAST._IType _1108___mcc_h479 = _source45.dtor_Newtype_a0;
                  DAST._IType _1109_b = _1108___mcc_h479;
                  {
                    if (object.Equals(_466_fromTpe, _1109_b)) {
                      Dafny.ISequence<Dafny.Rune> _1110_recursiveGen;
                      bool _1111_recOwned;
                      bool _1112_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1113_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out654;
                      bool _out655;
                      bool _out656;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out657;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out654, out _out655, out _out656, out _out657);
                      _1110_recursiveGen = _out654;
                      _1111_recOwned = _out655;
                      _1112_recErased = _out656;
                      _1113_recIdents = _out657;
                      Dafny.ISequence<Dafny.Rune> _1114_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out658;
                      _out658 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _1114_rhsType = _out658;
                      Dafny.ISequence<Dafny.Rune> _1115_uneraseFn;
                      _1115_uneraseFn = ((_1111_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1114_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1115_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1110_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1111_recOwned;
                      isErased = false;
                      readIdents = _1113_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out659;
                      bool _out660;
                      bool _out661;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out662;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1109_b), _1109_b, _465_toTpe), @params, mustOwn, out _out659, out _out660, out _out661, out _out662);
                      s = _out659;
                      isOwned = _out660;
                      isErased = _out661;
                      readIdents = _out662;
                    }
                  }
                }
              } else if (_source44.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1116___mcc_h481 = _source44.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1117_recursiveGen;
                  bool _1118_recOwned;
                  bool _1119_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1120_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out663;
                  bool _out664;
                  bool _out665;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out666;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out663, out _out664, out _out665, out _out666);
                  _1117_recursiveGen = _out663;
                  _1118_recOwned = _out664;
                  _1119_recErased = _out665;
                  _1120_recIdents = _out666;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1117_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1118_recOwned;
                  isErased = _1119_recErased;
                  readIdents = _1120_recIdents;
                }
              } else if (_source44.is_Array) {
                DAST._IType _1121___mcc_h483 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1122_recursiveGen;
                  bool _1123_recOwned;
                  bool _1124_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1125_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out667;
                  bool _out668;
                  bool _out669;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out670;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out667, out _out668, out _out669, out _out670);
                  _1122_recursiveGen = _out667;
                  _1123_recOwned = _out668;
                  _1124_recErased = _out669;
                  _1125_recIdents = _out670;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1122_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1123_recOwned;
                  isErased = _1124_recErased;
                  readIdents = _1125_recIdents;
                }
              } else if (_source44.is_Seq) {
                DAST._IType _1126___mcc_h485 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1127_recursiveGen;
                  bool _1128_recOwned;
                  bool _1129_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1130_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out671;
                  bool _out672;
                  bool _out673;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out674;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out671, out _out672, out _out673, out _out674);
                  _1127_recursiveGen = _out671;
                  _1128_recOwned = _out672;
                  _1129_recErased = _out673;
                  _1130_recIdents = _out674;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1127_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1128_recOwned;
                  isErased = _1129_recErased;
                  readIdents = _1130_recIdents;
                }
              } else if (_source44.is_Set) {
                DAST._IType _1131___mcc_h487 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1132_recursiveGen;
                  bool _1133_recOwned;
                  bool _1134_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1135_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out675;
                  bool _out676;
                  bool _out677;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out678;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out675, out _out676, out _out677, out _out678);
                  _1132_recursiveGen = _out675;
                  _1133_recOwned = _out676;
                  _1134_recErased = _out677;
                  _1135_recIdents = _out678;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1132_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1133_recOwned;
                  isErased = _1134_recErased;
                  readIdents = _1135_recIdents;
                }
              } else if (_source44.is_Multiset) {
                DAST._IType _1136___mcc_h489 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1137_recursiveGen;
                  bool _1138_recOwned;
                  bool _1139_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1140_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out679;
                  bool _out680;
                  bool _out681;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out679, out _out680, out _out681, out _out682);
                  _1137_recursiveGen = _out679;
                  _1138_recOwned = _out680;
                  _1139_recErased = _out681;
                  _1140_recIdents = _out682;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1137_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1138_recOwned;
                  isErased = _1139_recErased;
                  readIdents = _1140_recIdents;
                }
              } else if (_source44.is_Map) {
                DAST._IType _1141___mcc_h491 = _source44.dtor_key;
                DAST._IType _1142___mcc_h492 = _source44.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1143_recursiveGen;
                  bool _1144_recOwned;
                  bool _1145_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1146_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out683;
                  bool _out684;
                  bool _out685;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out686;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out683, out _out684, out _out685, out _out686);
                  _1143_recursiveGen = _out683;
                  _1144_recOwned = _out684;
                  _1145_recErased = _out685;
                  _1146_recIdents = _out686;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1143_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1144_recOwned;
                  isErased = _1145_recErased;
                  readIdents = _1146_recIdents;
                }
              } else if (_source44.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1147___mcc_h495 = _source44.dtor_args;
                DAST._IType _1148___mcc_h496 = _source44.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1149_recursiveGen;
                  bool _1150_recOwned;
                  bool _1151_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1152_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out687;
                  bool _out688;
                  bool _out689;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out690;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out687, out _out688, out _out689, out _out690);
                  _1149_recursiveGen = _out687;
                  _1150_recOwned = _out688;
                  _1151_recErased = _out689;
                  _1152_recIdents = _out690;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1149_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1150_recOwned;
                  isErased = _1151_recErased;
                  readIdents = _1152_recIdents;
                }
              } else if (_source44.is_Primitive) {
                DAST._IPrimitive _1153___mcc_h499 = _source44.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1154_recursiveGen;
                  bool _1155_recOwned;
                  bool _1156_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1157_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out691;
                  bool _out692;
                  bool _out693;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out694;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out691, out _out692, out _out693, out _out694);
                  _1154_recursiveGen = _out691;
                  _1155_recOwned = _out692;
                  _1156_recErased = _out693;
                  _1157_recIdents = _out694;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1154_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1155_recOwned;
                  isErased = _1156_recErased;
                  readIdents = _1157_recIdents;
                }
              } else if (_source44.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1158___mcc_h501 = _source44.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1159_recursiveGen;
                  bool _1160_recOwned;
                  bool _1161_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1162_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out695;
                  bool _out696;
                  bool _out697;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out698;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out695, out _out696, out _out697, out _out698);
                  _1159_recursiveGen = _out695;
                  _1160_recOwned = _out696;
                  _1161_recErased = _out697;
                  _1162_recIdents = _out698;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1159_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1160_recOwned;
                  isErased = _1161_recErased;
                  readIdents = _1162_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1163___mcc_h503 = _source44.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1164_recursiveGen;
                  bool _1165_recOwned;
                  bool _1166_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1167_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out699;
                  bool _out700;
                  bool _out701;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out702;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out699, out _out700, out _out701, out _out702);
                  _1164_recursiveGen = _out699;
                  _1165_recOwned = _out700;
                  _1166_recErased = _out701;
                  _1167_recIdents = _out702;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1164_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1165_recOwned;
                  isErased = _1166_recErased;
                  readIdents = _1167_recIdents;
                }
              }
            } else if (_source26.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1168___mcc_h505 = _source26.dtor_args;
              DAST._IType _1169___mcc_h506 = _source26.dtor_result;
              DAST._IType _source46 = _473___mcc_h121;
              if (_source46.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1170___mcc_h511 = _source46.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1171___mcc_h512 = _source46.dtor_typeArgs;
                DAST._IResolvedType _1172___mcc_h513 = _source46.dtor_resolved;
                DAST._IResolvedType _source47 = _1172___mcc_h513;
                if (_source47.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1173___mcc_h517 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1174_recursiveGen;
                    bool _1175_recOwned;
                    bool _1176_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1177_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out703;
                    bool _out704;
                    bool _out705;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out706;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out703, out _out704, out _out705, out _out706);
                    _1174_recursiveGen = _out703;
                    _1175_recOwned = _out704;
                    _1176_recErased = _out705;
                    _1177_recIdents = _out706;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1174_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1175_recOwned;
                    isErased = _1176_recErased;
                    readIdents = _1177_recIdents;
                  }
                } else if (_source47.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1178___mcc_h519 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1179_recursiveGen;
                    bool _1180_recOwned;
                    bool _1181_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1182_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out707;
                    bool _out708;
                    bool _out709;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out710;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out707, out _out708, out _out709, out _out710);
                    _1179_recursiveGen = _out707;
                    _1180_recOwned = _out708;
                    _1181_recErased = _out709;
                    _1182_recIdents = _out710;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1179_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1180_recOwned;
                    isErased = _1181_recErased;
                    readIdents = _1182_recIdents;
                  }
                } else {
                  DAST._IType _1183___mcc_h521 = _source47.dtor_Newtype_a0;
                  DAST._IType _1184_b = _1183___mcc_h521;
                  {
                    if (object.Equals(_466_fromTpe, _1184_b)) {
                      Dafny.ISequence<Dafny.Rune> _1185_recursiveGen;
                      bool _1186_recOwned;
                      bool _1187_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1188_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out711;
                      bool _out712;
                      bool _out713;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out714;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out711, out _out712, out _out713, out _out714);
                      _1185_recursiveGen = _out711;
                      _1186_recOwned = _out712;
                      _1187_recErased = _out713;
                      _1188_recIdents = _out714;
                      Dafny.ISequence<Dafny.Rune> _1189_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out715;
                      _out715 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _1189_rhsType = _out715;
                      Dafny.ISequence<Dafny.Rune> _1190_uneraseFn;
                      _1190_uneraseFn = ((_1186_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1189_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1190_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1185_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1186_recOwned;
                      isErased = false;
                      readIdents = _1188_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out716;
                      bool _out717;
                      bool _out718;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out719;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1184_b), _1184_b, _465_toTpe), @params, mustOwn, out _out716, out _out717, out _out718, out _out719);
                      s = _out716;
                      isOwned = _out717;
                      isErased = _out718;
                      readIdents = _out719;
                    }
                  }
                }
              } else if (_source46.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1191___mcc_h523 = _source46.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1192_recursiveGen;
                  bool _1193_recOwned;
                  bool _1194_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1195_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out720;
                  bool _out721;
                  bool _out722;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out723;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out720, out _out721, out _out722, out _out723);
                  _1192_recursiveGen = _out720;
                  _1193_recOwned = _out721;
                  _1194_recErased = _out722;
                  _1195_recIdents = _out723;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1192_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1193_recOwned;
                  isErased = _1194_recErased;
                  readIdents = _1195_recIdents;
                }
              } else if (_source46.is_Array) {
                DAST._IType _1196___mcc_h525 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1197_recursiveGen;
                  bool _1198_recOwned;
                  bool _1199_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1200_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out724;
                  bool _out725;
                  bool _out726;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out727;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out724, out _out725, out _out726, out _out727);
                  _1197_recursiveGen = _out724;
                  _1198_recOwned = _out725;
                  _1199_recErased = _out726;
                  _1200_recIdents = _out727;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1197_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1198_recOwned;
                  isErased = _1199_recErased;
                  readIdents = _1200_recIdents;
                }
              } else if (_source46.is_Seq) {
                DAST._IType _1201___mcc_h527 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1202_recursiveGen;
                  bool _1203_recOwned;
                  bool _1204_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1205_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out728;
                  bool _out729;
                  bool _out730;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out731;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out728, out _out729, out _out730, out _out731);
                  _1202_recursiveGen = _out728;
                  _1203_recOwned = _out729;
                  _1204_recErased = _out730;
                  _1205_recIdents = _out731;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1202_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1203_recOwned;
                  isErased = _1204_recErased;
                  readIdents = _1205_recIdents;
                }
              } else if (_source46.is_Set) {
                DAST._IType _1206___mcc_h529 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1207_recursiveGen;
                  bool _1208_recOwned;
                  bool _1209_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1210_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out732;
                  bool _out733;
                  bool _out734;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out735;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out732, out _out733, out _out734, out _out735);
                  _1207_recursiveGen = _out732;
                  _1208_recOwned = _out733;
                  _1209_recErased = _out734;
                  _1210_recIdents = _out735;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1207_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1208_recOwned;
                  isErased = _1209_recErased;
                  readIdents = _1210_recIdents;
                }
              } else if (_source46.is_Multiset) {
                DAST._IType _1211___mcc_h531 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1212_recursiveGen;
                  bool _1213_recOwned;
                  bool _1214_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1215_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out736;
                  bool _out737;
                  bool _out738;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out739;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out736, out _out737, out _out738, out _out739);
                  _1212_recursiveGen = _out736;
                  _1213_recOwned = _out737;
                  _1214_recErased = _out738;
                  _1215_recIdents = _out739;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1212_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1213_recOwned;
                  isErased = _1214_recErased;
                  readIdents = _1215_recIdents;
                }
              } else if (_source46.is_Map) {
                DAST._IType _1216___mcc_h533 = _source46.dtor_key;
                DAST._IType _1217___mcc_h534 = _source46.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1218_recursiveGen;
                  bool _1219_recOwned;
                  bool _1220_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1221_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out740;
                  bool _out741;
                  bool _out742;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out743;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out740, out _out741, out _out742, out _out743);
                  _1218_recursiveGen = _out740;
                  _1219_recOwned = _out741;
                  _1220_recErased = _out742;
                  _1221_recIdents = _out743;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1218_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1219_recOwned;
                  isErased = _1220_recErased;
                  readIdents = _1221_recIdents;
                }
              } else if (_source46.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1222___mcc_h537 = _source46.dtor_args;
                DAST._IType _1223___mcc_h538 = _source46.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1224_recursiveGen;
                  bool _1225_recOwned;
                  bool _1226_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1227_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out744;
                  bool _out745;
                  bool _out746;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out747;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out744, out _out745, out _out746, out _out747);
                  _1224_recursiveGen = _out744;
                  _1225_recOwned = _out745;
                  _1226_recErased = _out746;
                  _1227_recIdents = _out747;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1224_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1225_recOwned;
                  isErased = _1226_recErased;
                  readIdents = _1227_recIdents;
                }
              } else if (_source46.is_Primitive) {
                DAST._IPrimitive _1228___mcc_h541 = _source46.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1229_recursiveGen;
                  bool _1230_recOwned;
                  bool _1231_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1232_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out748;
                  bool _out749;
                  bool _out750;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out751;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out748, out _out749, out _out750, out _out751);
                  _1229_recursiveGen = _out748;
                  _1230_recOwned = _out749;
                  _1231_recErased = _out750;
                  _1232_recIdents = _out751;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1229_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1230_recOwned;
                  isErased = _1231_recErased;
                  readIdents = _1232_recIdents;
                }
              } else if (_source46.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1233___mcc_h543 = _source46.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1234_recursiveGen;
                  bool _1235_recOwned;
                  bool _1236_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1237_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out752;
                  bool _out753;
                  bool _out754;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out755;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out752, out _out753, out _out754, out _out755);
                  _1234_recursiveGen = _out752;
                  _1235_recOwned = _out753;
                  _1236_recErased = _out754;
                  _1237_recIdents = _out755;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1234_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1235_recOwned;
                  isErased = _1236_recErased;
                  readIdents = _1237_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1238___mcc_h545 = _source46.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1239_recursiveGen;
                  bool _1240_recOwned;
                  bool _1241_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1242_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out756;
                  bool _out757;
                  bool _out758;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out759;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out756, out _out757, out _out758, out _out759);
                  _1239_recursiveGen = _out756;
                  _1240_recOwned = _out757;
                  _1241_recErased = _out758;
                  _1242_recIdents = _out759;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1239_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1240_recOwned;
                  isErased = _1241_recErased;
                  readIdents = _1242_recIdents;
                }
              }
            } else if (_source26.is_Primitive) {
              DAST._IPrimitive _1243___mcc_h547 = _source26.dtor_Primitive_a0;
              DAST._IPrimitive _source48 = _1243___mcc_h547;
              if (_source48.is_Int) {
                DAST._IType _source49 = _473___mcc_h121;
                if (_source49.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1244___mcc_h550 = _source49.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1245___mcc_h551 = _source49.dtor_typeArgs;
                  DAST._IResolvedType _1246___mcc_h552 = _source49.dtor_resolved;
                  DAST._IResolvedType _source50 = _1246___mcc_h552;
                  if (_source50.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1247___mcc_h556 = _source50.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1248_recursiveGen;
                      bool _1249_recOwned;
                      bool _1250_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1251_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out760;
                      bool _out761;
                      bool _out762;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out763;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out760, out _out761, out _out762, out _out763);
                      _1248_recursiveGen = _out760;
                      _1249_recOwned = _out761;
                      _1250_recErased = _out762;
                      _1251_recIdents = _out763;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1248_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1249_recOwned;
                      isErased = _1250_recErased;
                      readIdents = _1251_recIdents;
                    }
                  } else if (_source50.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1252___mcc_h558 = _source50.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1253_recursiveGen;
                      bool _1254_recOwned;
                      bool _1255_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1256_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out764;
                      bool _out765;
                      bool _out766;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out767;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out764, out _out765, out _out766, out _out767);
                      _1253_recursiveGen = _out764;
                      _1254_recOwned = _out765;
                      _1255_recErased = _out766;
                      _1256_recIdents = _out767;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1253_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1254_recOwned;
                      isErased = _1255_recErased;
                      readIdents = _1256_recIdents;
                    }
                  } else {
                    DAST._IType _1257___mcc_h560 = _source50.dtor_Newtype_a0;
                    DAST._IType _1258_b = _1257___mcc_h560;
                    {
                      if (object.Equals(_466_fromTpe, _1258_b)) {
                        Dafny.ISequence<Dafny.Rune> _1259_recursiveGen;
                        bool _1260_recOwned;
                        bool _1261_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1262_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out768;
                        bool _out769;
                        bool _out770;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out771;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out768, out _out769, out _out770, out _out771);
                        _1259_recursiveGen = _out768;
                        _1260_recOwned = _out769;
                        _1261_recErased = _out770;
                        _1262_recIdents = _out771;
                        Dafny.ISequence<Dafny.Rune> _1263_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out772;
                        _out772 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _1263_rhsType = _out772;
                        Dafny.ISequence<Dafny.Rune> _1264_uneraseFn;
                        _1264_uneraseFn = ((_1260_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1263_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1264_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1259_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1260_recOwned;
                        isErased = false;
                        readIdents = _1262_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out773;
                        bool _out774;
                        bool _out775;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out776;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1258_b), _1258_b, _465_toTpe), @params, mustOwn, out _out773, out _out774, out _out775, out _out776);
                        s = _out773;
                        isOwned = _out774;
                        isErased = _out775;
                        readIdents = _out776;
                      }
                    }
                  }
                } else if (_source49.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1265___mcc_h562 = _source49.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1266_recursiveGen;
                    bool _1267_recOwned;
                    bool _1268_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1269_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out777;
                    bool _out778;
                    bool _out779;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out780;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out777, out _out778, out _out779, out _out780);
                    _1266_recursiveGen = _out777;
                    _1267_recOwned = _out778;
                    _1268_recErased = _out779;
                    _1269_recIdents = _out780;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1266_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1267_recOwned;
                    isErased = _1268_recErased;
                    readIdents = _1269_recIdents;
                  }
                } else if (_source49.is_Array) {
                  DAST._IType _1270___mcc_h564 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1271_recursiveGen;
                    bool _1272_recOwned;
                    bool _1273_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1274_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out781;
                    bool _out782;
                    bool _out783;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out784;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out781, out _out782, out _out783, out _out784);
                    _1271_recursiveGen = _out781;
                    _1272_recOwned = _out782;
                    _1273_recErased = _out783;
                    _1274_recIdents = _out784;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1271_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1272_recOwned;
                    isErased = _1273_recErased;
                    readIdents = _1274_recIdents;
                  }
                } else if (_source49.is_Seq) {
                  DAST._IType _1275___mcc_h566 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1276_recursiveGen;
                    bool _1277_recOwned;
                    bool _1278_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1279_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out785;
                    bool _out786;
                    bool _out787;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out788;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out785, out _out786, out _out787, out _out788);
                    _1276_recursiveGen = _out785;
                    _1277_recOwned = _out786;
                    _1278_recErased = _out787;
                    _1279_recIdents = _out788;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1276_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1277_recOwned;
                    isErased = _1278_recErased;
                    readIdents = _1279_recIdents;
                  }
                } else if (_source49.is_Set) {
                  DAST._IType _1280___mcc_h568 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1281_recursiveGen;
                    bool _1282_recOwned;
                    bool _1283_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1284_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out789;
                    bool _out790;
                    bool _out791;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out792;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out789, out _out790, out _out791, out _out792);
                    _1281_recursiveGen = _out789;
                    _1282_recOwned = _out790;
                    _1283_recErased = _out791;
                    _1284_recIdents = _out792;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1281_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1282_recOwned;
                    isErased = _1283_recErased;
                    readIdents = _1284_recIdents;
                  }
                } else if (_source49.is_Multiset) {
                  DAST._IType _1285___mcc_h570 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1286_recursiveGen;
                    bool _1287_recOwned;
                    bool _1288_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1289_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out793;
                    bool _out794;
                    bool _out795;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out796;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out793, out _out794, out _out795, out _out796);
                    _1286_recursiveGen = _out793;
                    _1287_recOwned = _out794;
                    _1288_recErased = _out795;
                    _1289_recIdents = _out796;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1286_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1287_recOwned;
                    isErased = _1288_recErased;
                    readIdents = _1289_recIdents;
                  }
                } else if (_source49.is_Map) {
                  DAST._IType _1290___mcc_h572 = _source49.dtor_key;
                  DAST._IType _1291___mcc_h573 = _source49.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1292_recursiveGen;
                    bool _1293_recOwned;
                    bool _1294_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1295_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out797;
                    bool _out798;
                    bool _out799;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out800;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out797, out _out798, out _out799, out _out800);
                    _1292_recursiveGen = _out797;
                    _1293_recOwned = _out798;
                    _1294_recErased = _out799;
                    _1295_recIdents = _out800;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1292_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1293_recOwned;
                    isErased = _1294_recErased;
                    readIdents = _1295_recIdents;
                  }
                } else if (_source49.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1296___mcc_h576 = _source49.dtor_args;
                  DAST._IType _1297___mcc_h577 = _source49.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1298_recursiveGen;
                    bool _1299_recOwned;
                    bool _1300_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1301_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out801;
                    bool _out802;
                    bool _out803;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out804;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out801, out _out802, out _out803, out _out804);
                    _1298_recursiveGen = _out801;
                    _1299_recOwned = _out802;
                    _1300_recErased = _out803;
                    _1301_recIdents = _out804;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1298_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1299_recOwned;
                    isErased = _1300_recErased;
                    readIdents = _1301_recIdents;
                  }
                } else if (_source49.is_Primitive) {
                  DAST._IPrimitive _1302___mcc_h580 = _source49.dtor_Primitive_a0;
                  DAST._IPrimitive _source51 = _1302___mcc_h580;
                  if (_source51.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1303_recursiveGen;
                      bool _1304_recOwned;
                      bool _1305_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1306_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out805;
                      bool _out806;
                      bool _out807;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out808;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out805, out _out806, out _out807, out _out808);
                      _1303_recursiveGen = _out805;
                      _1304_recOwned = _out806;
                      _1305_recErased = _out807;
                      _1306_recIdents = _out808;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1303_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1304_recOwned;
                      isErased = _1305_recErased;
                      readIdents = _1306_recIdents;
                    }
                  } else if (_source51.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1307_recursiveGen;
                      bool _1308___v39;
                      bool _1309___v40;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1310_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out809;
                      bool _out810;
                      bool _out811;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out812;
                      DCOMP.COMP.GenExpr(_467_expr, @params, true, out _out809, out _out810, out _out811, out _out812);
                      _1307_recursiveGen = _out809;
                      _1308___v39 = _out810;
                      _1309___v40 = _out811;
                      _1310_recIdents = _out812;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1307_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1310_recIdents;
                    }
                  } else if (_source51.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1311_recursiveGen;
                      bool _1312_recOwned;
                      bool _1313_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1314_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out813;
                      bool _out814;
                      bool _out815;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out816;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out813, out _out814, out _out815, out _out816);
                      _1311_recursiveGen = _out813;
                      _1312_recOwned = _out814;
                      _1313_recErased = _out815;
                      _1314_recIdents = _out816;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1311_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1312_recOwned;
                      isErased = _1313_recErased;
                      readIdents = _1314_recIdents;
                    }
                  } else if (_source51.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1315_recursiveGen;
                      bool _1316_recOwned;
                      bool _1317_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1318_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out817;
                      bool _out818;
                      bool _out819;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out820;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out817, out _out818, out _out819, out _out820);
                      _1315_recursiveGen = _out817;
                      _1316_recOwned = _out818;
                      _1317_recErased = _out819;
                      _1318_recIdents = _out820;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1315_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1316_recOwned;
                      isErased = _1317_recErased;
                      readIdents = _1318_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1319_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out821;
                      _out821 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _1319_rhsType = _out821;
                      Dafny.ISequence<Dafny.Rune> _1320_recursiveGen;
                      bool _1321___v49;
                      bool _1322___v50;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1323_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out822;
                      bool _out823;
                      bool _out824;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out825;
                      DCOMP.COMP.GenExpr(_467_expr, @params, true, out _out822, out _out823, out _out824, out _out825);
                      _1320_recursiveGen = _out822;
                      _1321___v49 = _out823;
                      _1322___v50 = _out824;
                      _1323_recIdents = _out825;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1320_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1323_recIdents;
                    }
                  }
                } else if (_source49.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1324___mcc_h582 = _source49.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1325_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out826;
                    _out826 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                    _1325_rhsType = _out826;
                    Dafny.ISequence<Dafny.Rune> _1326_recursiveGen;
                    bool _1327___v44;
                    bool _1328___v45;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1329_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out827;
                    bool _out828;
                    bool _out829;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out830;
                    DCOMP.COMP.GenExpr(_467_expr, @params, true, out _out827, out _out828, out _out829, out _out830);
                    _1326_recursiveGen = _out827;
                    _1327___v44 = _out828;
                    _1328___v45 = _out829;
                    _1329_recIdents = _out830;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1325_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1326_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1329_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1330___mcc_h584 = _source49.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1331_recursiveGen;
                    bool _1332_recOwned;
                    bool _1333_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1334_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out831;
                    bool _out832;
                    bool _out833;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out834;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out831, out _out832, out _out833, out _out834);
                    _1331_recursiveGen = _out831;
                    _1332_recOwned = _out832;
                    _1333_recErased = _out833;
                    _1334_recIdents = _out834;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1331_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1332_recOwned;
                    isErased = _1333_recErased;
                    readIdents = _1334_recIdents;
                  }
                }
              } else if (_source48.is_Real) {
                DAST._IType _source52 = _473___mcc_h121;
                if (_source52.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1335___mcc_h586 = _source52.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1336___mcc_h587 = _source52.dtor_typeArgs;
                  DAST._IResolvedType _1337___mcc_h588 = _source52.dtor_resolved;
                  DAST._IResolvedType _source53 = _1337___mcc_h588;
                  if (_source53.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1338___mcc_h592 = _source53.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1339_recursiveGen;
                      bool _1340_recOwned;
                      bool _1341_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1342_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out835;
                      bool _out836;
                      bool _out837;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out835, out _out836, out _out837, out _out838);
                      _1339_recursiveGen = _out835;
                      _1340_recOwned = _out836;
                      _1341_recErased = _out837;
                      _1342_recIdents = _out838;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1339_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1340_recOwned;
                      isErased = _1341_recErased;
                      readIdents = _1342_recIdents;
                    }
                  } else if (_source53.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1343___mcc_h594 = _source53.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1344_recursiveGen;
                      bool _1345_recOwned;
                      bool _1346_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1347_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out839;
                      bool _out840;
                      bool _out841;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out842;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out839, out _out840, out _out841, out _out842);
                      _1344_recursiveGen = _out839;
                      _1345_recOwned = _out840;
                      _1346_recErased = _out841;
                      _1347_recIdents = _out842;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1344_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1345_recOwned;
                      isErased = _1346_recErased;
                      readIdents = _1347_recIdents;
                    }
                  } else {
                    DAST._IType _1348___mcc_h596 = _source53.dtor_Newtype_a0;
                    DAST._IType _1349_b = _1348___mcc_h596;
                    {
                      if (object.Equals(_466_fromTpe, _1349_b)) {
                        Dafny.ISequence<Dafny.Rune> _1350_recursiveGen;
                        bool _1351_recOwned;
                        bool _1352_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1353_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out843;
                        bool _out844;
                        bool _out845;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out846;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out843, out _out844, out _out845, out _out846);
                        _1350_recursiveGen = _out843;
                        _1351_recOwned = _out844;
                        _1352_recErased = _out845;
                        _1353_recIdents = _out846;
                        Dafny.ISequence<Dafny.Rune> _1354_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out847;
                        _out847 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _1354_rhsType = _out847;
                        Dafny.ISequence<Dafny.Rune> _1355_uneraseFn;
                        _1355_uneraseFn = ((_1351_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1354_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1355_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1350_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1351_recOwned;
                        isErased = false;
                        readIdents = _1353_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out848;
                        bool _out849;
                        bool _out850;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out851;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1349_b), _1349_b, _465_toTpe), @params, mustOwn, out _out848, out _out849, out _out850, out _out851);
                        s = _out848;
                        isOwned = _out849;
                        isErased = _out850;
                        readIdents = _out851;
                      }
                    }
                  }
                } else if (_source52.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1356___mcc_h598 = _source52.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1357_recursiveGen;
                    bool _1358_recOwned;
                    bool _1359_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1360_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out852;
                    bool _out853;
                    bool _out854;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out855;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out852, out _out853, out _out854, out _out855);
                    _1357_recursiveGen = _out852;
                    _1358_recOwned = _out853;
                    _1359_recErased = _out854;
                    _1360_recIdents = _out855;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1357_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1358_recOwned;
                    isErased = _1359_recErased;
                    readIdents = _1360_recIdents;
                  }
                } else if (_source52.is_Array) {
                  DAST._IType _1361___mcc_h600 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1362_recursiveGen;
                    bool _1363_recOwned;
                    bool _1364_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1365_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out856;
                    bool _out857;
                    bool _out858;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out859;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out856, out _out857, out _out858, out _out859);
                    _1362_recursiveGen = _out856;
                    _1363_recOwned = _out857;
                    _1364_recErased = _out858;
                    _1365_recIdents = _out859;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1362_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1363_recOwned;
                    isErased = _1364_recErased;
                    readIdents = _1365_recIdents;
                  }
                } else if (_source52.is_Seq) {
                  DAST._IType _1366___mcc_h602 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1367_recursiveGen;
                    bool _1368_recOwned;
                    bool _1369_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1370_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out860;
                    bool _out861;
                    bool _out862;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out863;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out860, out _out861, out _out862, out _out863);
                    _1367_recursiveGen = _out860;
                    _1368_recOwned = _out861;
                    _1369_recErased = _out862;
                    _1370_recIdents = _out863;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1367_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1368_recOwned;
                    isErased = _1369_recErased;
                    readIdents = _1370_recIdents;
                  }
                } else if (_source52.is_Set) {
                  DAST._IType _1371___mcc_h604 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1372_recursiveGen;
                    bool _1373_recOwned;
                    bool _1374_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1375_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out864;
                    bool _out865;
                    bool _out866;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out867;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out864, out _out865, out _out866, out _out867);
                    _1372_recursiveGen = _out864;
                    _1373_recOwned = _out865;
                    _1374_recErased = _out866;
                    _1375_recIdents = _out867;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1372_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1373_recOwned;
                    isErased = _1374_recErased;
                    readIdents = _1375_recIdents;
                  }
                } else if (_source52.is_Multiset) {
                  DAST._IType _1376___mcc_h606 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1377_recursiveGen;
                    bool _1378_recOwned;
                    bool _1379_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1380_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out868;
                    bool _out869;
                    bool _out870;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out871;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out868, out _out869, out _out870, out _out871);
                    _1377_recursiveGen = _out868;
                    _1378_recOwned = _out869;
                    _1379_recErased = _out870;
                    _1380_recIdents = _out871;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1377_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1378_recOwned;
                    isErased = _1379_recErased;
                    readIdents = _1380_recIdents;
                  }
                } else if (_source52.is_Map) {
                  DAST._IType _1381___mcc_h608 = _source52.dtor_key;
                  DAST._IType _1382___mcc_h609 = _source52.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1383_recursiveGen;
                    bool _1384_recOwned;
                    bool _1385_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1386_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out872;
                    bool _out873;
                    bool _out874;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out875;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out872, out _out873, out _out874, out _out875);
                    _1383_recursiveGen = _out872;
                    _1384_recOwned = _out873;
                    _1385_recErased = _out874;
                    _1386_recIdents = _out875;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1383_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1384_recOwned;
                    isErased = _1385_recErased;
                    readIdents = _1386_recIdents;
                  }
                } else if (_source52.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1387___mcc_h612 = _source52.dtor_args;
                  DAST._IType _1388___mcc_h613 = _source52.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1389_recursiveGen;
                    bool _1390_recOwned;
                    bool _1391_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1392_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out876;
                    bool _out877;
                    bool _out878;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out879;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out876, out _out877, out _out878, out _out879);
                    _1389_recursiveGen = _out876;
                    _1390_recOwned = _out877;
                    _1391_recErased = _out878;
                    _1392_recIdents = _out879;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1389_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1390_recOwned;
                    isErased = _1391_recErased;
                    readIdents = _1392_recIdents;
                  }
                } else if (_source52.is_Primitive) {
                  DAST._IPrimitive _1393___mcc_h616 = _source52.dtor_Primitive_a0;
                  DAST._IPrimitive _source54 = _1393___mcc_h616;
                  if (_source54.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1394_recursiveGen;
                      bool _1395___v41;
                      bool _1396___v42;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1397_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out880;
                      bool _out881;
                      bool _out882;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                      DCOMP.COMP.GenExpr(_467_expr, @params, false, out _out880, out _out881, out _out882, out _out883);
                      _1394_recursiveGen = _out880;
                      _1395___v41 = _out881;
                      _1396___v42 = _out882;
                      _1397_recIdents = _out883;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1394_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1397_recIdents;
                    }
                  } else if (_source54.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1398_recursiveGen;
                      bool _1399_recOwned;
                      bool _1400_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1401_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out884;
                      bool _out885;
                      bool _out886;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out887;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out884, out _out885, out _out886, out _out887);
                      _1398_recursiveGen = _out884;
                      _1399_recOwned = _out885;
                      _1400_recErased = _out886;
                      _1401_recIdents = _out887;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1398_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1399_recOwned;
                      isErased = _1400_recErased;
                      readIdents = _1401_recIdents;
                    }
                  } else if (_source54.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1402_recursiveGen;
                      bool _1403_recOwned;
                      bool _1404_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1405_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out888;
                      bool _out889;
                      bool _out890;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out891;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out888, out _out889, out _out890, out _out891);
                      _1402_recursiveGen = _out888;
                      _1403_recOwned = _out889;
                      _1404_recErased = _out890;
                      _1405_recIdents = _out891;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1402_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1403_recOwned;
                      isErased = _1404_recErased;
                      readIdents = _1405_recIdents;
                    }
                  } else if (_source54.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1406_recursiveGen;
                      bool _1407_recOwned;
                      bool _1408_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1409_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out892;
                      bool _out893;
                      bool _out894;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out892, out _out893, out _out894, out _out895);
                      _1406_recursiveGen = _out892;
                      _1407_recOwned = _out893;
                      _1408_recErased = _out894;
                      _1409_recIdents = _out895;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1406_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1407_recOwned;
                      isErased = _1408_recErased;
                      readIdents = _1409_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1410_recursiveGen;
                      bool _1411_recOwned;
                      bool _1412_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1413_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out896;
                      bool _out897;
                      bool _out898;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out899;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out896, out _out897, out _out898, out _out899);
                      _1410_recursiveGen = _out896;
                      _1411_recOwned = _out897;
                      _1412_recErased = _out898;
                      _1413_recIdents = _out899;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1410_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1411_recOwned;
                      isErased = _1412_recErased;
                      readIdents = _1413_recIdents;
                    }
                  }
                } else if (_source52.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1414___mcc_h618 = _source52.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1415_recursiveGen;
                    bool _1416_recOwned;
                    bool _1417_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1418_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out900;
                    bool _out901;
                    bool _out902;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out903;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out900, out _out901, out _out902, out _out903);
                    _1415_recursiveGen = _out900;
                    _1416_recOwned = _out901;
                    _1417_recErased = _out902;
                    _1418_recIdents = _out903;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1415_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1416_recOwned;
                    isErased = _1417_recErased;
                    readIdents = _1418_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1419___mcc_h620 = _source52.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1420_recursiveGen;
                    bool _1421_recOwned;
                    bool _1422_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1423_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out904;
                    bool _out905;
                    bool _out906;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out904, out _out905, out _out906, out _out907);
                    _1420_recursiveGen = _out904;
                    _1421_recOwned = _out905;
                    _1422_recErased = _out906;
                    _1423_recIdents = _out907;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1420_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1421_recOwned;
                    isErased = _1422_recErased;
                    readIdents = _1423_recIdents;
                  }
                }
              } else if (_source48.is_String) {
                DAST._IType _source55 = _473___mcc_h121;
                if (_source55.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1424___mcc_h622 = _source55.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1425___mcc_h623 = _source55.dtor_typeArgs;
                  DAST._IResolvedType _1426___mcc_h624 = _source55.dtor_resolved;
                  DAST._IResolvedType _source56 = _1426___mcc_h624;
                  if (_source56.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1427___mcc_h628 = _source56.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1428_recursiveGen;
                      bool _1429_recOwned;
                      bool _1430_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1431_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out908;
                      bool _out909;
                      bool _out910;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out911;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out908, out _out909, out _out910, out _out911);
                      _1428_recursiveGen = _out908;
                      _1429_recOwned = _out909;
                      _1430_recErased = _out910;
                      _1431_recIdents = _out911;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1428_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1429_recOwned;
                      isErased = _1430_recErased;
                      readIdents = _1431_recIdents;
                    }
                  } else if (_source56.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1432___mcc_h630 = _source56.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1433_recursiveGen;
                      bool _1434_recOwned;
                      bool _1435_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1436_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out912;
                      bool _out913;
                      bool _out914;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out915;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out912, out _out913, out _out914, out _out915);
                      _1433_recursiveGen = _out912;
                      _1434_recOwned = _out913;
                      _1435_recErased = _out914;
                      _1436_recIdents = _out915;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1433_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1434_recOwned;
                      isErased = _1435_recErased;
                      readIdents = _1436_recIdents;
                    }
                  } else {
                    DAST._IType _1437___mcc_h632 = _source56.dtor_Newtype_a0;
                    DAST._IType _1438_b = _1437___mcc_h632;
                    {
                      if (object.Equals(_466_fromTpe, _1438_b)) {
                        Dafny.ISequence<Dafny.Rune> _1439_recursiveGen;
                        bool _1440_recOwned;
                        bool _1441_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1442_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out916;
                        bool _out917;
                        bool _out918;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out916, out _out917, out _out918, out _out919);
                        _1439_recursiveGen = _out916;
                        _1440_recOwned = _out917;
                        _1441_recErased = _out918;
                        _1442_recIdents = _out919;
                        Dafny.ISequence<Dafny.Rune> _1443_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out920;
                        _out920 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _1443_rhsType = _out920;
                        Dafny.ISequence<Dafny.Rune> _1444_uneraseFn;
                        _1444_uneraseFn = ((_1440_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1443_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1444_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1439_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1440_recOwned;
                        isErased = false;
                        readIdents = _1442_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out921;
                        bool _out922;
                        bool _out923;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out924;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1438_b), _1438_b, _465_toTpe), @params, mustOwn, out _out921, out _out922, out _out923, out _out924);
                        s = _out921;
                        isOwned = _out922;
                        isErased = _out923;
                        readIdents = _out924;
                      }
                    }
                  }
                } else if (_source55.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1445___mcc_h634 = _source55.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1446_recursiveGen;
                    bool _1447_recOwned;
                    bool _1448_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1449_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out925;
                    bool _out926;
                    bool _out927;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out928;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out925, out _out926, out _out927, out _out928);
                    _1446_recursiveGen = _out925;
                    _1447_recOwned = _out926;
                    _1448_recErased = _out927;
                    _1449_recIdents = _out928;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1446_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1447_recOwned;
                    isErased = _1448_recErased;
                    readIdents = _1449_recIdents;
                  }
                } else if (_source55.is_Array) {
                  DAST._IType _1450___mcc_h636 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1451_recursiveGen;
                    bool _1452_recOwned;
                    bool _1453_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1454_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out929;
                    bool _out930;
                    bool _out931;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out932;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out929, out _out930, out _out931, out _out932);
                    _1451_recursiveGen = _out929;
                    _1452_recOwned = _out930;
                    _1453_recErased = _out931;
                    _1454_recIdents = _out932;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1451_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1452_recOwned;
                    isErased = _1453_recErased;
                    readIdents = _1454_recIdents;
                  }
                } else if (_source55.is_Seq) {
                  DAST._IType _1455___mcc_h638 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1456_recursiveGen;
                    bool _1457_recOwned;
                    bool _1458_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1459_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out933;
                    bool _out934;
                    bool _out935;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out933, out _out934, out _out935, out _out936);
                    _1456_recursiveGen = _out933;
                    _1457_recOwned = _out934;
                    _1458_recErased = _out935;
                    _1459_recIdents = _out936;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1456_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1457_recOwned;
                    isErased = _1458_recErased;
                    readIdents = _1459_recIdents;
                  }
                } else if (_source55.is_Set) {
                  DAST._IType _1460___mcc_h640 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1461_recursiveGen;
                    bool _1462_recOwned;
                    bool _1463_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1464_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out937;
                    bool _out938;
                    bool _out939;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out940;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out937, out _out938, out _out939, out _out940);
                    _1461_recursiveGen = _out937;
                    _1462_recOwned = _out938;
                    _1463_recErased = _out939;
                    _1464_recIdents = _out940;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1461_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1462_recOwned;
                    isErased = _1463_recErased;
                    readIdents = _1464_recIdents;
                  }
                } else if (_source55.is_Multiset) {
                  DAST._IType _1465___mcc_h642 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1466_recursiveGen;
                    bool _1467_recOwned;
                    bool _1468_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out941;
                    bool _out942;
                    bool _out943;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out944;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out941, out _out942, out _out943, out _out944);
                    _1466_recursiveGen = _out941;
                    _1467_recOwned = _out942;
                    _1468_recErased = _out943;
                    _1469_recIdents = _out944;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1466_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1467_recOwned;
                    isErased = _1468_recErased;
                    readIdents = _1469_recIdents;
                  }
                } else if (_source55.is_Map) {
                  DAST._IType _1470___mcc_h644 = _source55.dtor_key;
                  DAST._IType _1471___mcc_h645 = _source55.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1472_recursiveGen;
                    bool _1473_recOwned;
                    bool _1474_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1475_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out945;
                    bool _out946;
                    bool _out947;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out948;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out945, out _out946, out _out947, out _out948);
                    _1472_recursiveGen = _out945;
                    _1473_recOwned = _out946;
                    _1474_recErased = _out947;
                    _1475_recIdents = _out948;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1472_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1473_recOwned;
                    isErased = _1474_recErased;
                    readIdents = _1475_recIdents;
                  }
                } else if (_source55.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1476___mcc_h648 = _source55.dtor_args;
                  DAST._IType _1477___mcc_h649 = _source55.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1478_recursiveGen;
                    bool _1479_recOwned;
                    bool _1480_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1481_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out949;
                    bool _out950;
                    bool _out951;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out952;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out949, out _out950, out _out951, out _out952);
                    _1478_recursiveGen = _out949;
                    _1479_recOwned = _out950;
                    _1480_recErased = _out951;
                    _1481_recIdents = _out952;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1478_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1479_recOwned;
                    isErased = _1480_recErased;
                    readIdents = _1481_recIdents;
                  }
                } else if (_source55.is_Primitive) {
                  DAST._IPrimitive _1482___mcc_h652 = _source55.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1483_recursiveGen;
                    bool _1484_recOwned;
                    bool _1485_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1486_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out953;
                    bool _out954;
                    bool _out955;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out956;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out953, out _out954, out _out955, out _out956);
                    _1483_recursiveGen = _out953;
                    _1484_recOwned = _out954;
                    _1485_recErased = _out955;
                    _1486_recIdents = _out956;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1483_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1484_recOwned;
                    isErased = _1485_recErased;
                    readIdents = _1486_recIdents;
                  }
                } else if (_source55.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1487___mcc_h654 = _source55.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1488_recursiveGen;
                    bool _1489_recOwned;
                    bool _1490_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1491_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out957;
                    bool _out958;
                    bool _out959;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out960;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out957, out _out958, out _out959, out _out960);
                    _1488_recursiveGen = _out957;
                    _1489_recOwned = _out958;
                    _1490_recErased = _out959;
                    _1491_recIdents = _out960;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1488_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1489_recOwned;
                    isErased = _1490_recErased;
                    readIdents = _1491_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1492___mcc_h656 = _source55.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1493_recursiveGen;
                    bool _1494_recOwned;
                    bool _1495_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1496_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out961;
                    bool _out962;
                    bool _out963;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out964;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out961, out _out962, out _out963, out _out964);
                    _1493_recursiveGen = _out961;
                    _1494_recOwned = _out962;
                    _1495_recErased = _out963;
                    _1496_recIdents = _out964;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1493_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1494_recOwned;
                    isErased = _1495_recErased;
                    readIdents = _1496_recIdents;
                  }
                }
              } else if (_source48.is_Bool) {
                DAST._IType _source57 = _473___mcc_h121;
                if (_source57.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1497___mcc_h658 = _source57.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1498___mcc_h659 = _source57.dtor_typeArgs;
                  DAST._IResolvedType _1499___mcc_h660 = _source57.dtor_resolved;
                  DAST._IResolvedType _source58 = _1499___mcc_h660;
                  if (_source58.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1500___mcc_h664 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1501_recursiveGen;
                      bool _1502_recOwned;
                      bool _1503_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1504_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out965;
                      bool _out966;
                      bool _out967;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out968;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out965, out _out966, out _out967, out _out968);
                      _1501_recursiveGen = _out965;
                      _1502_recOwned = _out966;
                      _1503_recErased = _out967;
                      _1504_recIdents = _out968;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1501_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1502_recOwned;
                      isErased = _1503_recErased;
                      readIdents = _1504_recIdents;
                    }
                  } else if (_source58.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1505___mcc_h666 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1506_recursiveGen;
                      bool _1507_recOwned;
                      bool _1508_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1509_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out969;
                      bool _out970;
                      bool _out971;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out972;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out969, out _out970, out _out971, out _out972);
                      _1506_recursiveGen = _out969;
                      _1507_recOwned = _out970;
                      _1508_recErased = _out971;
                      _1509_recIdents = _out972;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1506_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1507_recOwned;
                      isErased = _1508_recErased;
                      readIdents = _1509_recIdents;
                    }
                  } else {
                    DAST._IType _1510___mcc_h668 = _source58.dtor_Newtype_a0;
                    DAST._IType _1511_b = _1510___mcc_h668;
                    {
                      if (object.Equals(_466_fromTpe, _1511_b)) {
                        Dafny.ISequence<Dafny.Rune> _1512_recursiveGen;
                        bool _1513_recOwned;
                        bool _1514_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1515_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out973;
                        bool _out974;
                        bool _out975;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out976;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out973, out _out974, out _out975, out _out976);
                        _1512_recursiveGen = _out973;
                        _1513_recOwned = _out974;
                        _1514_recErased = _out975;
                        _1515_recIdents = _out976;
                        Dafny.ISequence<Dafny.Rune> _1516_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out977;
                        _out977 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _1516_rhsType = _out977;
                        Dafny.ISequence<Dafny.Rune> _1517_uneraseFn;
                        _1517_uneraseFn = ((_1513_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1516_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1517_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1512_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1513_recOwned;
                        isErased = false;
                        readIdents = _1515_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out978;
                        bool _out979;
                        bool _out980;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out981;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1511_b), _1511_b, _465_toTpe), @params, mustOwn, out _out978, out _out979, out _out980, out _out981);
                        s = _out978;
                        isOwned = _out979;
                        isErased = _out980;
                        readIdents = _out981;
                      }
                    }
                  }
                } else if (_source57.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1518___mcc_h670 = _source57.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1519_recursiveGen;
                    bool _1520_recOwned;
                    bool _1521_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out982;
                    bool _out983;
                    bool _out984;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out985;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out982, out _out983, out _out984, out _out985);
                    _1519_recursiveGen = _out982;
                    _1520_recOwned = _out983;
                    _1521_recErased = _out984;
                    _1522_recIdents = _out985;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1519_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1520_recOwned;
                    isErased = _1521_recErased;
                    readIdents = _1522_recIdents;
                  }
                } else if (_source57.is_Array) {
                  DAST._IType _1523___mcc_h672 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1524_recursiveGen;
                    bool _1525_recOwned;
                    bool _1526_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1527_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out986;
                    bool _out987;
                    bool _out988;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out989;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out986, out _out987, out _out988, out _out989);
                    _1524_recursiveGen = _out986;
                    _1525_recOwned = _out987;
                    _1526_recErased = _out988;
                    _1527_recIdents = _out989;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1524_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1525_recOwned;
                    isErased = _1526_recErased;
                    readIdents = _1527_recIdents;
                  }
                } else if (_source57.is_Seq) {
                  DAST._IType _1528___mcc_h674 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1529_recursiveGen;
                    bool _1530_recOwned;
                    bool _1531_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1532_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out990;
                    bool _out991;
                    bool _out992;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out993;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out990, out _out991, out _out992, out _out993);
                    _1529_recursiveGen = _out990;
                    _1530_recOwned = _out991;
                    _1531_recErased = _out992;
                    _1532_recIdents = _out993;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1529_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1530_recOwned;
                    isErased = _1531_recErased;
                    readIdents = _1532_recIdents;
                  }
                } else if (_source57.is_Set) {
                  DAST._IType _1533___mcc_h676 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1534_recursiveGen;
                    bool _1535_recOwned;
                    bool _1536_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1537_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out994;
                    bool _out995;
                    bool _out996;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out997;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out994, out _out995, out _out996, out _out997);
                    _1534_recursiveGen = _out994;
                    _1535_recOwned = _out995;
                    _1536_recErased = _out996;
                    _1537_recIdents = _out997;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1534_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1535_recOwned;
                    isErased = _1536_recErased;
                    readIdents = _1537_recIdents;
                  }
                } else if (_source57.is_Multiset) {
                  DAST._IType _1538___mcc_h678 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1539_recursiveGen;
                    bool _1540_recOwned;
                    bool _1541_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1542_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out998;
                    bool _out999;
                    bool _out1000;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1001;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out998, out _out999, out _out1000, out _out1001);
                    _1539_recursiveGen = _out998;
                    _1540_recOwned = _out999;
                    _1541_recErased = _out1000;
                    _1542_recIdents = _out1001;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1539_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1540_recOwned;
                    isErased = _1541_recErased;
                    readIdents = _1542_recIdents;
                  }
                } else if (_source57.is_Map) {
                  DAST._IType _1543___mcc_h680 = _source57.dtor_key;
                  DAST._IType _1544___mcc_h681 = _source57.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1545_recursiveGen;
                    bool _1546_recOwned;
                    bool _1547_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1548_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1002;
                    bool _out1003;
                    bool _out1004;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1005;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1002, out _out1003, out _out1004, out _out1005);
                    _1545_recursiveGen = _out1002;
                    _1546_recOwned = _out1003;
                    _1547_recErased = _out1004;
                    _1548_recIdents = _out1005;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1545_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1546_recOwned;
                    isErased = _1547_recErased;
                    readIdents = _1548_recIdents;
                  }
                } else if (_source57.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1549___mcc_h684 = _source57.dtor_args;
                  DAST._IType _1550___mcc_h685 = _source57.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1551_recursiveGen;
                    bool _1552_recOwned;
                    bool _1553_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1006;
                    bool _out1007;
                    bool _out1008;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1009;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1006, out _out1007, out _out1008, out _out1009);
                    _1551_recursiveGen = _out1006;
                    _1552_recOwned = _out1007;
                    _1553_recErased = _out1008;
                    _1554_recIdents = _out1009;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1551_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1552_recOwned;
                    isErased = _1553_recErased;
                    readIdents = _1554_recIdents;
                  }
                } else if (_source57.is_Primitive) {
                  DAST._IPrimitive _1555___mcc_h688 = _source57.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1556_recursiveGen;
                    bool _1557_recOwned;
                    bool _1558_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1010;
                    bool _out1011;
                    bool _out1012;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1013;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1010, out _out1011, out _out1012, out _out1013);
                    _1556_recursiveGen = _out1010;
                    _1557_recOwned = _out1011;
                    _1558_recErased = _out1012;
                    _1559_recIdents = _out1013;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1556_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1557_recOwned;
                    isErased = _1558_recErased;
                    readIdents = _1559_recIdents;
                  }
                } else if (_source57.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1560___mcc_h690 = _source57.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1561_recursiveGen;
                    bool _1562_recOwned;
                    bool _1563_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1564_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1014;
                    bool _out1015;
                    bool _out1016;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1017;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1014, out _out1015, out _out1016, out _out1017);
                    _1561_recursiveGen = _out1014;
                    _1562_recOwned = _out1015;
                    _1563_recErased = _out1016;
                    _1564_recIdents = _out1017;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1561_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1562_recOwned;
                    isErased = _1563_recErased;
                    readIdents = _1564_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1565___mcc_h692 = _source57.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1566_recursiveGen;
                    bool _1567_recOwned;
                    bool _1568_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1018;
                    bool _out1019;
                    bool _out1020;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1021;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1018, out _out1019, out _out1020, out _out1021);
                    _1566_recursiveGen = _out1018;
                    _1567_recOwned = _out1019;
                    _1568_recErased = _out1020;
                    _1569_recIdents = _out1021;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1566_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1567_recOwned;
                    isErased = _1568_recErased;
                    readIdents = _1569_recIdents;
                  }
                }
              } else {
                DAST._IType _source59 = _473___mcc_h121;
                if (_source59.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1570___mcc_h694 = _source59.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1571___mcc_h695 = _source59.dtor_typeArgs;
                  DAST._IResolvedType _1572___mcc_h696 = _source59.dtor_resolved;
                  DAST._IResolvedType _source60 = _1572___mcc_h696;
                  if (_source60.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1573___mcc_h700 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1574_recursiveGen;
                      bool _1575_recOwned;
                      bool _1576_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1577_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1022;
                      bool _out1023;
                      bool _out1024;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1025;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1022, out _out1023, out _out1024, out _out1025);
                      _1574_recursiveGen = _out1022;
                      _1575_recOwned = _out1023;
                      _1576_recErased = _out1024;
                      _1577_recIdents = _out1025;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1575_recOwned;
                      isErased = _1576_recErased;
                      readIdents = _1577_recIdents;
                    }
                  } else if (_source60.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1578___mcc_h702 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1579_recursiveGen;
                      bool _1580_recOwned;
                      bool _1581_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1582_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1026;
                      bool _out1027;
                      bool _out1028;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1029;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1026, out _out1027, out _out1028, out _out1029);
                      _1579_recursiveGen = _out1026;
                      _1580_recOwned = _out1027;
                      _1581_recErased = _out1028;
                      _1582_recIdents = _out1029;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1579_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1580_recOwned;
                      isErased = _1581_recErased;
                      readIdents = _1582_recIdents;
                    }
                  } else {
                    DAST._IType _1583___mcc_h704 = _source60.dtor_Newtype_a0;
                    DAST._IType _1584_b = _1583___mcc_h704;
                    {
                      if (object.Equals(_466_fromTpe, _1584_b)) {
                        Dafny.ISequence<Dafny.Rune> _1585_recursiveGen;
                        bool _1586_recOwned;
                        bool _1587_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1588_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1030;
                        bool _out1031;
                        bool _out1032;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1033;
                        DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1030, out _out1031, out _out1032, out _out1033);
                        _1585_recursiveGen = _out1030;
                        _1586_recOwned = _out1031;
                        _1587_recErased = _out1032;
                        _1588_recIdents = _out1033;
                        Dafny.ISequence<Dafny.Rune> _1589_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1034;
                        _out1034 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                        _1589_rhsType = _out1034;
                        Dafny.ISequence<Dafny.Rune> _1590_uneraseFn;
                        _1590_uneraseFn = ((_1586_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1589_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1590_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1585_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1586_recOwned;
                        isErased = false;
                        readIdents = _1588_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1035;
                        bool _out1036;
                        bool _out1037;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1038;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1584_b), _1584_b, _465_toTpe), @params, mustOwn, out _out1035, out _out1036, out _out1037, out _out1038);
                        s = _out1035;
                        isOwned = _out1036;
                        isErased = _out1037;
                        readIdents = _out1038;
                      }
                    }
                  }
                } else if (_source59.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1591___mcc_h706 = _source59.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1592_recursiveGen;
                    bool _1593_recOwned;
                    bool _1594_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1595_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1039;
                    bool _out1040;
                    bool _out1041;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1042;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1039, out _out1040, out _out1041, out _out1042);
                    _1592_recursiveGen = _out1039;
                    _1593_recOwned = _out1040;
                    _1594_recErased = _out1041;
                    _1595_recIdents = _out1042;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1592_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1593_recOwned;
                    isErased = _1594_recErased;
                    readIdents = _1595_recIdents;
                  }
                } else if (_source59.is_Array) {
                  DAST._IType _1596___mcc_h708 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1597_recursiveGen;
                    bool _1598_recOwned;
                    bool _1599_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1600_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1043;
                    bool _out1044;
                    bool _out1045;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1046;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1043, out _out1044, out _out1045, out _out1046);
                    _1597_recursiveGen = _out1043;
                    _1598_recOwned = _out1044;
                    _1599_recErased = _out1045;
                    _1600_recIdents = _out1046;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1597_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1598_recOwned;
                    isErased = _1599_recErased;
                    readIdents = _1600_recIdents;
                  }
                } else if (_source59.is_Seq) {
                  DAST._IType _1601___mcc_h710 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1602_recursiveGen;
                    bool _1603_recOwned;
                    bool _1604_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1605_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1047;
                    bool _out1048;
                    bool _out1049;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1050;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1047, out _out1048, out _out1049, out _out1050);
                    _1602_recursiveGen = _out1047;
                    _1603_recOwned = _out1048;
                    _1604_recErased = _out1049;
                    _1605_recIdents = _out1050;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1602_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1603_recOwned;
                    isErased = _1604_recErased;
                    readIdents = _1605_recIdents;
                  }
                } else if (_source59.is_Set) {
                  DAST._IType _1606___mcc_h712 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1607_recursiveGen;
                    bool _1608_recOwned;
                    bool _1609_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1610_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1051;
                    bool _out1052;
                    bool _out1053;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1054;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1051, out _out1052, out _out1053, out _out1054);
                    _1607_recursiveGen = _out1051;
                    _1608_recOwned = _out1052;
                    _1609_recErased = _out1053;
                    _1610_recIdents = _out1054;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1607_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1608_recOwned;
                    isErased = _1609_recErased;
                    readIdents = _1610_recIdents;
                  }
                } else if (_source59.is_Multiset) {
                  DAST._IType _1611___mcc_h714 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1612_recursiveGen;
                    bool _1613_recOwned;
                    bool _1614_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1615_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1055;
                    bool _out1056;
                    bool _out1057;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1058;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1055, out _out1056, out _out1057, out _out1058);
                    _1612_recursiveGen = _out1055;
                    _1613_recOwned = _out1056;
                    _1614_recErased = _out1057;
                    _1615_recIdents = _out1058;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1612_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1613_recOwned;
                    isErased = _1614_recErased;
                    readIdents = _1615_recIdents;
                  }
                } else if (_source59.is_Map) {
                  DAST._IType _1616___mcc_h716 = _source59.dtor_key;
                  DAST._IType _1617___mcc_h717 = _source59.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1618_recursiveGen;
                    bool _1619_recOwned;
                    bool _1620_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1621_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1059;
                    bool _out1060;
                    bool _out1061;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1062;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1059, out _out1060, out _out1061, out _out1062);
                    _1618_recursiveGen = _out1059;
                    _1619_recOwned = _out1060;
                    _1620_recErased = _out1061;
                    _1621_recIdents = _out1062;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1618_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1619_recOwned;
                    isErased = _1620_recErased;
                    readIdents = _1621_recIdents;
                  }
                } else if (_source59.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1622___mcc_h720 = _source59.dtor_args;
                  DAST._IType _1623___mcc_h721 = _source59.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1624_recursiveGen;
                    bool _1625_recOwned;
                    bool _1626_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1627_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1063;
                    bool _out1064;
                    bool _out1065;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1066;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1063, out _out1064, out _out1065, out _out1066);
                    _1624_recursiveGen = _out1063;
                    _1625_recOwned = _out1064;
                    _1626_recErased = _out1065;
                    _1627_recIdents = _out1066;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1624_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1625_recOwned;
                    isErased = _1626_recErased;
                    readIdents = _1627_recIdents;
                  }
                } else if (_source59.is_Primitive) {
                  DAST._IPrimitive _1628___mcc_h724 = _source59.dtor_Primitive_a0;
                  DAST._IPrimitive _source61 = _1628___mcc_h724;
                  if (_source61.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1629_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1067;
                      _out1067 = DCOMP.COMP.GenType(_466_fromTpe, true, false);
                      _1629_rhsType = _out1067;
                      Dafny.ISequence<Dafny.Rune> _1630_recursiveGen;
                      bool _1631___v51;
                      bool _1632___v52;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1633_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1068;
                      bool _out1069;
                      bool _out1070;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1071;
                      DCOMP.COMP.GenExpr(_467_expr, @params, true, out _out1068, out _out1069, out _out1070, out _out1071);
                      _1630_recursiveGen = _out1068;
                      _1631___v51 = _out1069;
                      _1632___v52 = _out1070;
                      _1633_recIdents = _out1071;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1630_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1633_recIdents;
                    }
                  } else if (_source61.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1634_recursiveGen;
                      bool _1635_recOwned;
                      bool _1636_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1637_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1072;
                      bool _out1073;
                      bool _out1074;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1075;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1072, out _out1073, out _out1074, out _out1075);
                      _1634_recursiveGen = _out1072;
                      _1635_recOwned = _out1073;
                      _1636_recErased = _out1074;
                      _1637_recIdents = _out1075;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1634_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1635_recOwned;
                      isErased = _1636_recErased;
                      readIdents = _1637_recIdents;
                    }
                  } else if (_source61.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1638_recursiveGen;
                      bool _1639_recOwned;
                      bool _1640_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1641_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1076;
                      bool _out1077;
                      bool _out1078;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1076, out _out1077, out _out1078, out _out1079);
                      _1638_recursiveGen = _out1076;
                      _1639_recOwned = _out1077;
                      _1640_recErased = _out1078;
                      _1641_recIdents = _out1079;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1638_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1639_recOwned;
                      isErased = _1640_recErased;
                      readIdents = _1641_recIdents;
                    }
                  } else if (_source61.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1642_recursiveGen;
                      bool _1643_recOwned;
                      bool _1644_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1645_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1080;
                      bool _out1081;
                      bool _out1082;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1083;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1080, out _out1081, out _out1082, out _out1083);
                      _1642_recursiveGen = _out1080;
                      _1643_recOwned = _out1081;
                      _1644_recErased = _out1082;
                      _1645_recIdents = _out1083;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1642_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1643_recOwned;
                      isErased = _1644_recErased;
                      readIdents = _1645_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1646_recursiveGen;
                      bool _1647_recOwned;
                      bool _1648_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1649_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1084;
                      bool _out1085;
                      bool _out1086;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1087;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1084, out _out1085, out _out1086, out _out1087);
                      _1646_recursiveGen = _out1084;
                      _1647_recOwned = _out1085;
                      _1648_recErased = _out1086;
                      _1649_recIdents = _out1087;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1646_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1647_recOwned;
                      isErased = _1648_recErased;
                      readIdents = _1649_recIdents;
                    }
                  }
                } else if (_source59.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1650___mcc_h726 = _source59.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1651_recursiveGen;
                    bool _1652_recOwned;
                    bool _1653_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1654_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1088;
                    bool _out1089;
                    bool _out1090;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1088, out _out1089, out _out1090, out _out1091);
                    _1651_recursiveGen = _out1088;
                    _1652_recOwned = _out1089;
                    _1653_recErased = _out1090;
                    _1654_recIdents = _out1091;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1651_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1652_recOwned;
                    isErased = _1653_recErased;
                    readIdents = _1654_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1655___mcc_h728 = _source59.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1656_recursiveGen;
                    bool _1657_recOwned;
                    bool _1658_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1659_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1092;
                    bool _out1093;
                    bool _out1094;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1095;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1092, out _out1093, out _out1094, out _out1095);
                    _1656_recursiveGen = _out1092;
                    _1657_recOwned = _out1093;
                    _1658_recErased = _out1094;
                    _1659_recIdents = _out1095;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1656_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1657_recOwned;
                    isErased = _1658_recErased;
                    readIdents = _1659_recIdents;
                  }
                }
              }
            } else if (_source26.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1660___mcc_h730 = _source26.dtor_Passthrough_a0;
              DAST._IType _source62 = _473___mcc_h121;
              if (_source62.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1661___mcc_h733 = _source62.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1662___mcc_h734 = _source62.dtor_typeArgs;
                DAST._IResolvedType _1663___mcc_h735 = _source62.dtor_resolved;
                DAST._IResolvedType _source63 = _1663___mcc_h735;
                if (_source63.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1664___mcc_h739 = _source63.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1665_recursiveGen;
                    bool _1666_recOwned;
                    bool _1667_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1668_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1096;
                    bool _out1097;
                    bool _out1098;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1099;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1096, out _out1097, out _out1098, out _out1099);
                    _1665_recursiveGen = _out1096;
                    _1666_recOwned = _out1097;
                    _1667_recErased = _out1098;
                    _1668_recIdents = _out1099;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1665_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1666_recOwned;
                    isErased = _1667_recErased;
                    readIdents = _1668_recIdents;
                  }
                } else if (_source63.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1669___mcc_h741 = _source63.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1670_recursiveGen;
                    bool _1671_recOwned;
                    bool _1672_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1673_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1100;
                    bool _out1101;
                    bool _out1102;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1103;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1100, out _out1101, out _out1102, out _out1103);
                    _1670_recursiveGen = _out1100;
                    _1671_recOwned = _out1101;
                    _1672_recErased = _out1102;
                    _1673_recIdents = _out1103;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1670_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1671_recOwned;
                    isErased = _1672_recErased;
                    readIdents = _1673_recIdents;
                  }
                } else {
                  DAST._IType _1674___mcc_h743 = _source63.dtor_Newtype_a0;
                  DAST._IType _1675_b = _1674___mcc_h743;
                  {
                    if (object.Equals(_466_fromTpe, _1675_b)) {
                      Dafny.ISequence<Dafny.Rune> _1676_recursiveGen;
                      bool _1677_recOwned;
                      bool _1678_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1679_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1104;
                      bool _out1105;
                      bool _out1106;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1107;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1104, out _out1105, out _out1106, out _out1107);
                      _1676_recursiveGen = _out1104;
                      _1677_recOwned = _out1105;
                      _1678_recErased = _out1106;
                      _1679_recIdents = _out1107;
                      Dafny.ISequence<Dafny.Rune> _1680_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1108;
                      _out1108 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _1680_rhsType = _out1108;
                      Dafny.ISequence<Dafny.Rune> _1681_uneraseFn;
                      _1681_uneraseFn = ((_1677_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1680_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1681_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1676_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1677_recOwned;
                      isErased = false;
                      readIdents = _1679_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1109;
                      bool _out1110;
                      bool _out1111;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1675_b), _1675_b, _465_toTpe), @params, mustOwn, out _out1109, out _out1110, out _out1111, out _out1112);
                      s = _out1109;
                      isOwned = _out1110;
                      isErased = _out1111;
                      readIdents = _out1112;
                    }
                  }
                }
              } else if (_source62.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1682___mcc_h745 = _source62.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1683_recursiveGen;
                  bool _1684_recOwned;
                  bool _1685_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1686_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1113;
                  bool _out1114;
                  bool _out1115;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1116;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1113, out _out1114, out _out1115, out _out1116);
                  _1683_recursiveGen = _out1113;
                  _1684_recOwned = _out1114;
                  _1685_recErased = _out1115;
                  _1686_recIdents = _out1116;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1683_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1684_recOwned;
                  isErased = _1685_recErased;
                  readIdents = _1686_recIdents;
                }
              } else if (_source62.is_Array) {
                DAST._IType _1687___mcc_h747 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1688_recursiveGen;
                  bool _1689_recOwned;
                  bool _1690_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1691_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1117;
                  bool _out1118;
                  bool _out1119;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1120;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1117, out _out1118, out _out1119, out _out1120);
                  _1688_recursiveGen = _out1117;
                  _1689_recOwned = _out1118;
                  _1690_recErased = _out1119;
                  _1691_recIdents = _out1120;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1688_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1689_recOwned;
                  isErased = _1690_recErased;
                  readIdents = _1691_recIdents;
                }
              } else if (_source62.is_Seq) {
                DAST._IType _1692___mcc_h749 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1693_recursiveGen;
                  bool _1694_recOwned;
                  bool _1695_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1121;
                  bool _out1122;
                  bool _out1123;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1121, out _out1122, out _out1123, out _out1124);
                  _1693_recursiveGen = _out1121;
                  _1694_recOwned = _out1122;
                  _1695_recErased = _out1123;
                  _1696_recIdents = _out1124;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1693_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1694_recOwned;
                  isErased = _1695_recErased;
                  readIdents = _1696_recIdents;
                }
              } else if (_source62.is_Set) {
                DAST._IType _1697___mcc_h751 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1698_recursiveGen;
                  bool _1699_recOwned;
                  bool _1700_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1125;
                  bool _out1126;
                  bool _out1127;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1125, out _out1126, out _out1127, out _out1128);
                  _1698_recursiveGen = _out1125;
                  _1699_recOwned = _out1126;
                  _1700_recErased = _out1127;
                  _1701_recIdents = _out1128;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1698_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1699_recOwned;
                  isErased = _1700_recErased;
                  readIdents = _1701_recIdents;
                }
              } else if (_source62.is_Multiset) {
                DAST._IType _1702___mcc_h753 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1703_recursiveGen;
                  bool _1704_recOwned;
                  bool _1705_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1706_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1129;
                  bool _out1130;
                  bool _out1131;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1132;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1129, out _out1130, out _out1131, out _out1132);
                  _1703_recursiveGen = _out1129;
                  _1704_recOwned = _out1130;
                  _1705_recErased = _out1131;
                  _1706_recIdents = _out1132;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1703_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1704_recOwned;
                  isErased = _1705_recErased;
                  readIdents = _1706_recIdents;
                }
              } else if (_source62.is_Map) {
                DAST._IType _1707___mcc_h755 = _source62.dtor_key;
                DAST._IType _1708___mcc_h756 = _source62.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1709_recursiveGen;
                  bool _1710_recOwned;
                  bool _1711_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1133;
                  bool _out1134;
                  bool _out1135;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1133, out _out1134, out _out1135, out _out1136);
                  _1709_recursiveGen = _out1133;
                  _1710_recOwned = _out1134;
                  _1711_recErased = _out1135;
                  _1712_recIdents = _out1136;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1709_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1710_recOwned;
                  isErased = _1711_recErased;
                  readIdents = _1712_recIdents;
                }
              } else if (_source62.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1713___mcc_h759 = _source62.dtor_args;
                DAST._IType _1714___mcc_h760 = _source62.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1715_recursiveGen;
                  bool _1716_recOwned;
                  bool _1717_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1718_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1137;
                  bool _out1138;
                  bool _out1139;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1140;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1137, out _out1138, out _out1139, out _out1140);
                  _1715_recursiveGen = _out1137;
                  _1716_recOwned = _out1138;
                  _1717_recErased = _out1139;
                  _1718_recIdents = _out1140;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1715_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1716_recOwned;
                  isErased = _1717_recErased;
                  readIdents = _1718_recIdents;
                }
              } else if (_source62.is_Primitive) {
                DAST._IPrimitive _1719___mcc_h763 = _source62.dtor_Primitive_a0;
                DAST._IPrimitive _source64 = _1719___mcc_h763;
                if (_source64.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1720_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1141;
                    _out1141 = DCOMP.COMP.GenType(_466_fromTpe, true, false);
                    _1720_rhsType = _out1141;
                    Dafny.ISequence<Dafny.Rune> _1721_recursiveGen;
                    bool _1722___v47;
                    bool _1723___v48;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1142;
                    bool _out1143;
                    bool _out1144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1145;
                    DCOMP.COMP.GenExpr(_467_expr, @params, true, out _out1142, out _out1143, out _out1144, out _out1145);
                    _1721_recursiveGen = _out1142;
                    _1722___v47 = _out1143;
                    _1723___v48 = _out1144;
                    _1724_recIdents = _out1145;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1721_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1724_recIdents;
                  }
                } else if (_source64.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1725_recursiveGen;
                    bool _1726_recOwned;
                    bool _1727_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1728_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1146;
                    bool _out1147;
                    bool _out1148;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1149;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1146, out _out1147, out _out1148, out _out1149);
                    _1725_recursiveGen = _out1146;
                    _1726_recOwned = _out1147;
                    _1727_recErased = _out1148;
                    _1728_recIdents = _out1149;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1725_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1726_recOwned;
                    isErased = _1727_recErased;
                    readIdents = _1728_recIdents;
                  }
                } else if (_source64.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1729_recursiveGen;
                    bool _1730_recOwned;
                    bool _1731_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1732_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1150;
                    bool _out1151;
                    bool _out1152;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1153;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1150, out _out1151, out _out1152, out _out1153);
                    _1729_recursiveGen = _out1150;
                    _1730_recOwned = _out1151;
                    _1731_recErased = _out1152;
                    _1732_recIdents = _out1153;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1729_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1730_recOwned;
                    isErased = _1731_recErased;
                    readIdents = _1732_recIdents;
                  }
                } else if (_source64.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1733_recursiveGen;
                    bool _1734_recOwned;
                    bool _1735_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1154;
                    bool _out1155;
                    bool _out1156;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1157;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1154, out _out1155, out _out1156, out _out1157);
                    _1733_recursiveGen = _out1154;
                    _1734_recOwned = _out1155;
                    _1735_recErased = _out1156;
                    _1736_recIdents = _out1157;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1733_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1734_recOwned;
                    isErased = _1735_recErased;
                    readIdents = _1736_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _1737_recursiveGen;
                    bool _1738_recOwned;
                    bool _1739_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1740_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1158;
                    bool _out1159;
                    bool _out1160;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1161;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1158, out _out1159, out _out1160, out _out1161);
                    _1737_recursiveGen = _out1158;
                    _1738_recOwned = _out1159;
                    _1739_recErased = _out1160;
                    _1740_recIdents = _out1161;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1737_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1738_recOwned;
                    isErased = _1739_recErased;
                    readIdents = _1740_recIdents;
                  }
                }
              } else if (_source62.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1741___mcc_h765 = _source62.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1742_recursiveGen;
                  bool _1743___v55;
                  bool _1744___v56;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1745_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1162;
                  bool _out1163;
                  bool _out1164;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1165;
                  DCOMP.COMP.GenExpr(_467_expr, @params, true, out _out1162, out _out1163, out _out1164, out _out1165);
                  _1742_recursiveGen = _out1162;
                  _1743___v55 = _out1163;
                  _1744___v56 = _out1164;
                  _1745_recIdents = _out1165;
                  Dafny.ISequence<Dafny.Rune> _1746_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1166;
                  _out1166 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                  _1746_toTpeGen = _out1166;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _1742_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _1746_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _1745_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1747___mcc_h767 = _source62.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1748_recursiveGen;
                  bool _1749_recOwned;
                  bool _1750_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1751_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1167;
                  bool _out1168;
                  bool _out1169;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1170;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1167, out _out1168, out _out1169, out _out1170);
                  _1748_recursiveGen = _out1167;
                  _1749_recOwned = _out1168;
                  _1750_recErased = _out1169;
                  _1751_recIdents = _out1170;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1748_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1749_recOwned;
                  isErased = _1750_recErased;
                  readIdents = _1751_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _1752___mcc_h769 = _source26.dtor_TypeArg_a0;
              DAST._IType _source65 = _473___mcc_h121;
              if (_source65.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1753___mcc_h772 = _source65.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1754___mcc_h773 = _source65.dtor_typeArgs;
                DAST._IResolvedType _1755___mcc_h774 = _source65.dtor_resolved;
                DAST._IResolvedType _source66 = _1755___mcc_h774;
                if (_source66.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1756___mcc_h778 = _source66.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1757_recursiveGen;
                    bool _1758_recOwned;
                    bool _1759_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1171;
                    bool _out1172;
                    bool _out1173;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1174;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1171, out _out1172, out _out1173, out _out1174);
                    _1757_recursiveGen = _out1171;
                    _1758_recOwned = _out1172;
                    _1759_recErased = _out1173;
                    _1760_recIdents = _out1174;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1757_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1758_recOwned;
                    isErased = _1759_recErased;
                    readIdents = _1760_recIdents;
                  }
                } else if (_source66.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1761___mcc_h780 = _source66.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1762_recursiveGen;
                    bool _1763_recOwned;
                    bool _1764_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1765_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1175;
                    bool _out1176;
                    bool _out1177;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1178;
                    DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1175, out _out1176, out _out1177, out _out1178);
                    _1762_recursiveGen = _out1175;
                    _1763_recOwned = _out1176;
                    _1764_recErased = _out1177;
                    _1765_recIdents = _out1178;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1762_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1763_recOwned;
                    isErased = _1764_recErased;
                    readIdents = _1765_recIdents;
                  }
                } else {
                  DAST._IType _1766___mcc_h782 = _source66.dtor_Newtype_a0;
                  DAST._IType _1767_b = _1766___mcc_h782;
                  {
                    if (object.Equals(_466_fromTpe, _1767_b)) {
                      Dafny.ISequence<Dafny.Rune> _1768_recursiveGen;
                      bool _1769_recOwned;
                      bool _1770_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1771_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1179;
                      bool _out1180;
                      bool _out1181;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1182;
                      DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1179, out _out1180, out _out1181, out _out1182);
                      _1768_recursiveGen = _out1179;
                      _1769_recOwned = _out1180;
                      _1770_recErased = _out1181;
                      _1771_recIdents = _out1182;
                      Dafny.ISequence<Dafny.Rune> _1772_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1183;
                      _out1183 = DCOMP.COMP.GenType(_465_toTpe, true, false);
                      _1772_rhsType = _out1183;
                      Dafny.ISequence<Dafny.Rune> _1773_uneraseFn;
                      _1773_uneraseFn = ((_1769_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1772_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1773_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1768_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1769_recOwned;
                      isErased = false;
                      readIdents = _1771_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1184;
                      bool _out1185;
                      bool _out1186;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1187;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_467_expr, _466_fromTpe, _1767_b), _1767_b, _465_toTpe), @params, mustOwn, out _out1184, out _out1185, out _out1186, out _out1187);
                      s = _out1184;
                      isOwned = _out1185;
                      isErased = _out1186;
                      readIdents = _out1187;
                    }
                  }
                }
              } else if (_source65.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1774___mcc_h784 = _source65.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1775_recursiveGen;
                  bool _1776_recOwned;
                  bool _1777_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1188;
                  bool _out1189;
                  bool _out1190;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1191;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1188, out _out1189, out _out1190, out _out1191);
                  _1775_recursiveGen = _out1188;
                  _1776_recOwned = _out1189;
                  _1777_recErased = _out1190;
                  _1778_recIdents = _out1191;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1775_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1776_recOwned;
                  isErased = _1777_recErased;
                  readIdents = _1778_recIdents;
                }
              } else if (_source65.is_Array) {
                DAST._IType _1779___mcc_h786 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1780_recursiveGen;
                  bool _1781_recOwned;
                  bool _1782_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1783_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1192;
                  bool _out1193;
                  bool _out1194;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1195;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1192, out _out1193, out _out1194, out _out1195);
                  _1780_recursiveGen = _out1192;
                  _1781_recOwned = _out1193;
                  _1782_recErased = _out1194;
                  _1783_recIdents = _out1195;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1780_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1781_recOwned;
                  isErased = _1782_recErased;
                  readIdents = _1783_recIdents;
                }
              } else if (_source65.is_Seq) {
                DAST._IType _1784___mcc_h788 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1785_recursiveGen;
                  bool _1786_recOwned;
                  bool _1787_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1196;
                  bool _out1197;
                  bool _out1198;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1199;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1196, out _out1197, out _out1198, out _out1199);
                  _1785_recursiveGen = _out1196;
                  _1786_recOwned = _out1197;
                  _1787_recErased = _out1198;
                  _1788_recIdents = _out1199;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1785_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1786_recOwned;
                  isErased = _1787_recErased;
                  readIdents = _1788_recIdents;
                }
              } else if (_source65.is_Set) {
                DAST._IType _1789___mcc_h790 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1790_recursiveGen;
                  bool _1791_recOwned;
                  bool _1792_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1200;
                  bool _out1201;
                  bool _out1202;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1203;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1200, out _out1201, out _out1202, out _out1203);
                  _1790_recursiveGen = _out1200;
                  _1791_recOwned = _out1201;
                  _1792_recErased = _out1202;
                  _1793_recIdents = _out1203;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1790_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1791_recOwned;
                  isErased = _1792_recErased;
                  readIdents = _1793_recIdents;
                }
              } else if (_source65.is_Multiset) {
                DAST._IType _1794___mcc_h792 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1795_recursiveGen;
                  bool _1796_recOwned;
                  bool _1797_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1798_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1204;
                  bool _out1205;
                  bool _out1206;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1207;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1204, out _out1205, out _out1206, out _out1207);
                  _1795_recursiveGen = _out1204;
                  _1796_recOwned = _out1205;
                  _1797_recErased = _out1206;
                  _1798_recIdents = _out1207;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1795_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1796_recOwned;
                  isErased = _1797_recErased;
                  readIdents = _1798_recIdents;
                }
              } else if (_source65.is_Map) {
                DAST._IType _1799___mcc_h794 = _source65.dtor_key;
                DAST._IType _1800___mcc_h795 = _source65.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1801_recursiveGen;
                  bool _1802_recOwned;
                  bool _1803_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1804_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1208;
                  bool _out1209;
                  bool _out1210;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1211;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1208, out _out1209, out _out1210, out _out1211);
                  _1801_recursiveGen = _out1208;
                  _1802_recOwned = _out1209;
                  _1803_recErased = _out1210;
                  _1804_recIdents = _out1211;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1801_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1802_recOwned;
                  isErased = _1803_recErased;
                  readIdents = _1804_recIdents;
                }
              } else if (_source65.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1805___mcc_h798 = _source65.dtor_args;
                DAST._IType _1806___mcc_h799 = _source65.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1807_recursiveGen;
                  bool _1808_recOwned;
                  bool _1809_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1810_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1212;
                  bool _out1213;
                  bool _out1214;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1215;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1212, out _out1213, out _out1214, out _out1215);
                  _1807_recursiveGen = _out1212;
                  _1808_recOwned = _out1213;
                  _1809_recErased = _out1214;
                  _1810_recIdents = _out1215;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1807_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1808_recOwned;
                  isErased = _1809_recErased;
                  readIdents = _1810_recIdents;
                }
              } else if (_source65.is_Primitive) {
                DAST._IPrimitive _1811___mcc_h802 = _source65.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1812_recursiveGen;
                  bool _1813_recOwned;
                  bool _1814_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1216;
                  bool _out1217;
                  bool _out1218;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1219;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1216, out _out1217, out _out1218, out _out1219);
                  _1812_recursiveGen = _out1216;
                  _1813_recOwned = _out1217;
                  _1814_recErased = _out1218;
                  _1815_recIdents = _out1219;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1812_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1813_recOwned;
                  isErased = _1814_recErased;
                  readIdents = _1815_recIdents;
                }
              } else if (_source65.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1816___mcc_h804 = _source65.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1817_recursiveGen;
                  bool _1818_recOwned;
                  bool _1819_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1220;
                  bool _out1221;
                  bool _out1222;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1223;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1220, out _out1221, out _out1222, out _out1223);
                  _1817_recursiveGen = _out1220;
                  _1818_recOwned = _out1221;
                  _1819_recErased = _out1222;
                  _1820_recIdents = _out1223;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1817_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1818_recOwned;
                  isErased = _1819_recErased;
                  readIdents = _1820_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1821___mcc_h806 = _source65.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1822_recursiveGen;
                  bool _1823_recOwned;
                  bool _1824_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1224;
                  bool _out1225;
                  bool _out1226;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1227;
                  DCOMP.COMP.GenExpr(_467_expr, @params, mustOwn, out _out1224, out _out1225, out _out1226, out _out1227);
                  _1822_recursiveGen = _out1224;
                  _1823_recOwned = _out1225;
                  _1824_recErased = _out1226;
                  _1825_recIdents = _out1227;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1822_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1823_recOwned;
                  isErased = _1824_recErased;
                  readIdents = _1825_recIdents;
                }
              }
            }
          }
        }
      } else if (_source19.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _1826___mcc_h22 = _source19.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _1827_exprs = _1826___mcc_h22;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _1828_generatedValues;
          _1828_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _1829_i;
          _1829_i = BigInteger.Zero;
          bool _1830_allErased;
          _1830_allErased = true;
          while ((_1829_i) < (new BigInteger((_1827_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _1831_recursiveGen;
            bool _1832___v58;
            bool _1833_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1834_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1228;
            bool _out1229;
            bool _out1230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1231;
            DCOMP.COMP.GenExpr((_1827_exprs).Select(_1829_i), @params, true, out _out1228, out _out1229, out _out1230, out _out1231);
            _1831_recursiveGen = _out1228;
            _1832___v58 = _out1229;
            _1833_isErased = _out1230;
            _1834_recIdents = _out1231;
            _1830_allErased = (_1830_allErased) && (_1833_isErased);
            _1828_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_1828_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_1831_recursiveGen, _1833_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1834_recIdents);
            _1829_i = (_1829_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _1829_i = BigInteger.Zero;
          while ((_1829_i) < (new BigInteger((_1828_generatedValues).Count))) {
            if ((_1829_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _1835_gen;
            _1835_gen = ((_1828_generatedValues).Select(_1829_i)).dtor__0;
            if ((((_1828_generatedValues).Select(_1829_i)).dtor__1) && (!(_1830_allErased))) {
              _1835_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _1835_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1835_gen);
            _1829_i = (_1829_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _1830_allErased;
        }
      } else if (_source19.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _1836___mcc_h23 = _source19.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _1837_exprs = _1836___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _1838_generatedValues;
          _1838_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _1839_i;
          _1839_i = BigInteger.Zero;
          bool _1840_allErased;
          _1840_allErased = true;
          while ((_1839_i) < (new BigInteger((_1837_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _1841_recursiveGen;
            bool _1842___v59;
            bool _1843_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1844_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1232;
            bool _out1233;
            bool _out1234;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1235;
            DCOMP.COMP.GenExpr((_1837_exprs).Select(_1839_i), @params, true, out _out1232, out _out1233, out _out1234, out _out1235);
            _1841_recursiveGen = _out1232;
            _1842___v59 = _out1233;
            _1843_isErased = _out1234;
            _1844_recIdents = _out1235;
            _1840_allErased = (_1840_allErased) && (_1843_isErased);
            _1838_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_1838_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_1841_recursiveGen, _1843_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1844_recIdents);
            _1839_i = (_1839_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _1839_i = BigInteger.Zero;
          while ((_1839_i) < (new BigInteger((_1838_generatedValues).Count))) {
            if ((_1839_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _1845_gen;
            _1845_gen = ((_1838_generatedValues).Select(_1839_i)).dtor__0;
            if ((((_1838_generatedValues).Select(_1839_i)).dtor__1) && (!(_1840_allErased))) {
              _1845_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _1845_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1845_gen);
            _1839_i = (_1839_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashSet<_>>()"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_This) {
        {
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.clone()");
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
            isOwned = false;
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"));
          isErased = false;
        }
      } else if (_source19.is_Ite) {
        DAST._IExpression _1846___mcc_h24 = _source19.dtor_cond;
        DAST._IExpression _1847___mcc_h25 = _source19.dtor_thn;
        DAST._IExpression _1848___mcc_h26 = _source19.dtor_els;
        DAST._IExpression _1849_f = _1848___mcc_h26;
        DAST._IExpression _1850_t = _1847___mcc_h25;
        DAST._IExpression _1851_cond = _1846___mcc_h24;
        {
          Dafny.ISequence<Dafny.Rune> _1852_condString;
          bool _1853___v60;
          bool _1854_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1855_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1236;
          bool _out1237;
          bool _out1238;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1239;
          DCOMP.COMP.GenExpr(_1851_cond, @params, true, out _out1236, out _out1237, out _out1238, out _out1239);
          _1852_condString = _out1236;
          _1853___v60 = _out1237;
          _1854_condErased = _out1238;
          _1855_recIdentsCond = _out1239;
          if (!(_1854_condErased)) {
            _1852_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1852_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _1856___v61;
          bool _1857_tHasToBeOwned;
          bool _1858___v62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1859___v63;
          Dafny.ISequence<Dafny.Rune> _out1240;
          bool _out1241;
          bool _out1242;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
          DCOMP.COMP.GenExpr(_1850_t, @params, mustOwn, out _out1240, out _out1241, out _out1242, out _out1243);
          _1856___v61 = _out1240;
          _1857_tHasToBeOwned = _out1241;
          _1858___v62 = _out1242;
          _1859___v63 = _out1243;
          Dafny.ISequence<Dafny.Rune> _1860_fString;
          bool _1861_fOwned;
          bool _1862_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1863_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1244;
          bool _out1245;
          bool _out1246;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
          DCOMP.COMP.GenExpr(_1849_f, @params, _1857_tHasToBeOwned, out _out1244, out _out1245, out _out1246, out _out1247);
          _1860_fString = _out1244;
          _1861_fOwned = _out1245;
          _1862_fErased = _out1246;
          _1863_recIdentsF = _out1247;
          Dafny.ISequence<Dafny.Rune> _1864_tString;
          bool _1865___v64;
          bool _1866_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1248;
          bool _out1249;
          bool _out1250;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
          DCOMP.COMP.GenExpr(_1850_t, @params, _1861_fOwned, out _out1248, out _out1249, out _out1250, out _out1251);
          _1864_tString = _out1248;
          _1865___v64 = _out1249;
          _1866_tErased = _out1250;
          _1867_recIdentsT = _out1251;
          if ((!(_1862_fErased)) || (!(_1866_tErased))) {
            if (_1862_fErased) {
              _1860_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1860_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_1866_tErased) {
              _1864_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1864_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1852_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1864_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1860_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _1861_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1855_recIdentsCond, _1867_recIdentsT), _1863_recIdentsF);
          isErased = (_1862_fErased) || (_1866_tErased);
        }
      } else if (_source19.is_UnOp) {
        DAST._IUnaryOp _1868___mcc_h27 = _source19.dtor_unOp;
        DAST._IExpression _1869___mcc_h28 = _source19.dtor_expr;
        DAST._IUnaryOp _source67 = _1868___mcc_h27;
        if (_source67.is_Not) {
          DAST._IExpression _1870_e = _1869___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _1871_recursiveGen;
            bool _1872___v65;
            bool _1873_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1252;
            bool _out1253;
            bool _out1254;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1255;
            DCOMP.COMP.GenExpr(_1870_e, @params, true, out _out1252, out _out1253, out _out1254, out _out1255);
            _1871_recursiveGen = _out1252;
            _1872___v65 = _out1253;
            _1873_recErased = _out1254;
            _1874_recIdents = _out1255;
            if (!(_1873_recErased)) {
              _1871_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1871_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _1871_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _1874_recIdents;
            isErased = true;
          }
        } else if (_source67.is_BitwiseNot) {
          DAST._IExpression _1875_e = _1869___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _1876_recursiveGen;
            bool _1877___v66;
            bool _1878_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1256;
            bool _out1257;
            bool _out1258;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
            DCOMP.COMP.GenExpr(_1875_e, @params, true, out _out1256, out _out1257, out _out1258, out _out1259);
            _1876_recursiveGen = _out1256;
            _1877___v66 = _out1257;
            _1878_recErased = _out1258;
            _1879_recIdents = _out1259;
            if (!(_1878_recErased)) {
              _1876_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _1876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _1879_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _1880_e = _1869___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _1881_recursiveGen;
            bool _1882___v67;
            bool _1883_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1260;
            bool _out1261;
            bool _out1262;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1263;
            DCOMP.COMP.GenExpr(_1880_e, @params, false, out _out1260, out _out1261, out _out1262, out _out1263);
            _1881_recursiveGen = _out1260;
            _1882___v67 = _out1261;
            _1883_recErased = _out1262;
            _1884_recIdents = _out1263;
            if (!(_1883_recErased)) {
              _1881_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1881_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1881_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len()"));
            isOwned = true;
            readIdents = _1884_recIdents;
            isErased = true;
          }
        }
      } else if (_source19.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _1885___mcc_h29 = _source19.dtor_op;
        DAST._IExpression _1886___mcc_h30 = _source19.dtor_left;
        DAST._IExpression _1887___mcc_h31 = _source19.dtor_right;
        DAST._IExpression _1888_r = _1887___mcc_h31;
        DAST._IExpression _1889_l = _1886___mcc_h30;
        Dafny.ISequence<Dafny.Rune> _1890_op = _1885___mcc_h29;
        {
          Dafny.ISequence<Dafny.Rune> _1891_left;
          bool _1892___v68;
          bool _1893_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1894_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1264;
          bool _out1265;
          bool _out1266;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1267;
          DCOMP.COMP.GenExpr(_1889_l, @params, true, out _out1264, out _out1265, out _out1266, out _out1267);
          _1891_left = _out1264;
          _1892___v68 = _out1265;
          _1893_leftErased = _out1266;
          _1894_recIdentsL = _out1267;
          Dafny.ISequence<Dafny.Rune> _1895_right;
          bool _1896___v69;
          bool _1897_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1898_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1268;
          bool _out1269;
          bool _out1270;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
          DCOMP.COMP.GenExpr(_1888_r, @params, true, out _out1268, out _out1269, out _out1270, out _out1271);
          _1895_right = _out1268;
          _1896___v69 = _out1269;
          _1897_rightErased = _out1270;
          _1898_recIdentsR = _out1271;
          if (!(_1893_leftErased)) {
            _1891_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1891_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_1897_rightErased)) {
            _1895_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1895_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_1890_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _1891_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _1895_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_1890_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _1891_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _1895_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1891_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _1890_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _1895_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1894_recIdentsL, _1898_recIdentsR);
          isErased = true;
        }
      } else if (_source19.is_Select) {
        DAST._IExpression _1899___mcc_h32 = _source19.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1900___mcc_h33 = _source19.dtor_field;
        bool _1901___mcc_h34 = _source19.dtor_isConstant;
        bool _1902___mcc_h35 = _source19.dtor_onDatatype;
        bool _1903_isDatatype = _1902___mcc_h35;
        bool _1904_isConstant = _1901___mcc_h34;
        Dafny.ISequence<Dafny.Rune> _1905_field = _1900___mcc_h33;
        DAST._IExpression _1906_on = _1899___mcc_h32;
        {
          Dafny.ISequence<Dafny.Rune> _1907_onString;
          bool _1908_onOwned;
          bool _1909_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1910_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1272;
          bool _out1273;
          bool _out1274;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1275;
          DCOMP.COMP.GenExpr(_1906_on, @params, false, out _out1272, out _out1273, out _out1274, out _out1275);
          _1907_onString = _out1272;
          _1908_onOwned = _out1273;
          _1909_onErased = _out1274;
          _1910_recIdents = _out1275;
          if (!(_1909_onErased)) {
            Dafny.ISequence<Dafny.Rune> _1911_eraseFn;
            _1911_eraseFn = ((_1908_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _1907_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _1911_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1907_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_1903_isDatatype) || (_1904_isConstant)) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1907_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _1905_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            if (_1904_isConstant) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            }
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            } else {
              isOwned = false;
            }
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _1907_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _1905_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          }
          isErased = false;
          readIdents = _1910_recIdents;
        }
      } else if (_source19.is_SelectFn) {
        DAST._IExpression _1912___mcc_h36 = _source19.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1913___mcc_h37 = _source19.dtor_field;
        bool _1914___mcc_h38 = _source19.dtor_onDatatype;
        bool _1915___mcc_h39 = _source19.dtor_isStatic;
        BigInteger _1916___mcc_h40 = _source19.dtor_arity;
        BigInteger _1917_arity = _1916___mcc_h40;
        bool _1918_isStatic = _1915___mcc_h39;
        bool _1919_isDatatype = _1914___mcc_h38;
        Dafny.ISequence<Dafny.Rune> _1920_field = _1913___mcc_h37;
        DAST._IExpression _1921_on = _1912___mcc_h36;
        {
          Dafny.ISequence<Dafny.Rune> _1922_onString;
          bool _1923_onOwned;
          bool _1924___v70;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1925_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1276;
          bool _out1277;
          bool _out1278;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1279;
          DCOMP.COMP.GenExpr(_1921_on, @params, false, out _out1276, out _out1277, out _out1278, out _out1279);
          _1922_onString = _out1276;
          _1923_onOwned = _out1277;
          _1924___v70 = _out1278;
          _1925_recIdents = _out1279;
          if (_1918_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1922_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1920_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1922_onString), ((_1923_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _1926_args;
            _1926_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _1927_i;
            _1927_i = BigInteger.Zero;
            while ((_1927_i) < (_1917_arity)) {
              if ((_1927_i).Sign == 1) {
                _1926_args = Dafny.Sequence<Dafny.Rune>.Concat(_1926_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1926_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1926_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_1927_i));
              _1927_i = (_1927_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1926_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _1920_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1926_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = true;
          readIdents = _1925_recIdents;
        }
      } else if (_source19.is_TupleSelect) {
        DAST._IExpression _1928___mcc_h41 = _source19.dtor_expr;
        BigInteger _1929___mcc_h42 = _source19.dtor_index;
        BigInteger _1930_idx = _1929___mcc_h42;
        DAST._IExpression _1931_on = _1928___mcc_h41;
        {
          Dafny.ISequence<Dafny.Rune> _1932_onString;
          bool _1933___v71;
          bool _1934_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1935_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1280;
          bool _out1281;
          bool _out1282;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1283;
          DCOMP.COMP.GenExpr(_1931_on, @params, false, out _out1280, out _out1281, out _out1282, out _out1283);
          _1932_onString = _out1280;
          _1933___v71 = _out1281;
          _1934_tupErased = _out1282;
          _1935_recIdents = _out1283;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1932_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_1930_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _1934_tupErased;
          readIdents = _1935_recIdents;
        }
      } else if (_source19.is_Call) {
        DAST._IExpression _1936___mcc_h43 = _source19.dtor_on;
        Dafny.ISequence<Dafny.Rune> _1937___mcc_h44 = _source19.dtor_name;
        Dafny.ISequence<DAST._IType> _1938___mcc_h45 = _source19.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _1939___mcc_h46 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _1940_args = _1939___mcc_h46;
        Dafny.ISequence<DAST._IType> _1941_typeArgs = _1938___mcc_h45;
        Dafny.ISequence<Dafny.Rune> _1942_name = _1937___mcc_h44;
        DAST._IExpression _1943_on = _1936___mcc_h43;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _1944_typeArgString;
          _1944_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_1941_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _1945_typeI;
            _1945_typeI = BigInteger.Zero;
            _1944_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_1945_typeI) < (new BigInteger((_1941_typeArgs).Count))) {
              if ((_1945_typeI).Sign == 1) {
                _1944_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_1944_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _1946_typeString;
              Dafny.ISequence<Dafny.Rune> _out1284;
              _out1284 = DCOMP.COMP.GenType((_1941_typeArgs).Select(_1945_typeI), false, false);
              _1946_typeString = _out1284;
              _1944_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_1944_typeArgString, _1946_typeString);
              _1945_typeI = (_1945_typeI) + (BigInteger.One);
            }
            _1944_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_1944_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _1947_argString;
          _1947_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _1948_i;
          _1948_i = BigInteger.Zero;
          while ((_1948_i) < (new BigInteger((_1940_args).Count))) {
            if ((_1948_i).Sign == 1) {
              _1947_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1947_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _1949_argExpr;
            bool _1950_isOwned;
            bool _1951_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1952_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1285;
            bool _out1286;
            bool _out1287;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1288;
            DCOMP.COMP.GenExpr((_1940_args).Select(_1948_i), @params, false, out _out1285, out _out1286, out _out1287, out _out1288);
            _1949_argExpr = _out1285;
            _1950_isOwned = _out1286;
            _1951_argErased = _out1287;
            _1952_argIdents = _out1288;
            if (_1950_isOwned) {
              _1949_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _1949_argExpr);
            }
            _1947_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1947_argString, _1949_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1952_argIdents);
            _1948_i = (_1948_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _1953_enclosingString;
          bool _1954___v72;
          bool _1955___v73;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1956_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1289;
          bool _out1290;
          bool _out1291;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
          DCOMP.COMP.GenExpr(_1943_on, @params, false, out _out1289, out _out1290, out _out1291, out _out1292);
          _1953_enclosingString = _out1289;
          _1954___v72 = _out1290;
          _1955___v73 = _out1291;
          _1956_recIdents = _out1292;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1956_recIdents);
          DAST._IExpression _source68 = _1943_on;
          if (_source68.is_Literal) {
            DAST._ILiteral _1957___mcc_h808 = _source68.dtor_Literal_a0;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _1958___mcc_h810 = _source68.dtor_Ident_a0;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1959___mcc_h812 = _source68.dtor_Companion_a0;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_1953_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source68.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _1960___mcc_h814 = _source68.dtor_Tuple_a0;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1961___mcc_h816 = _source68.dtor_path;
            Dafny.ISequence<DAST._IExpression> _1962___mcc_h817 = _source68.dtor_args;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _1963___mcc_h820 = _source68.dtor_dims;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1964___mcc_h822 = _source68.dtor_path;
            Dafny.ISequence<Dafny.Rune> _1965___mcc_h823 = _source68.dtor_variant;
            bool _1966___mcc_h824 = _source68.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1967___mcc_h825 = _source68.dtor_contents;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Convert) {
            DAST._IExpression _1968___mcc_h830 = _source68.dtor_value;
            DAST._IType _1969___mcc_h831 = _source68.dtor_from;
            DAST._IType _1970___mcc_h832 = _source68.dtor_typ;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _1971___mcc_h836 = _source68.dtor_elements;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _1972___mcc_h838 = _source68.dtor_elements;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_This) {
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Ite) {
            DAST._IExpression _1973___mcc_h840 = _source68.dtor_cond;
            DAST._IExpression _1974___mcc_h841 = _source68.dtor_thn;
            DAST._IExpression _1975___mcc_h842 = _source68.dtor_els;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_UnOp) {
            DAST._IUnaryOp _1976___mcc_h846 = _source68.dtor_unOp;
            DAST._IExpression _1977___mcc_h847 = _source68.dtor_expr;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _1978___mcc_h850 = _source68.dtor_op;
            DAST._IExpression _1979___mcc_h851 = _source68.dtor_left;
            DAST._IExpression _1980___mcc_h852 = _source68.dtor_right;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Select) {
            DAST._IExpression _1981___mcc_h856 = _source68.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _1982___mcc_h857 = _source68.dtor_field;
            bool _1983___mcc_h858 = _source68.dtor_isConstant;
            bool _1984___mcc_h859 = _source68.dtor_onDatatype;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_SelectFn) {
            DAST._IExpression _1985___mcc_h864 = _source68.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _1986___mcc_h865 = _source68.dtor_field;
            bool _1987___mcc_h866 = _source68.dtor_onDatatype;
            bool _1988___mcc_h867 = _source68.dtor_isStatic;
            BigInteger _1989___mcc_h868 = _source68.dtor_arity;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_TupleSelect) {
            DAST._IExpression _1990___mcc_h874 = _source68.dtor_expr;
            BigInteger _1991___mcc_h875 = _source68.dtor_index;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Call) {
            DAST._IExpression _1992___mcc_h878 = _source68.dtor_on;
            Dafny.ISequence<Dafny.Rune> _1993___mcc_h879 = _source68.dtor_name;
            Dafny.ISequence<DAST._IType> _1994___mcc_h880 = _source68.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _1995___mcc_h881 = _source68.dtor_args;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _1996___mcc_h886 = _source68.dtor_params;
            DAST._IType _1997___mcc_h887 = _source68.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _1998___mcc_h888 = _source68.dtor_body;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _1999___mcc_h892 = _source68.dtor_name;
            DAST._IType _2000___mcc_h893 = _source68.dtor_typ;
            DAST._IExpression _2001___mcc_h894 = _source68.dtor_value;
            DAST._IExpression _2002___mcc_h895 = _source68.dtor_iifeBody;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Apply) {
            DAST._IExpression _2003___mcc_h900 = _source68.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2004___mcc_h901 = _source68.dtor_args;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_TypeTest) {
            DAST._IExpression _2005___mcc_h904 = _source68.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2006___mcc_h905 = _source68.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2007___mcc_h906 = _source68.dtor_variant;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _2008___mcc_h910 = _source68.dtor_typ;
            {
              _1953_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1953_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_1942_name)), _1944_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1947_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source19.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2009___mcc_h47 = _source19.dtor_params;
        DAST._IType _2010___mcc_h48 = _source19.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2011___mcc_h49 = _source19.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2012_body = _2011___mcc_h49;
        DAST._IType _2013_retType = _2010___mcc_h48;
        Dafny.ISequence<DAST._IFormal> _2014_params = _2009___mcc_h47;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2015_paramNames;
          _2015_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2016_i;
          _2016_i = BigInteger.Zero;
          while ((_2016_i) < (new BigInteger((_2014_params).Count))) {
            _2015_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2015_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2014_params).Select(_2016_i)).dtor_name));
            _2016_i = (_2016_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2017_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2018_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1293;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1294;
          DCOMP.COMP.GenStmts(_2012_body, _2015_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1293, out _out1294);
          _2017_recursiveGen = _out1293;
          _2018_recIdents = _out1294;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2019_allReadCloned;
          _2019_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2018_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2020_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2018_recIdents).Elements) {
              _2020_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2018_recIdents).Contains(_2020_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1513)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2015_paramNames).Contains(_2020_next))) {
              _2019_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2019_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2020_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2020_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2020_next));
            }
            _2018_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2018_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2020_next));
          }
          Dafny.ISequence<Dafny.Rune> _2021_paramsString;
          _2021_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2016_i = BigInteger.Zero;
          while ((_2016_i) < (new BigInteger((_2014_params).Count))) {
            if ((_2016_i).Sign == 1) {
              _2021_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2021_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2022_typStr;
            Dafny.ISequence<Dafny.Rune> _out1295;
            _out1295 = DCOMP.COMP.GenType(((_2014_params).Select(_2016_i)).dtor_typ, false, true);
            _2022_typStr = _out1295;
            _2021_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2021_paramsString, ((_2014_params).Select(_2016_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2022_typStr);
            _2016_i = (_2016_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2023_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1296;
          _out1296 = DCOMP.COMP.GenType(_2013_retType, false, true);
          _2023_retTypeGen = _out1296;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper({\n"), _2019_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::boxed::Box::new(move |")), _2021_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2023_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2017_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2024___mcc_h50 = _source19.dtor_name;
        DAST._IType _2025___mcc_h51 = _source19.dtor_typ;
        DAST._IExpression _2026___mcc_h52 = _source19.dtor_value;
        DAST._IExpression _2027___mcc_h53 = _source19.dtor_iifeBody;
        DAST._IExpression _2028_iifeBody = _2027___mcc_h53;
        DAST._IExpression _2029_value = _2026___mcc_h52;
        DAST._IType _2030_tpe = _2025___mcc_h51;
        Dafny.ISequence<Dafny.Rune> _2031_name = _2024___mcc_h50;
        {
          Dafny.ISequence<Dafny.Rune> _2032_valueGen;
          bool _2033_valueOwned;
          bool _2034_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2035_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1297;
          bool _out1298;
          bool _out1299;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1300;
          DCOMP.COMP.GenExpr(_2029_value, @params, false, out _out1297, out _out1298, out _out1299, out _out1300);
          _2032_valueGen = _out1297;
          _2033_valueOwned = _out1298;
          _2034_valueErased = _out1299;
          _2035_recIdents = _out1300;
          if (_2034_valueErased) {
            Dafny.ISequence<Dafny.Rune> _2036_eraseFn;
            _2036_eraseFn = ((_2033_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
            _2032_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::"), _2036_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2032_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2035_recIdents;
          Dafny.ISequence<Dafny.Rune> _2037_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1301;
          _out1301 = DCOMP.COMP.GenType(_2030_tpe, false, true);
          _2037_valueTypeGen = _out1301;
          Dafny.ISequence<Dafny.Rune> _2038_bodyGen;
          bool _2039_bodyOwned;
          bool _2040_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2041_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1302;
          bool _out1303;
          bool _out1304;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
          DCOMP.COMP.GenExpr(_2028_iifeBody, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, ((_2033_valueOwned) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2031_name))))), mustOwn, out _out1302, out _out1303, out _out1304, out _out1305);
          _2038_bodyGen = _out1302;
          _2039_bodyOwned = _out1303;
          _2040_bodyErased = _out1304;
          _2041_bodyIdents = _out1305;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2041_bodyIdents);
          Dafny.ISequence<Dafny.Rune> _2042_eraseFn;
          _2042_eraseFn = ((_2033_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2031_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((_2033_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")))), _2037_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2032_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2038_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2039_bodyOwned;
          isErased = _2040_bodyErased;
        }
      } else if (_source19.is_Apply) {
        DAST._IExpression _2043___mcc_h54 = _source19.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2044___mcc_h55 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2045_args = _2044___mcc_h55;
        DAST._IExpression _2046_func = _2043___mcc_h54;
        {
          Dafny.ISequence<Dafny.Rune> _2047_funcString;
          bool _2048___v76;
          bool _2049_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1306;
          bool _out1307;
          bool _out1308;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1309;
          DCOMP.COMP.GenExpr(_2046_func, @params, false, out _out1306, out _out1307, out _out1308, out _out1309);
          _2047_funcString = _out1306;
          _2048___v76 = _out1307;
          _2049_funcErased = _out1308;
          _2050_recIdents = _out1309;
          readIdents = _2050_recIdents;
          Dafny.ISequence<Dafny.Rune> _2051_argString;
          _2051_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2052_i;
          _2052_i = BigInteger.Zero;
          while ((_2052_i) < (new BigInteger((_2045_args).Count))) {
            if ((_2052_i).Sign == 1) {
              _2051_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2051_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2053_argExpr;
            bool _2054_isOwned;
            bool _2055_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2056_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1310;
            bool _out1311;
            bool _out1312;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
            DCOMP.COMP.GenExpr((_2045_args).Select(_2052_i), @params, false, out _out1310, out _out1311, out _out1312, out _out1313);
            _2053_argExpr = _out1310;
            _2054_isOwned = _out1311;
            _2055_argErased = _out1312;
            _2056_argIdents = _out1313;
            if (_2054_isOwned) {
              _2053_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2053_argExpr);
            }
            _2051_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2051_argString, _2053_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2056_argIdents);
            _2052_i = (_2052_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2047_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2051_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source19.is_TypeTest) {
        DAST._IExpression _2057___mcc_h56 = _source19.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2058___mcc_h57 = _source19.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2059___mcc_h58 = _source19.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2060_variant = _2059___mcc_h58;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2061_dType = _2058___mcc_h57;
        DAST._IExpression _2062_on = _2057___mcc_h56;
        {
          Dafny.ISequence<Dafny.Rune> _2063_exprGen;
          bool _2064___v77;
          bool _2065_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2066_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1314;
          bool _out1315;
          bool _out1316;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1317;
          DCOMP.COMP.GenExpr(_2062_on, @params, false, out _out1314, out _out1315, out _out1316, out _out1317);
          _2063_exprGen = _out1314;
          _2064___v77 = _out1315;
          _2065_exprErased = _out1316;
          _2066_recIdents = _out1317;
          Dafny.ISequence<Dafny.Rune> _2067_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1318;
          _out1318 = DCOMP.COMP.GenPath(_2061_dType);
          _2067_dTypePath = _out1318;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2063_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2067_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2060_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2066_recIdents;
        }
      } else {
        DAST._IType _2068___mcc_h59 = _source19.dtor_typ;
        DAST._IType _2069_typ = _2068___mcc_h59;
        {
          Dafny.ISequence<Dafny.Rune> _2070_typString;
          Dafny.ISequence<Dafny.Rune> _out1319;
          _out1319 = DCOMP.COMP.GenType(_2069_typ, false, false);
          _2070_typString = _out1319;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2070_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
          isOwned = true;
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      }
    }
    public static Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern crate dafny_runtime;\n"));
      BigInteger _2071_i;
      _2071_i = BigInteger.Zero;
      while ((_2071_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2072_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1320;
        _out1320 = DCOMP.COMP.GenModule((p).Select(_2071_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2072_generated = _out1320;
        if ((_2071_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2072_generated);
        _2071_i = (_2071_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2073_i;
      _2073_i = BigInteger.Zero;
      while ((_2073_i) < (new BigInteger((fullName).Count))) {
        if ((_2073_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2073_i));
        _2073_i = (_2073_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

