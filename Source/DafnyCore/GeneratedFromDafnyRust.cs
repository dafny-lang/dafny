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
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Default)]\npub struct r#"), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _19_fields), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      Dafny.ISequence<Dafny.Rune> _30_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _31_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out15;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out16;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(path)), Dafny.Set<DAST._IType>.FromElements(), out _out15, out _out16);
      _30_implBody = _out15;
      _31_traitBodies = _out16;
      _30_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn new() -> Self {\n"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _20_fieldInits), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n}\n")), _30_implBody);
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _30_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      if ((new BigInteger(((c).dtor_superClasses).Count)).Sign == 1) {
        BigInteger _32_i;
        _32_i = BigInteger.Zero;
        while ((_32_i) < (new BigInteger(((c).dtor_superClasses).Count))) {
          DAST._IType _33_superClass;
          _33_superClass = ((c).dtor_superClasses).Select(_32_i);
          DAST._IType _source2 = _33_superClass;
          if (_source2.is_Path) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _34___mcc_h1 = _source2.dtor_Path_a0;
            Dafny.ISequence<DAST._IType> _35___mcc_h2 = _source2.dtor_typeArgs;
            DAST._IResolvedType _36___mcc_h3 = _source2.dtor_resolved;
            DAST._IResolvedType _source3 = _36___mcc_h3;
            if (_source3.is_Datatype) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _37___mcc_h7 = _source3.dtor_path;
            } else if (_source3.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _38___mcc_h9 = _source3.dtor_path;
              Dafny.ISequence<DAST._IType> _39_typeArgs = _35___mcc_h2;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _40_traitPath = _34___mcc_h1;
              {
                Dafny.ISequence<Dafny.Rune> _41_pathStr;
                Dafny.ISequence<Dafny.Rune> _out17;
                _out17 = DCOMP.COMP.GenPath(_40_traitPath);
                _41_pathStr = _out17;
                Dafny.ISequence<Dafny.Rune> _42_typeArgs;
                Dafny.ISequence<Dafny.Rune> _out18;
                _out18 = DCOMP.COMP.GenTypeArgs(_39_typeArgs, false, false);
                _42_typeArgs = _out18;
                Dafny.ISequence<Dafny.Rune> _43_body;
                _43_body = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                if ((_31_traitBodies).Contains(_40_traitPath)) {
                  _43_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(_31_traitBodies, _40_traitPath);
                }
                Dafny.ISequence<Dafny.Rune> _44_genSelfPath;
                Dafny.ISequence<Dafny.Rune> _out19;
                _out19 = DCOMP.COMP.GenPath(path);
                _44_genSelfPath = _out19;
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nimpl ")), _41_pathStr), _42_typeArgs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" for ::std::rc::Rc<")), _44_genSelfPath), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> {\n")), _43_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
              }
            } else {
              DAST._IType _45___mcc_h11 = _source3.dtor_Newtype_a0;
            }
          } else if (_source2.is_Tuple) {
            Dafny.ISequence<DAST._IType> _46___mcc_h13 = _source2.dtor_Tuple_a0;
          } else if (_source2.is_Array) {
            DAST._IType _47___mcc_h15 = _source2.dtor_element;
          } else if (_source2.is_Seq) {
            DAST._IType _48___mcc_h17 = _source2.dtor_element;
          } else if (_source2.is_Set) {
            DAST._IType _49___mcc_h19 = _source2.dtor_element;
          } else if (_source2.is_Multiset) {
            DAST._IType _50___mcc_h21 = _source2.dtor_element;
          } else if (_source2.is_Map) {
            DAST._IType _51___mcc_h23 = _source2.dtor_key;
            DAST._IType _52___mcc_h24 = _source2.dtor_value;
          } else if (_source2.is_Arrow) {
            Dafny.ISequence<DAST._IType> _53___mcc_h27 = _source2.dtor_args;
            DAST._IType _54___mcc_h28 = _source2.dtor_result;
          } else if (_source2.is_Primitive) {
            DAST._IPrimitive _55___mcc_h31 = _source2.dtor_Primitive_a0;
          } else if (_source2.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _56___mcc_h33 = _source2.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _57___mcc_h35 = _source2.dtor_TypeArg_a0;
          }
          _32_i = (_32_i) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.Rune> _58_printImpl;
      _58_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n"));
      _58_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_58_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(__fmt_print_formatter, \"r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((new BigInteger(((c).dtor_fields).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"));
      BigInteger _59_i;
      _59_i = BigInteger.Zero;
      while ((_59_i) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _60_field;
        _60_field = ((c).dtor_fields).Select(_59_i);
        if ((_59_i).Sign == 1) {
          _58_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_58_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \", \")?;"));
        }
        _58_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_58_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(::std::ops::Deref::deref(&(self.r#")), ((_60_field).dtor_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow())), __fmt_print_formatter, false)?;"));
        _59_i = (_59_i) + (BigInteger.One);
      }
      _58_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_58_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \")\")?;\nOk(())\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _61_ptrPartialEqImpl;
      _61_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::cmp::PartialEq for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      _61_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn eq(&self, other: &Self) -> bool {\n"));
      _61_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)"));
      _61_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _58_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _61_ptrPartialEqImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _62_typeParamsSet;
      _62_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<Dafny.Rune> _63_typeParams;
      _63_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _64_tpI;
      _64_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        _63_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_64_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _65_tp;
          _65_tp = ((t).dtor_typeParams).Select(_64_tpI);
          _62_typeParamsSet = Dafny.Set<DAST._IType>.Union(_62_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_65_tp));
          Dafny.ISequence<Dafny.Rune> _66_genTp;
          Dafny.ISequence<Dafny.Rune> _out20;
          _out20 = DCOMP.COMP.GenType(_65_tp, false, false);
          _66_genTp = _out20;
          _63_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_63_typeParams, _66_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          _64_tpI = (_64_tpI) + (BigInteger.One);
        }
        _63_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(_63_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _67_fullPath;
      _67_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<Dafny.Rune> _68_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _69___v6;
      Dafny.ISequence<Dafny.Rune> _out21;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out22;
      DCOMP.COMP.GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_67_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_67_fullPath)), _62_typeParamsSet, out _out21, out _out22);
      _68_implBody = _out21;
      _69___v6 = _out22;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub trait r#"), (t).dtor_name), _63_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _68_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenNewtype(DAST._INewtype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _70_typeParamsSet;
      Dafny.ISequence<Dafny.Rune> _71_typeParams;
      Dafny.ISequence<Dafny.Rune> _72_constrainedTypeParams;
      Dafny.ISet<DAST._IType> _out23;
      Dafny.ISequence<Dafny.Rune> _out24;
      Dafny.ISequence<Dafny.Rune> _out25;
      DCOMP.COMP.GenTypeParameters((c).dtor_typeParams, out _out23, out _out24, out _out25);
      _70_typeParamsSet = _out23;
      _71_typeParams = _out24;
      _72_constrainedTypeParams = _out25;
      Dafny.ISequence<Dafny.Rune> _73_underlyingType;
      Dafny.ISequence<Dafny.Rune> _out26;
      _out26 = DCOMP.COMP.GenType((c).dtor_base, false, false);
      _73_underlyingType = _out26;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]\n#[repr(transparent)]\npub struct r#"), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(pub ")), _73_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _72_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyErasable for r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Erased = ")), _73_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn erase(&self) -> &Self::Erased {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn erase_owned(self) -> Self::Erased {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.0\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _72_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<")), _73_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase(x: &")), _73_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> &Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe { &*(x as *const ")), _73_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as *const r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") }\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase_owned(x: ")), _73_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(x)\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _72_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase(x: &r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> &Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase_owned(x: r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _72_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n"));
      DAST._IOptional<DAST._IExpression> _source4 = (c).dtor_witnessExpr;
      if (_source4.is_Some) {
        DAST._IExpression _74___mcc_h0 = _source4.dtor_Some_a0;
        DAST._IExpression _75_e = _74___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _76_eStr;
          bool _77___v7;
          bool _78___v8;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _79___v9;
          Dafny.ISequence<Dafny.Rune> _out27;
          bool _out28;
          bool _out29;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out30;
          DCOMP.COMP.GenExpr(_75_e, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out27, out _out28, out _out29, out _out30);
          _76_eStr = _out27;
          _77___v7 = _out28;
          _78___v8 = _out29;
          _79___v9 = _out30;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _76_eStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
        }
      } else {
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())\n"));
        }
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _72_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _71_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, __fmt_print_formatter, in_seq)\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenDatatype(DAST._IDatatype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _80_typeParamsSet;
      Dafny.ISequence<Dafny.Rune> _81_typeParams;
      Dafny.ISequence<Dafny.Rune> _82_constrainedTypeParams;
      Dafny.ISet<DAST._IType> _out31;
      Dafny.ISequence<Dafny.Rune> _out32;
      Dafny.ISequence<Dafny.Rune> _out33;
      DCOMP.COMP.GenTypeParameters((c).dtor_typeParams, out _out31, out _out32, out _out33);
      _80_typeParamsSet = _out31;
      _81_typeParams = _out32;
      _82_constrainedTypeParams = _out33;
      Dafny.ISequence<Dafny.Rune> _83_ctors;
      _83_ctors = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _84_i;
      _84_i = BigInteger.Zero;
      while ((_84_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _85_ctor;
        _85_ctor = ((c).dtor_ctors).Select(_84_i);
        Dafny.ISequence<Dafny.Rune> _86_ctorBody;
        _86_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_85_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        BigInteger _87_j;
        _87_j = BigInteger.Zero;
        while ((_87_j) < (new BigInteger(((_85_ctor).dtor_args).Count))) {
          DAST._IFormal _88_formal;
          _88_formal = ((_85_ctor).dtor_args).Select(_87_j);
          Dafny.ISequence<Dafny.Rune> _89_formalType;
          Dafny.ISequence<Dafny.Rune> _out34;
          _out34 = DCOMP.COMP.GenType((_88_formal).dtor_typ, false, false);
          _89_formalType = _out34;
          if ((c).dtor_isCo) {
            _86_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_86_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_88_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper<")), _89_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">, "));
          } else {
            _86_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_86_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_88_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _89_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          _87_j = (_87_j) + (BigInteger.One);
        }
        _86_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(_86_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        _83_ctors = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_83_ctors, _86_ctorBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
        _84_i = (_84_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _90_selfPath;
      _90_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _91_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _92_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out35;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out36;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_90_selfPath)), _80_typeParamsSet, out _out35, out _out36);
      _91_implBody = _out35;
      _92_traitBodies = _out36;
      _84_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _93_emittedFields;
      _93_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_84_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _94_ctor;
        _94_ctor = ((c).dtor_ctors).Select(_84_i);
        BigInteger _95_j;
        _95_j = BigInteger.Zero;
        while ((_95_j) < (new BigInteger(((_94_ctor).dtor_args).Count))) {
          DAST._IFormal _96_formal;
          _96_formal = ((_94_ctor).dtor_args).Select(_95_j);
          if (!((_93_emittedFields).Contains((_96_formal).dtor_name))) {
            _93_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_93_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_96_formal).dtor_name));
            Dafny.ISequence<Dafny.Rune> _97_formalType;
            Dafny.ISequence<Dafny.Rune> _out37;
            _out37 = DCOMP.COMP.GenType((_96_formal).dtor_typ, false, false);
            _97_formalType = _out37;
            Dafny.ISequence<Dafny.Rune> _98_methodBody;
            _98_methodBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n");
            BigInteger _99_k;
            _99_k = BigInteger.Zero;
            while ((_99_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _100_ctor2;
              _100_ctor2 = ((c).dtor_ctors).Select(_99_k);
              Dafny.ISequence<Dafny.Rune> _101_ctorMatch;
              _101_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_100_ctor2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              BigInteger _102_l;
              _102_l = BigInteger.Zero;
              bool _103_hasMatchingField;
              _103_hasMatchingField = false;
              while ((_102_l) < (new BigInteger(((_100_ctor2).dtor_args).Count))) {
                DAST._IFormal _104_formal2;
                _104_formal2 = ((_100_ctor2).dtor_args).Select(_102_l);
                if (((_96_formal).dtor_name).Equals((_104_formal2).dtor_name)) {
                  _103_hasMatchingField = true;
                }
                _101_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_101_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_104_formal2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _102_l = (_102_l) + (BigInteger.One);
              }
              if (_103_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _101_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_101_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ::std::ops::Deref::deref(&")), (_96_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0),\n"));
                } else {
                  _101_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_101_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ")), (_96_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
                }
              } else {
                _101_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_101_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => panic!(\"field does not exist on this variant\"),\n"));
              }
              _98_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_98_methodBody, _101_ctorMatch);
              _99_k = (_99_k) + (BigInteger.One);
            }
            _98_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_98_methodBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _91_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_91_implBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#")), (_96_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&self) -> &")), _97_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _98_methodBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
          }
          _95_j = (_95_j) + (BigInteger.One);
        }
        _84_i = (_84_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.Rune> _105_enumBody;
      _105_enumBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]\npub enum r#"), (c).dtor_name), _81_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _83_ctors), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _82_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" r#")), (c).dtor_name), _81_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _91_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      Dafny.ISequence<Dafny.Rune> _106_identEraseImpls;
      _106_identEraseImpls = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _82_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyErasable for r#")), (c).dtor_name), _81_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Erased = Self;\nfn erase(&self) -> &Self::Erased { self }\nfn erase_owned(self) -> Self::Erased { self }}\n"));
      _106_identEraseImpls = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_106_identEraseImpls, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _82_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<r#")), (c).dtor_name), _81_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _81_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn unerase(x: &Self) -> &Self { x }\nfn unerase_owned(x: Self) -> Self { x }}\n"));
      Dafny.ISequence<Dafny.Rune> _107_printImpl;
      _107_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _82_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _81_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n"));
      _84_i = BigInteger.Zero;
      while ((_84_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _108_ctor;
        _108_ctor = ((c).dtor_ctors).Select(_84_i);
        Dafny.ISequence<Dafny.Rune> _109_ctorMatch;
        _109_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_108_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _110_modulePrefix;
        _110_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _111_printRhs;
        _111_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(__fmt_print_formatter, \""), _110_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (_108_ctor).dtor_name), (((_108_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?;")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"))));
        BigInteger _112_j;
        _112_j = BigInteger.Zero;
        while ((_112_j) < (new BigInteger(((_108_ctor).dtor_args).Count))) {
          DAST._IFormal _113_formal;
          _113_formal = ((_108_ctor).dtor_args).Select(_112_j);
          _109_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_109_ctorMatch, (_113_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_112_j).Sign == 1) {
            _111_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_111_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \", \")?;"));
          }
          _111_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_111_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(")), (_113_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", __fmt_print_formatter, false)?;"));
          _112_j = (_112_j) + (BigInteger.One);
        }
        _109_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_109_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_108_ctor).dtor_hasAnyArgs) {
          _111_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_111_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \")\")?;"));
        }
        _111_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_111_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nOk(())"));
        _107_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_107_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _109_ctorMatch), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" => {\n")), _111_printRhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
        _84_i = (_84_i) + (BigInteger.One);
      }
      _107_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_107_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _114_defaultImpl;
      _114_defaultImpl = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _114_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _82_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _81_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
        _84_i = BigInteger.Zero;
        while ((_84_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _115_formal;
          _115_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_84_i);
          _114_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_114_defaultImpl, (_115_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": std::default::Default::default(),\n"));
          _84_i = (_84_i) + (BigInteger.One);
        }
        _114_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_114_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_105_enumBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _106_identEraseImpls), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _107_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _114_defaultImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((new BigInteger((p).Count)).Sign == 0) {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        return s;
      } else {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super::");
        BigInteger _116_i;
        _116_i = BigInteger.Zero;
        while ((_116_i) < (new BigInteger((p).Count))) {
          if ((_116_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), ((p).Select(_116_i)));
          _116_i = (_116_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((args).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _117_i;
        _117_i = BigInteger.Zero;
        while ((_117_i) < (new BigInteger((args).Count))) {
          if ((_117_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _118_genTp;
          Dafny.ISequence<Dafny.Rune> _out38;
          _out38 = DCOMP.COMP.GenType((args).Select(_117_i), inBinding, inFn);
          _118_genTp = _out38;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _118_genTp);
          _117_i = (_117_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenType(DAST._IType c, bool inBinding, bool inFn) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      DAST._IType _source5 = c;
      if (_source5.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _119___mcc_h0 = _source5.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _120___mcc_h1 = _source5.dtor_typeArgs;
        DAST._IResolvedType _121___mcc_h2 = _source5.dtor_resolved;
        DAST._IResolvedType _122_resolved = _121___mcc_h2;
        Dafny.ISequence<DAST._IType> _123_args = _120___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _124_p = _119___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _out39;
          _out39 = DCOMP.COMP.GenPath(_124_p);
          s = _out39;
          Dafny.ISequence<Dafny.Rune> _125_typeArgs;
          Dafny.ISequence<Dafny.Rune> _out40;
          _out40 = DCOMP.COMP.GenTypeArgs(_123_args, inBinding, inFn);
          _125_typeArgs = _out40;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _125_typeArgs);
          DAST._IResolvedType _source6 = _122_resolved;
          if (_source6.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _126___mcc_h16 = _source6.dtor_path;
            {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            }
          } else if (_source6.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _127___mcc_h18 = _source6.dtor_path;
            {
              if (inBinding) {
                s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_");
              } else {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              }
            }
          } else {
            DAST._IType _128___mcc_h20 = _source6.dtor_Newtype_a0;
            DAST._IResolvedType _129_Primitive = _122_resolved;
          }
        }
      } else if (_source5.is_Tuple) {
        Dafny.ISequence<DAST._IType> _130___mcc_h3 = _source5.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _131_types = _130___mcc_h3;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          BigInteger _132_i;
          _132_i = BigInteger.Zero;
          while ((_132_i) < (new BigInteger((_131_types).Count))) {
            if ((_132_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _133_generated;
            Dafny.ISequence<Dafny.Rune> _out41;
            _out41 = DCOMP.COMP.GenType((_131_types).Select(_132_i), inBinding, inFn);
            _133_generated = _out41;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _133_generated), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            _132_i = (_132_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else if (_source5.is_Array) {
        DAST._IType _134___mcc_h4 = _source5.dtor_element;
        DAST._IType _135_element = _134___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _136_elemStr;
          Dafny.ISequence<Dafny.Rune> _out42;
          _out42 = DCOMP.COMP.GenType(_135_element, inBinding, inFn);
          _136_elemStr = _out42;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::vec::Vec<"), _136_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Seq) {
        DAST._IType _137___mcc_h5 = _source5.dtor_element;
        DAST._IType _138_element = _137___mcc_h5;
        {
          Dafny.ISequence<Dafny.Rune> _139_elemStr;
          Dafny.ISequence<Dafny.Rune> _out43;
          _out43 = DCOMP.COMP.GenType(_138_element, inBinding, inFn);
          _139_elemStr = _out43;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::vec::Vec<"), _139_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Set) {
        DAST._IType _140___mcc_h6 = _source5.dtor_element;
        DAST._IType _141_element = _140___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _142_elemStr;
          Dafny.ISequence<Dafny.Rune> _out44;
          _out44 = DCOMP.COMP.GenType(_141_element, inBinding, inFn);
          _142_elemStr = _out44;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashSet<"), _142_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Multiset) {
        DAST._IType _143___mcc_h7 = _source5.dtor_element;
        DAST._IType _144_element = _143___mcc_h7;
        {
          Dafny.ISequence<Dafny.Rune> _145_elemStr;
          Dafny.ISequence<Dafny.Rune> _out45;
          _out45 = DCOMP.COMP.GenType(_144_element, inBinding, inFn);
          _145_elemStr = _out45;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _145_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", u64>"));
        }
      } else if (_source5.is_Map) {
        DAST._IType _146___mcc_h8 = _source5.dtor_key;
        DAST._IType _147___mcc_h9 = _source5.dtor_value;
        DAST._IType _148_value = _147___mcc_h9;
        DAST._IType _149_key = _146___mcc_h8;
        {
          Dafny.ISequence<Dafny.Rune> _150_keyStr;
          Dafny.ISequence<Dafny.Rune> _out46;
          _out46 = DCOMP.COMP.GenType(_149_key, inBinding, inFn);
          _150_keyStr = _out46;
          Dafny.ISequence<Dafny.Rune> _151_valueStr;
          Dafny.ISequence<Dafny.Rune> _out47;
          _out47 = DCOMP.COMP.GenType(_148_value, inBinding, inFn);
          _151_valueStr = _out47;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _150_keyStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _151_valueStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Arrow) {
        Dafny.ISequence<DAST._IType> _152___mcc_h10 = _source5.dtor_args;
        DAST._IType _153___mcc_h11 = _source5.dtor_result;
        DAST._IType _154_result = _153___mcc_h11;
        Dafny.ISequence<DAST._IType> _155_args = _152___mcc_h10;
        {
          if (inBinding) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<_>");
          } else {
            if (inFn) {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<::std::boxed::Box<dyn ::std::ops::Fn(");
            } else {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<impl ::std::ops::Fn(");
            }
            BigInteger _156_i;
            _156_i = BigInteger.Zero;
            while ((_156_i) < (new BigInteger((_155_args).Count))) {
              if ((_156_i).Sign == 1) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _157_generated;
              Dafny.ISequence<Dafny.Rune> _out48;
              _out48 = DCOMP.COMP.GenType((_155_args).Select(_156_i), inBinding, true);
              _157_generated = _out48;
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), _157_generated);
              _156_i = (_156_i) + (BigInteger.One);
            }
            Dafny.ISequence<Dafny.Rune> _158_resultType;
            Dafny.ISequence<Dafny.Rune> _out49;
            _out49 = DCOMP.COMP.GenType(_154_result, inBinding, inFn);
            _158_resultType = _out49;
            if (inFn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _158_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + 'static>>"));
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _158_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + Clone + 'static>"));
            }
          }
        }
      } else if (_source5.is_Primitive) {
        DAST._IPrimitive _159___mcc_h12 = _source5.dtor_Primitive_a0;
        DAST._IPrimitive _160_p = _159___mcc_h12;
        {
          DAST._IPrimitive _source7 = _160_p;
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
        Dafny.ISequence<Dafny.Rune> _161___mcc_h13 = _source5.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _162_v = _161___mcc_h13;
        s = _162_v;
      } else {
        Dafny.ISequence<Dafny.Rune> _163___mcc_h14 = _source5.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source8 = _163___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _164___mcc_h15 = _source8;
        Dafny.ISequence<Dafny.Rune> _165_name = _164___mcc_h15;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _165_name);
      }
      return s;
    }
    public static void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<Dafny.Rune> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> traitBodies) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _166_i;
      _166_i = BigInteger.Zero;
      while ((_166_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source9 = (body).Select(_166_i);
        DAST._IMethod _167___mcc_h0 = _source9;
        DAST._IMethod _168_m = _167___mcc_h0;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source10 = (_168_m).dtor_overridingPath;
          if (_source10.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _169___mcc_h1 = _source10.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _170_p = _169___mcc_h1;
            {
              Dafny.ISequence<Dafny.Rune> _171_existing;
              _171_existing = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              if ((traitBodies).Contains(_170_p)) {
                _171_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(traitBodies, _170_p);
              }
              if ((new BigInteger((_171_existing).Count)).Sign == 1) {
                _171_existing = Dafny.Sequence<Dafny.Rune>.Concat(_171_existing, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
              }
              Dafny.ISequence<Dafny.Rune> _172_genMethod;
              Dafny.ISequence<Dafny.Rune> _out50;
              _out50 = DCOMP.COMP.GenMethod(_168_m, true, enclosingType, enclosingTypeParams);
              _172_genMethod = _out50;
              _171_existing = Dafny.Sequence<Dafny.Rune>.Concat(_171_existing, _172_genMethod);
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>(_170_p, _171_existing)));
            }
          } else {
            {
              Dafny.ISequence<Dafny.Rune> _173_generated;
              Dafny.ISequence<Dafny.Rune> _out51;
              _out51 = DCOMP.COMP.GenMethod(_168_m, forTrait, enclosingType, enclosingTypeParams);
              _173_generated = _out51;
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, _173_generated);
            }
          }
        }
        if ((new BigInteger((s).Count)).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        _166_i = (_166_i) + (BigInteger.One);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GenParams(Dafny.ISequence<DAST._IFormal> @params) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _174_i;
      _174_i = BigInteger.Zero;
      while ((_174_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _175_param;
        _175_param = (@params).Select(_174_i);
        Dafny.ISequence<Dafny.Rune> _176_paramType;
        Dafny.ISequence<Dafny.Rune> _out52;
        _out52 = DCOMP.COMP.GenType((_175_param).dtor_typ, false, false);
        _176_paramType = _out52;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_175_param).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _176_paramType);
        if ((_174_i) < ((new BigInteger((@params).Count)) - (BigInteger.One))) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        _174_i = (_174_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _177_params;
      Dafny.ISequence<Dafny.Rune> _out53;
      _out53 = DCOMP.COMP.GenParams((m).dtor_params);
      _177_params = _out53;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _178_paramNames;
      _178_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _179_paramI;
      _179_paramI = BigInteger.Zero;
      while ((_179_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _178_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_178_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_179_paramI)).dtor_name));
        _179_paramI = (_179_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _177_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _177_params);
        } else {
          Dafny.ISequence<Dafny.Rune> _180_enclosingTypeString;
          Dafny.ISequence<Dafny.Rune> _out54;
          _out54 = DCOMP.COMP.GenType(enclosingType, false, false);
          _180_enclosingTypeString = _out54;
          _177_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self: &"), _180_enclosingTypeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _177_params);
        }
      }
      Dafny.ISequence<Dafny.Rune> _181_retType;
      _181_retType = (((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      BigInteger _182_typeI;
      _182_typeI = BigInteger.Zero;
      while ((_182_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        if ((_182_typeI).Sign == 1) {
          _181_retType = Dafny.Sequence<Dafny.Rune>.Concat(_181_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        Dafny.ISequence<Dafny.Rune> _183_typeString;
        Dafny.ISequence<Dafny.Rune> _out55;
        _out55 = DCOMP.COMP.GenType(((m).dtor_outTypes).Select(_182_typeI), false, false);
        _183_typeString = _out55;
        _181_retType = Dafny.Sequence<Dafny.Rune>.Concat(_181_retType, _183_typeString);
        _182_typeI = (_182_typeI) + (BigInteger.One);
      }
      if ((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) {
        _181_retType = Dafny.Sequence<Dafny.Rune>.Concat(_181_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      if (forTrait) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn r#"), (m).dtor_name);
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#"), (m).dtor_name);
      }
      Dafny.ISequence<DAST._IType> _184_typeParamsFiltered;
      _184_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _185_typeParamI;
      _185_typeParamI = BigInteger.Zero;
      while ((_185_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _186_typeParam;
        _186_typeParam = ((m).dtor_typeParams).Select(_185_typeParamI);
        if (!((enclosingTypeParams).Contains(_186_typeParam))) {
          _184_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_184_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_186_typeParam));
        }
        _185_typeParamI = (_185_typeParamI) + (BigInteger.One);
      }
      if ((new BigInteger((_184_typeParamsFiltered).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _187_i;
        _187_i = BigInteger.Zero;
        while ((_187_i) < (new BigInteger((_184_typeParamsFiltered).Count))) {
          if ((_187_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _188_typeString;
          Dafny.ISequence<Dafny.Rune> _out56;
          _out56 = DCOMP.COMP.GenType((_184_typeParamsFiltered).Select(_187_i), false, false);
          _188_typeString = _out56;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _188_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<")), _188_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> + Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _187_i = (_187_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _177_params), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _181_retType);
      if ((m).dtor_hasBody) {
        Dafny.ISequence<Dafny.Rune> _189_earlyReturn;
        _189_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return;");
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source11 = (m).dtor_outVars;
        if (_source11.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _190___mcc_h0 = _source11.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _191_outVars = _190___mcc_h0;
          {
            _189_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return (");
            BigInteger _192_outI;
            _192_outI = BigInteger.Zero;
            while ((_192_outI) < (new BigInteger((_191_outVars).Count))) {
              if ((_192_outI).Sign == 1) {
                _189_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_189_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _193_outVar;
              _193_outVar = (_191_outVars).Select(_192_outI);
              _189_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_189_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_193_outVar));
              _192_outI = (_192_outI) + (BigInteger.One);
            }
            _189_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_189_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
          }
        } else {
        }
        Dafny.ISequence<Dafny.Rune> _194_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _195___v12;
        Dafny.ISequence<Dafny.Rune> _out57;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out58;
        DCOMP.COMP.GenStmts((m).dtor_body, _178_paramNames, true, _189_earlyReturn, out _out57, out _out58);
        _194_body = _out57;
        _195___v12 = _out58;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source12 = (m).dtor_outVars;
        if (_source12.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _196___mcc_h1 = _source12.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _197_outVars = _196___mcc_h1;
          {
            _194_body = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_194_body, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _189_earlyReturn);
          }
        } else {
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _194_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
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
      BigInteger _198_i;
      _198_i = BigInteger.Zero;
      while ((_198_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _199_stmt;
        _199_stmt = (stmts).Select(_198_i);
        Dafny.ISequence<Dafny.Rune> _200_stmtString;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _201_recIdents;
        Dafny.ISequence<Dafny.Rune> _out59;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out60;
        DCOMP.COMP.GenStmt(_199_stmt, @params, (isLast) && ((_198_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out59, out _out60);
        _200_stmtString = _out59;
        _201_recIdents = _out60;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _201_recIdents);
        if ((_198_i).Sign == 1) {
          generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, _200_stmtString);
        _198_i = (_198_i) + (BigInteger.One);
      }
    }
    public static void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source13 = lhs;
      if (_source13.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _202___mcc_h0 = _source13.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source14 = _202___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _203___mcc_h1 = _source14;
        Dafny.ISequence<Dafny.Rune> _204_id = _203___mcc_h1;
        {
          if ((@params).Contains(_204_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*r#"), _204_id);
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _204_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_204_id);
          needsIIFE = false;
        }
      } else {
        DAST._IExpression _205___mcc_h2 = _source13.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _206___mcc_h3 = _source13.dtor_field;
        Dafny.ISequence<Dafny.Rune> _207_field = _206___mcc_h3;
        DAST._IExpression _208_on = _205___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _209_onExpr;
          bool _210_onOwned;
          bool _211_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _212_recIdents;
          Dafny.ISequence<Dafny.Rune> _out61;
          bool _out62;
          bool _out63;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out64;
          DCOMP.COMP.GenExpr(_208_on, @params, false, out _out61, out _out62, out _out63, out _out64);
          _209_onExpr = _out61;
          _210_onOwned = _out62;
          _211_onErased = _out63;
          _212_recIdents = _out64;
          if (!(_211_onErased)) {
            Dafny.ISequence<Dafny.Rune> _213_eraseFn;
            _213_eraseFn = ((_210_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _209_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _213_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _209_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), _209_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _207_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut())"));
          readIdents = _212_recIdents;
          needsIIFE = true;
        }
      }
    }
    public static void GenStmt(DAST._IStatement stmt, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, Dafny.ISequence<Dafny.Rune> earlyReturn, out Dafny.ISequence<Dafny.Rune> generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IStatement _source15 = stmt;
      if (_source15.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _214___mcc_h0 = _source15.dtor_name;
        DAST._IType _215___mcc_h1 = _source15.dtor_typ;
        DAST._IOptional<DAST._IExpression> _216___mcc_h2 = _source15.dtor_maybeValue;
        DAST._IOptional<DAST._IExpression> _source16 = _216___mcc_h2;
        if (_source16.is_Some) {
          DAST._IExpression _217___mcc_h3 = _source16.dtor_Some_a0;
          DAST._IExpression _218_expression = _217___mcc_h3;
          DAST._IType _219_typ = _215___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _220_name = _214___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _221_expr;
            bool _222___v13;
            bool _223_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _224_recIdents;
            Dafny.ISequence<Dafny.Rune> _out65;
            bool _out66;
            bool _out67;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out68;
            DCOMP.COMP.GenExpr(_218_expression, @params, true, out _out65, out _out66, out _out67, out _out68);
            _221_expr = _out65;
            _222___v13 = _out66;
            _223_recErased = _out67;
            _224_recIdents = _out68;
            if (_223_recErased) {
              _221_expr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _221_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            Dafny.ISequence<Dafny.Rune> _225_typeString;
            Dafny.ISequence<Dafny.Rune> _out69;
            _out69 = DCOMP.COMP.GenType(_219_typ, true, false);
            _225_typeString = _out69;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _220_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _225_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _221_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = _224_recIdents;
          }
        } else {
          DAST._IType _226_typ = _215___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _227_name = _214___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _228_typeString;
            Dafny.ISequence<Dafny.Rune> _out70;
            _out70 = DCOMP.COMP.GenType(_226_typ, true, false);
            _228_typeString = _out70;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _227_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _228_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source15.is_Assign) {
        DAST._IAssignLhs _229___mcc_h4 = _source15.dtor_lhs;
        DAST._IExpression _230___mcc_h5 = _source15.dtor_value;
        DAST._IExpression _231_expression = _230___mcc_h5;
        DAST._IAssignLhs _232_lhs = _229___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _233_lhsGen;
          bool _234_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _235_recIdents;
          Dafny.ISequence<Dafny.Rune> _out71;
          bool _out72;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out73;
          DCOMP.COMP.GenAssignLhs(_232_lhs, @params, out _out71, out _out72, out _out73);
          _233_lhsGen = _out71;
          _234_needsIIFE = _out72;
          _235_recIdents = _out73;
          Dafny.ISequence<Dafny.Rune> _236_exprGen;
          bool _237___v14;
          bool _238_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _239_exprIdents;
          Dafny.ISequence<Dafny.Rune> _out74;
          bool _out75;
          bool _out76;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out77;
          DCOMP.COMP.GenExpr(_231_expression, @params, true, out _out74, out _out75, out _out76, out _out77);
          _236_exprGen = _out74;
          _237___v14 = _out75;
          _238_exprErased = _out76;
          _239_exprIdents = _out77;
          if (_238_exprErased) {
            _236_exprGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _236_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (_234_needsIIFE) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ let __rhs = "), _236_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; ")), _233_lhsGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = __rhs; }"));
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_233_lhsGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _236_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_235_recIdents, _239_exprIdents);
        }
      } else if (_source15.is_If) {
        DAST._IExpression _240___mcc_h6 = _source15.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _241___mcc_h7 = _source15.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _242___mcc_h8 = _source15.dtor_els;
        Dafny.ISequence<DAST._IStatement> _243_els = _242___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _244_thn = _241___mcc_h7;
        DAST._IExpression _245_cond = _240___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _246_condString;
          bool _247___v15;
          bool _248_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _249_recIdents;
          Dafny.ISequence<Dafny.Rune> _out78;
          bool _out79;
          bool _out80;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out81;
          DCOMP.COMP.GenExpr(_245_cond, @params, true, out _out78, out _out79, out _out80, out _out81);
          _246_condString = _out78;
          _247___v15 = _out79;
          _248_condErased = _out80;
          _249_recIdents = _out81;
          if (!(_248_condErased)) {
            _246_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _246_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _249_recIdents;
          Dafny.ISequence<Dafny.Rune> _250_thnString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _251_thnIdents;
          Dafny.ISequence<Dafny.Rune> _out82;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out83;
          DCOMP.COMP.GenStmts(_244_thn, @params, isLast, earlyReturn, out _out82, out _out83);
          _250_thnString = _out82;
          _251_thnIdents = _out83;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _251_thnIdents);
          Dafny.ISequence<Dafny.Rune> _252_elsString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _253_elsIdents;
          Dafny.ISequence<Dafny.Rune> _out84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out85;
          DCOMP.COMP.GenStmts(_243_els, @params, isLast, earlyReturn, out _out84, out _out85);
          _252_elsString = _out84;
          _253_elsIdents = _out85;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _253_elsIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), _246_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _250_thnString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _252_elsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_While) {
        DAST._IExpression _254___mcc_h9 = _source15.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _255___mcc_h10 = _source15.dtor_body;
        Dafny.ISequence<DAST._IStatement> _256_body = _255___mcc_h10;
        DAST._IExpression _257_cond = _254___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _258_condString;
          bool _259___v16;
          bool _260_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _261_recIdents;
          Dafny.ISequence<Dafny.Rune> _out86;
          bool _out87;
          bool _out88;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out89;
          DCOMP.COMP.GenExpr(_257_cond, @params, true, out _out86, out _out87, out _out88, out _out89);
          _258_condString = _out86;
          _259___v16 = _out87;
          _260_condErased = _out88;
          _261_recIdents = _out89;
          if (!(_260_condErased)) {
            _258_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase("), _258_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _261_recIdents;
          Dafny.ISequence<Dafny.Rune> _262_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _263_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out90;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out91;
          DCOMP.COMP.GenStmts(_256_body, @params, false, earlyReturn, out _out90, out _out91);
          _262_bodyString = _out90;
          _263_bodyIdents = _out91;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _263_bodyIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), _258_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _262_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_Call) {
        DAST._IExpression _264___mcc_h11 = _source15.dtor_on;
        Dafny.ISequence<Dafny.Rune> _265___mcc_h12 = _source15.dtor_name;
        Dafny.ISequence<DAST._IType> _266___mcc_h13 = _source15.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _267___mcc_h14 = _source15.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _268___mcc_h15 = _source15.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _269_maybeOutVars = _268___mcc_h15;
        Dafny.ISequence<DAST._IExpression> _270_args = _267___mcc_h14;
        Dafny.ISequence<DAST._IType> _271_typeArgs = _266___mcc_h13;
        Dafny.ISequence<Dafny.Rune> _272_name = _265___mcc_h12;
        DAST._IExpression _273_on = _264___mcc_h11;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _274_typeArgString;
          _274_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_271_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _275_typeI;
            _275_typeI = BigInteger.Zero;
            _274_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_275_typeI) < (new BigInteger((_271_typeArgs).Count))) {
              if ((_275_typeI).Sign == 1) {
                _274_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_274_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _276_typeString;
              Dafny.ISequence<Dafny.Rune> _out92;
              _out92 = DCOMP.COMP.GenType((_271_typeArgs).Select(_275_typeI), false, false);
              _276_typeString = _out92;
              _274_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_274_typeArgString, _276_typeString);
              _275_typeI = (_275_typeI) + (BigInteger.One);
            }
            _274_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_274_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _277_argString;
          _277_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _278_i;
          _278_i = BigInteger.Zero;
          while ((_278_i) < (new BigInteger((_270_args).Count))) {
            if ((_278_i).Sign == 1) {
              _277_argString = Dafny.Sequence<Dafny.Rune>.Concat(_277_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _279_argExpr;
            bool _280_isOwned;
            bool _281_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _282_argIdents;
            Dafny.ISequence<Dafny.Rune> _out93;
            bool _out94;
            bool _out95;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
            DCOMP.COMP.GenExpr((_270_args).Select(_278_i), @params, false, out _out93, out _out94, out _out95, out _out96);
            _279_argExpr = _out93;
            _280_isOwned = _out94;
            _281_argErased = _out95;
            _282_argIdents = _out96;
            if (_280_isOwned) {
              _279_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _279_argExpr);
            }
            _277_argString = Dafny.Sequence<Dafny.Rune>.Concat(_277_argString, _279_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _282_argIdents);
            _278_i = (_278_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _283_enclosingString;
          bool _284___v17;
          bool _285___v18;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _286_enclosingIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          bool _out98;
          bool _out99;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
          DCOMP.COMP.GenExpr(_273_on, @params, false, out _out97, out _out98, out _out99, out _out100);
          _283_enclosingString = _out97;
          _284___v17 = _out98;
          _285___v18 = _out99;
          _286_enclosingIdents = _out100;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _286_enclosingIdents);
          DAST._IExpression _source17 = _273_on;
          if (_source17.is_Literal) {
            DAST._ILiteral _287___mcc_h18 = _source17.dtor_Literal_a0;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _288___mcc_h20 = _source17.dtor_Ident_a0;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _289___mcc_h22 = _source17.dtor_Companion_a0;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_283_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source17.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _290___mcc_h24 = _source17.dtor_Tuple_a0;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _291___mcc_h26 = _source17.dtor_path;
            Dafny.ISequence<DAST._IExpression> _292___mcc_h27 = _source17.dtor_args;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _293___mcc_h30 = _source17.dtor_dims;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _294___mcc_h32 = _source17.dtor_path;
            Dafny.ISequence<Dafny.Rune> _295___mcc_h33 = _source17.dtor_variant;
            bool _296___mcc_h34 = _source17.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _297___mcc_h35 = _source17.dtor_contents;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Convert) {
            DAST._IExpression _298___mcc_h40 = _source17.dtor_value;
            DAST._IType _299___mcc_h41 = _source17.dtor_from;
            DAST._IType _300___mcc_h42 = _source17.dtor_typ;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _301___mcc_h46 = _source17.dtor_elements;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _302___mcc_h48 = _source17.dtor_elements;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_This) {
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Ite) {
            DAST._IExpression _303___mcc_h50 = _source17.dtor_cond;
            DAST._IExpression _304___mcc_h51 = _source17.dtor_thn;
            DAST._IExpression _305___mcc_h52 = _source17.dtor_els;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_UnOp) {
            DAST._IUnaryOp _306___mcc_h56 = _source17.dtor_unOp;
            DAST._IExpression _307___mcc_h57 = _source17.dtor_expr;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _308___mcc_h60 = _source17.dtor_op;
            DAST._IExpression _309___mcc_h61 = _source17.dtor_left;
            DAST._IExpression _310___mcc_h62 = _source17.dtor_right;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Select) {
            DAST._IExpression _311___mcc_h66 = _source17.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _312___mcc_h67 = _source17.dtor_field;
            bool _313___mcc_h68 = _source17.dtor_isConstant;
            bool _314___mcc_h69 = _source17.dtor_onDatatype;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SelectFn) {
            DAST._IExpression _315___mcc_h74 = _source17.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _316___mcc_h75 = _source17.dtor_field;
            bool _317___mcc_h76 = _source17.dtor_onDatatype;
            bool _318___mcc_h77 = _source17.dtor_isStatic;
            BigInteger _319___mcc_h78 = _source17.dtor_arity;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_TupleSelect) {
            DAST._IExpression _320___mcc_h84 = _source17.dtor_expr;
            BigInteger _321___mcc_h85 = _source17.dtor_index;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Call) {
            DAST._IExpression _322___mcc_h88 = _source17.dtor_on;
            Dafny.ISequence<Dafny.Rune> _323___mcc_h89 = _source17.dtor_name;
            Dafny.ISequence<DAST._IType> _324___mcc_h90 = _source17.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _325___mcc_h91 = _source17.dtor_args;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _326___mcc_h96 = _source17.dtor_params;
            DAST._IType _327___mcc_h97 = _source17.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _328___mcc_h98 = _source17.dtor_body;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _329___mcc_h102 = _source17.dtor_name;
            DAST._IType _330___mcc_h103 = _source17.dtor_typ;
            DAST._IExpression _331___mcc_h104 = _source17.dtor_value;
            DAST._IExpression _332___mcc_h105 = _source17.dtor_iifeBody;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Apply) {
            DAST._IExpression _333___mcc_h110 = _source17.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _334___mcc_h111 = _source17.dtor_args;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_TypeTest) {
            DAST._IExpression _335___mcc_h114 = _source17.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _336___mcc_h115 = _source17.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _337___mcc_h116 = _source17.dtor_variant;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _338___mcc_h120 = _source17.dtor_typ;
            {
              _283_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _339_receiver;
          _339_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source18 = _269_maybeOutVars;
          if (_source18.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _340___mcc_h122 = _source18.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _341_outVars = _340___mcc_h122;
            {
              if ((new BigInteger((_341_outVars).Count)) > (BigInteger.One)) {
                _339_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _342_outI;
              _342_outI = BigInteger.Zero;
              while ((_342_outI) < (new BigInteger((_341_outVars).Count))) {
                if ((_342_outI).Sign == 1) {
                  _339_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_339_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _343_outVar;
                _343_outVar = (_341_outVars).Select(_342_outI);
                _339_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_339_receiver, (_343_outVar));
                _342_outI = (_342_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_341_outVars).Count)) > (BigInteger.One)) {
                _339_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_339_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_339_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_339_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _283_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _272_name), _274_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _277_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source15.is_Return) {
        DAST._IExpression _344___mcc_h16 = _source15.dtor_expr;
        DAST._IExpression _345_expr = _344___mcc_h16;
        {
          Dafny.ISequence<Dafny.Rune> _346_exprString;
          bool _347___v21;
          bool _348_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _349_recIdents;
          Dafny.ISequence<Dafny.Rune> _out101;
          bool _out102;
          bool _out103;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out104;
          DCOMP.COMP.GenExpr(_345_expr, @params, true, out _out101, out _out102, out _out103, out _out104);
          _346_exprString = _out101;
          _347___v21 = _out102;
          _348_recErased = _out103;
          _349_recIdents = _out104;
          _346_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _346_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _349_recIdents;
          if (isLast) {
            generated = _346_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _346_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
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
        DAST._IExpression _350___mcc_h17 = _source15.dtor_Print_a0;
        DAST._IExpression _351_e = _350___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _352_printedExpr;
          bool _353_isOwned;
          bool _354___v22;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _355_recIdents;
          Dafny.ISequence<Dafny.Rune> _out105;
          bool _out106;
          bool _out107;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out108;
          DCOMP.COMP.GenExpr(_351_e, @params, false, out _out105, out _out106, out _out107, out _out108);
          _352_printedExpr = _out105;
          _353_isOwned = _out106;
          _354___v22 = _out107;
          _355_recIdents = _out108;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_353_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _352_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _355_recIdents;
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
        DAST._ILiteral _356___mcc_h0 = _source19.dtor_Literal_a0;
        DAST._ILiteral _source20 = _356___mcc_h0;
        if (_source20.is_BoolLiteral) {
          bool _357___mcc_h1 = _source20.dtor_BoolLiteral_a0;
          if ((_357___mcc_h1) == (false)) {
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
          Dafny.ISequence<Dafny.Rune> _358___mcc_h2 = _source20.dtor_IntLiteral_a0;
          DAST._IType _359___mcc_h3 = _source20.dtor_IntLiteral_a1;
          DAST._IType _360_t = _359___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _361_i = _358___mcc_h2;
          {
            DAST._IType _source21 = _360_t;
            if (_source21.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _362___mcc_h60 = _source21.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _363___mcc_h61 = _source21.dtor_typeArgs;
              DAST._IResolvedType _364___mcc_h62 = _source21.dtor_resolved;
              {
                s = _361_i;
              }
            } else if (_source21.is_Tuple) {
              Dafny.ISequence<DAST._IType> _365___mcc_h66 = _source21.dtor_Tuple_a0;
              {
                s = _361_i;
              }
            } else if (_source21.is_Array) {
              DAST._IType _366___mcc_h68 = _source21.dtor_element;
              {
                s = _361_i;
              }
            } else if (_source21.is_Seq) {
              DAST._IType _367___mcc_h70 = _source21.dtor_element;
              {
                s = _361_i;
              }
            } else if (_source21.is_Set) {
              DAST._IType _368___mcc_h72 = _source21.dtor_element;
              {
                s = _361_i;
              }
            } else if (_source21.is_Multiset) {
              DAST._IType _369___mcc_h74 = _source21.dtor_element;
              {
                s = _361_i;
              }
            } else if (_source21.is_Map) {
              DAST._IType _370___mcc_h76 = _source21.dtor_key;
              DAST._IType _371___mcc_h77 = _source21.dtor_value;
              {
                s = _361_i;
              }
            } else if (_source21.is_Arrow) {
              Dafny.ISequence<DAST._IType> _372___mcc_h80 = _source21.dtor_args;
              DAST._IType _373___mcc_h81 = _source21.dtor_result;
              {
                s = _361_i;
              }
            } else if (_source21.is_Primitive) {
              DAST._IPrimitive _374___mcc_h84 = _source21.dtor_Primitive_a0;
              DAST._IPrimitive _source22 = _374___mcc_h84;
              if (_source22.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _361_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source22.is_Real) {
                {
                  s = _361_i;
                }
              } else if (_source22.is_String) {
                {
                  s = _361_i;
                }
              } else if (_source22.is_Bool) {
                {
                  s = _361_i;
                }
              } else {
                {
                  s = _361_i;
                }
              }
            } else if (_source21.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _375___mcc_h86 = _source21.dtor_Passthrough_a0;
              {
                s = _361_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _376___mcc_h88 = _source21.dtor_TypeArg_a0;
              {
                s = _361_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _377___mcc_h4 = _source20.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _378___mcc_h5 = _source20.dtor_DecLiteral_a1;
          DAST._IType _379___mcc_h6 = _source20.dtor_DecLiteral_a2;
          DAST._IType _380_t = _379___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _381_d = _378___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _382_n = _377___mcc_h4;
          {
            DAST._IType _source23 = _380_t;
            if (_source23.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _383___mcc_h90 = _source23.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _384___mcc_h91 = _source23.dtor_typeArgs;
              DAST._IResolvedType _385___mcc_h92 = _source23.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Tuple) {
              Dafny.ISequence<DAST._IType> _386___mcc_h96 = _source23.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Array) {
              DAST._IType _387___mcc_h98 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Seq) {
              DAST._IType _388___mcc_h100 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Set) {
              DAST._IType _389___mcc_h102 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Multiset) {
              DAST._IType _390___mcc_h104 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Map) {
              DAST._IType _391___mcc_h106 = _source23.dtor_key;
              DAST._IType _392___mcc_h107 = _source23.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Arrow) {
              Dafny.ISequence<DAST._IType> _393___mcc_h110 = _source23.dtor_args;
              DAST._IType _394___mcc_h111 = _source23.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Primitive) {
              DAST._IPrimitive _395___mcc_h114 = _source23.dtor_Primitive_a0;
              DAST._IPrimitive _source24 = _395___mcc_h114;
              if (_source24.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source24.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _382_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source24.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source24.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source23.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _396___mcc_h116 = _source23.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _397___mcc_h118 = _source23.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_382_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _381_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _398___mcc_h7 = _source20.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _399_l = _398___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _399_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_CharLiteral) {
          Dafny.Rune _400___mcc_h8 = _source20.dtor_CharLiteral_a0;
          Dafny.Rune _401_c = _400___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_401_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
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
        Dafny.ISequence<Dafny.Rune> _402___mcc_h9 = _source19.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _403_name = _402___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _403_name);
          if (!((@params).Contains(_403_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_403_name);
        }
      } else if (_source19.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _404___mcc_h10 = _source19.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _405_path = _404___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out109;
          _out109 = DCOMP.COMP.GenPath(_405_path);
          s = _out109;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source19.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _406___mcc_h11 = _source19.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _407_values = _406___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _408_i;
          _408_i = BigInteger.Zero;
          bool _409_allErased;
          _409_allErased = true;
          while ((_408_i) < (new BigInteger((_407_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _410___v25;
            bool _411___v26;
            bool _412_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _413___v27;
            Dafny.ISequence<Dafny.Rune> _out110;
            bool _out111;
            bool _out112;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
            DCOMP.COMP.GenExpr((_407_values).Select(_408_i), @params, true, out _out110, out _out111, out _out112, out _out113);
            _410___v25 = _out110;
            _411___v26 = _out111;
            _412_isErased = _out112;
            _413___v27 = _out113;
            _409_allErased = (_409_allErased) && (_412_isErased);
            _408_i = (_408_i) + (BigInteger.One);
          }
          _408_i = BigInteger.Zero;
          while ((_408_i) < (new BigInteger((_407_values).Count))) {
            if ((_408_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _414_recursiveGen;
            bool _415___v28;
            bool _416_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _417_recIdents;
            Dafny.ISequence<Dafny.Rune> _out114;
            bool _out115;
            bool _out116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
            DCOMP.COMP.GenExpr((_407_values).Select(_408_i), @params, true, out _out114, out _out115, out _out116, out _out117);
            _414_recursiveGen = _out114;
            _415___v28 = _out115;
            _416_isErased = _out116;
            _417_recIdents = _out117;
            if ((_416_isErased) && (!(_409_allErased))) {
              _414_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _414_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _414_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _417_recIdents);
            _408_i = (_408_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _409_allErased;
        }
      } else if (_source19.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _418___mcc_h12 = _source19.dtor_path;
        Dafny.ISequence<DAST._IExpression> _419___mcc_h13 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _420_args = _419___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _421_path = _418___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _422_path;
          Dafny.ISequence<Dafny.Rune> _out118;
          _out118 = DCOMP.COMP.GenPath(_421_path);
          _422_path = _out118;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _422_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _423_i;
          _423_i = BigInteger.Zero;
          while ((_423_i) < (new BigInteger((_420_args).Count))) {
            if ((_423_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _424_recursiveGen;
            bool _425___v29;
            bool _426_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _427_recIdents;
            Dafny.ISequence<Dafny.Rune> _out119;
            bool _out120;
            bool _out121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
            DCOMP.COMP.GenExpr((_420_args).Select(_423_i), @params, true, out _out119, out _out120, out _out121, out _out122);
            _424_recursiveGen = _out119;
            _425___v29 = _out120;
            _426_isErased = _out121;
            _427_recIdents = _out122;
            if (_426_isErased) {
              _424_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _424_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _424_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _427_recIdents);
            _423_i = (_423_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _428___mcc_h14 = _source19.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _429_dims = _428___mcc_h14;
        {
          BigInteger _430_i;
          _430_i = (new BigInteger((_429_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_430_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _431_recursiveGen;
            bool _432___v30;
            bool _433_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _434_recIdents;
            Dafny.ISequence<Dafny.Rune> _out123;
            bool _out124;
            bool _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            DCOMP.COMP.GenExpr((_429_dims).Select(_430_i), @params, true, out _out123, out _out124, out _out125, out _out126);
            _431_recursiveGen = _out123;
            _432___v30 = _out124;
            _433_isErased = _out125;
            _434_recIdents = _out126;
            if (!(_433_isErased)) {
              _431_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _431_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _431_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _434_recIdents);
            _430_i = (_430_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _435___mcc_h15 = _source19.dtor_path;
        Dafny.ISequence<Dafny.Rune> _436___mcc_h16 = _source19.dtor_variant;
        bool _437___mcc_h17 = _source19.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _438___mcc_h18 = _source19.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _439_values = _438___mcc_h18;
        bool _440_isCo = _437___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _441_variant = _436___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _442_path = _435___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _443_path;
          Dafny.ISequence<Dafny.Rune> _out127;
          _out127 = DCOMP.COMP.GenPath(_442_path);
          _443_path = _out127;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _443_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _441_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _444_i;
          _444_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_444_i) < (new BigInteger((_439_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_439_values).Select(_444_i);
            Dafny.ISequence<Dafny.Rune> _445_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _446_value = _let_tmp_rhs0.dtor__1;
            if ((_444_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_440_isCo) {
              Dafny.ISequence<Dafny.Rune> _447_recursiveGen;
              bool _448___v31;
              bool _449_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _450_recIdents;
              Dafny.ISequence<Dafny.Rune> _out128;
              bool _out129;
              bool _out130;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
              DCOMP.COMP.GenExpr(_446_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out128, out _out129, out _out130, out _out131);
              _447_recursiveGen = _out128;
              _448___v31 = _out129;
              _449_isErased = _out130;
              _450_recIdents = _out131;
              if (!(_449_isErased)) {
                _447_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _447_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _447_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _447_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _450_recIdents);
              Dafny.ISequence<Dafny.Rune> _451_allReadCloned;
              _451_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_450_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _452_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_450_recIdents).Elements) {
                  _452_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_450_recIdents).Contains(_452_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1053)");
              after__ASSIGN_SUCH_THAT_0:;
                _451_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _452_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _452_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _450_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_450_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_452_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _445_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _451_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _447_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _453_recursiveGen;
              bool _454___v32;
              bool _455_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _456_recIdents;
              Dafny.ISequence<Dafny.Rune> _out132;
              bool _out133;
              bool _out134;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
              DCOMP.COMP.GenExpr(_446_value, @params, true, out _out132, out _out133, out _out134, out _out135);
              _453_recursiveGen = _out132;
              _454___v32 = _out133;
              _455_isErased = _out134;
              _456_recIdents = _out135;
              if (!(_455_isErased)) {
                _453_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _453_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _453_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _453_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _445_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _453_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _456_recIdents);
            }
            _444_i = (_444_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_Convert) {
        DAST._IExpression _457___mcc_h19 = _source19.dtor_value;
        DAST._IType _458___mcc_h20 = _source19.dtor_from;
        DAST._IType _459___mcc_h21 = _source19.dtor_typ;
        DAST._IType _460_toTpe = _459___mcc_h21;
        DAST._IType _461_fromTpe = _458___mcc_h20;
        DAST._IExpression _462_expr = _457___mcc_h19;
        {
          if (object.Equals(_461_fromTpe, _460_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _463_recursiveGen;
            bool _464_recOwned;
            bool _465_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _466_recIdents;
            Dafny.ISequence<Dafny.Rune> _out136;
            bool _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out136, out _out137, out _out138, out _out139);
            _463_recursiveGen = _out136;
            _464_recOwned = _out137;
            _465_recErased = _out138;
            _466_recIdents = _out139;
            s = _463_recursiveGen;
            isOwned = _464_recOwned;
            isErased = _465_recErased;
            readIdents = _466_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source25 = _System.Tuple2<DAST._IType, DAST._IType>.create(_461_fromTpe, _460_toTpe);
            DAST._IType _467___mcc_h120 = _source25.dtor__0;
            DAST._IType _468___mcc_h121 = _source25.dtor__1;
            DAST._IType _source26 = _467___mcc_h120;
            if (_source26.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _469___mcc_h124 = _source26.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _470___mcc_h125 = _source26.dtor_typeArgs;
              DAST._IResolvedType _471___mcc_h126 = _source26.dtor_resolved;
              DAST._IResolvedType _source27 = _471___mcc_h126;
              if (_source27.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _472___mcc_h133 = _source27.dtor_path;
                DAST._IType _source28 = _468___mcc_h121;
                if (_source28.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _473___mcc_h136 = _source28.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _474___mcc_h137 = _source28.dtor_typeArgs;
                  DAST._IResolvedType _475___mcc_h138 = _source28.dtor_resolved;
                  DAST._IResolvedType _source29 = _475___mcc_h138;
                  if (_source29.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _476___mcc_h142 = _source29.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _477_recursiveGen;
                      bool _478_recOwned;
                      bool _479_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _480_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out140;
                      bool _out141;
                      bool _out142;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out140, out _out141, out _out142, out _out143);
                      _477_recursiveGen = _out140;
                      _478_recOwned = _out141;
                      _479_recErased = _out142;
                      _480_recIdents = _out143;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _477_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _478_recOwned;
                      isErased = _479_recErased;
                      readIdents = _480_recIdents;
                    }
                  } else if (_source29.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _481___mcc_h144 = _source29.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _482_recursiveGen;
                      bool _483_recOwned;
                      bool _484_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _485_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out144;
                      bool _out145;
                      bool _out146;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out144, out _out145, out _out146, out _out147);
                      _482_recursiveGen = _out144;
                      _483_recOwned = _out145;
                      _484_recErased = _out146;
                      _485_recIdents = _out147;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _482_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _483_recOwned;
                      isErased = _484_recErased;
                      readIdents = _485_recIdents;
                    }
                  } else {
                    DAST._IType _486___mcc_h146 = _source29.dtor_Newtype_a0;
                    DAST._IType _487_b = _486___mcc_h146;
                    {
                      if (object.Equals(_461_fromTpe, _487_b)) {
                        Dafny.ISequence<Dafny.Rune> _488_recursiveGen;
                        bool _489_recOwned;
                        bool _490_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _491_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out148;
                        bool _out149;
                        bool _out150;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out151;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out148, out _out149, out _out150, out _out151);
                        _488_recursiveGen = _out148;
                        _489_recOwned = _out149;
                        _490_recErased = _out150;
                        _491_recIdents = _out151;
                        Dafny.ISequence<Dafny.Rune> _492_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out152;
                        _out152 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _492_rhsType = _out152;
                        Dafny.ISequence<Dafny.Rune> _493_uneraseFn;
                        _493_uneraseFn = ((_489_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _492_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _493_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _488_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _489_recOwned;
                        isErased = false;
                        readIdents = _491_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out153;
                        bool _out154;
                        bool _out155;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _487_b), _487_b, _460_toTpe), @params, mustOwn, out _out153, out _out154, out _out155, out _out156);
                        s = _out153;
                        isOwned = _out154;
                        isErased = _out155;
                        readIdents = _out156;
                      }
                    }
                  }
                } else if (_source28.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _494___mcc_h148 = _source28.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _495_recursiveGen;
                    bool _496_recOwned;
                    bool _497_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _498_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out157;
                    bool _out158;
                    bool _out159;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out157, out _out158, out _out159, out _out160);
                    _495_recursiveGen = _out157;
                    _496_recOwned = _out158;
                    _497_recErased = _out159;
                    _498_recIdents = _out160;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _495_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _496_recOwned;
                    isErased = _497_recErased;
                    readIdents = _498_recIdents;
                  }
                } else if (_source28.is_Array) {
                  DAST._IType _499___mcc_h150 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _500_recursiveGen;
                    bool _501_recOwned;
                    bool _502_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _503_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out161;
                    bool _out162;
                    bool _out163;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out161, out _out162, out _out163, out _out164);
                    _500_recursiveGen = _out161;
                    _501_recOwned = _out162;
                    _502_recErased = _out163;
                    _503_recIdents = _out164;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _500_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _501_recOwned;
                    isErased = _502_recErased;
                    readIdents = _503_recIdents;
                  }
                } else if (_source28.is_Seq) {
                  DAST._IType _504___mcc_h152 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _505_recursiveGen;
                    bool _506_recOwned;
                    bool _507_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _508_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out165;
                    bool _out166;
                    bool _out167;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out165, out _out166, out _out167, out _out168);
                    _505_recursiveGen = _out165;
                    _506_recOwned = _out166;
                    _507_recErased = _out167;
                    _508_recIdents = _out168;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _505_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _506_recOwned;
                    isErased = _507_recErased;
                    readIdents = _508_recIdents;
                  }
                } else if (_source28.is_Set) {
                  DAST._IType _509___mcc_h154 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _510_recursiveGen;
                    bool _511_recOwned;
                    bool _512_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _513_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out169;
                    bool _out170;
                    bool _out171;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out169, out _out170, out _out171, out _out172);
                    _510_recursiveGen = _out169;
                    _511_recOwned = _out170;
                    _512_recErased = _out171;
                    _513_recIdents = _out172;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _510_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _511_recOwned;
                    isErased = _512_recErased;
                    readIdents = _513_recIdents;
                  }
                } else if (_source28.is_Multiset) {
                  DAST._IType _514___mcc_h156 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _515_recursiveGen;
                    bool _516_recOwned;
                    bool _517_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _518_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out173;
                    bool _out174;
                    bool _out175;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out173, out _out174, out _out175, out _out176);
                    _515_recursiveGen = _out173;
                    _516_recOwned = _out174;
                    _517_recErased = _out175;
                    _518_recIdents = _out176;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _515_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _516_recOwned;
                    isErased = _517_recErased;
                    readIdents = _518_recIdents;
                  }
                } else if (_source28.is_Map) {
                  DAST._IType _519___mcc_h158 = _source28.dtor_key;
                  DAST._IType _520___mcc_h159 = _source28.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _521_recursiveGen;
                    bool _522_recOwned;
                    bool _523_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _524_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out177;
                    bool _out178;
                    bool _out179;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out180;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out177, out _out178, out _out179, out _out180);
                    _521_recursiveGen = _out177;
                    _522_recOwned = _out178;
                    _523_recErased = _out179;
                    _524_recIdents = _out180;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _521_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _522_recOwned;
                    isErased = _523_recErased;
                    readIdents = _524_recIdents;
                  }
                } else if (_source28.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _525___mcc_h162 = _source28.dtor_args;
                  DAST._IType _526___mcc_h163 = _source28.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _527_recursiveGen;
                    bool _528_recOwned;
                    bool _529_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _530_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out181;
                    bool _out182;
                    bool _out183;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out184;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out181, out _out182, out _out183, out _out184);
                    _527_recursiveGen = _out181;
                    _528_recOwned = _out182;
                    _529_recErased = _out183;
                    _530_recIdents = _out184;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _527_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _528_recOwned;
                    isErased = _529_recErased;
                    readIdents = _530_recIdents;
                  }
                } else if (_source28.is_Primitive) {
                  DAST._IPrimitive _531___mcc_h166 = _source28.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _532_recursiveGen;
                    bool _533_recOwned;
                    bool _534_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _535_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out185;
                    bool _out186;
                    bool _out187;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out185, out _out186, out _out187, out _out188);
                    _532_recursiveGen = _out185;
                    _533_recOwned = _out186;
                    _534_recErased = _out187;
                    _535_recIdents = _out188;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _532_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _533_recOwned;
                    isErased = _534_recErased;
                    readIdents = _535_recIdents;
                  }
                } else if (_source28.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _536___mcc_h168 = _source28.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _537_recursiveGen;
                    bool _538_recOwned;
                    bool _539_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _540_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out189;
                    bool _out190;
                    bool _out191;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out192;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out189, out _out190, out _out191, out _out192);
                    _537_recursiveGen = _out189;
                    _538_recOwned = _out190;
                    _539_recErased = _out191;
                    _540_recIdents = _out192;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _537_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _538_recOwned;
                    isErased = _539_recErased;
                    readIdents = _540_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _541___mcc_h170 = _source28.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _542_recursiveGen;
                    bool _543_recOwned;
                    bool _544_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _545_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out193;
                    bool _out194;
                    bool _out195;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out196;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out193, out _out194, out _out195, out _out196);
                    _542_recursiveGen = _out193;
                    _543_recOwned = _out194;
                    _544_recErased = _out195;
                    _545_recIdents = _out196;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _542_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _543_recOwned;
                    isErased = _544_recErased;
                    readIdents = _545_recIdents;
                  }
                }
              } else if (_source27.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _546___mcc_h172 = _source27.dtor_path;
                DAST._IType _source30 = _468___mcc_h121;
                if (_source30.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _547___mcc_h175 = _source30.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _548___mcc_h176 = _source30.dtor_typeArgs;
                  DAST._IResolvedType _549___mcc_h177 = _source30.dtor_resolved;
                  DAST._IResolvedType _source31 = _549___mcc_h177;
                  if (_source31.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _550___mcc_h181 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _551_recursiveGen;
                      bool _552_recOwned;
                      bool _553_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _554_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out197;
                      bool _out198;
                      bool _out199;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out197, out _out198, out _out199, out _out200);
                      _551_recursiveGen = _out197;
                      _552_recOwned = _out198;
                      _553_recErased = _out199;
                      _554_recIdents = _out200;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _551_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _552_recOwned;
                      isErased = _553_recErased;
                      readIdents = _554_recIdents;
                    }
                  } else if (_source31.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _555___mcc_h183 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _556_recursiveGen;
                      bool _557_recOwned;
                      bool _558_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _559_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out201;
                      bool _out202;
                      bool _out203;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out201, out _out202, out _out203, out _out204);
                      _556_recursiveGen = _out201;
                      _557_recOwned = _out202;
                      _558_recErased = _out203;
                      _559_recIdents = _out204;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _556_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _557_recOwned;
                      isErased = _558_recErased;
                      readIdents = _559_recIdents;
                    }
                  } else {
                    DAST._IType _560___mcc_h185 = _source31.dtor_Newtype_a0;
                    DAST._IType _561_b = _560___mcc_h185;
                    {
                      if (object.Equals(_461_fromTpe, _561_b)) {
                        Dafny.ISequence<Dafny.Rune> _562_recursiveGen;
                        bool _563_recOwned;
                        bool _564_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _565_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out205;
                        bool _out206;
                        bool _out207;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out208;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out205, out _out206, out _out207, out _out208);
                        _562_recursiveGen = _out205;
                        _563_recOwned = _out206;
                        _564_recErased = _out207;
                        _565_recIdents = _out208;
                        Dafny.ISequence<Dafny.Rune> _566_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out209;
                        _out209 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _566_rhsType = _out209;
                        Dafny.ISequence<Dafny.Rune> _567_uneraseFn;
                        _567_uneraseFn = ((_563_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _566_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _567_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _562_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _563_recOwned;
                        isErased = false;
                        readIdents = _565_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out210;
                        bool _out211;
                        bool _out212;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _561_b), _561_b, _460_toTpe), @params, mustOwn, out _out210, out _out211, out _out212, out _out213);
                        s = _out210;
                        isOwned = _out211;
                        isErased = _out212;
                        readIdents = _out213;
                      }
                    }
                  }
                } else if (_source30.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _568___mcc_h187 = _source30.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _569_recursiveGen;
                    bool _570_recOwned;
                    bool _571_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _572_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out214;
                    bool _out215;
                    bool _out216;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out214, out _out215, out _out216, out _out217);
                    _569_recursiveGen = _out214;
                    _570_recOwned = _out215;
                    _571_recErased = _out216;
                    _572_recIdents = _out217;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _569_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _570_recOwned;
                    isErased = _571_recErased;
                    readIdents = _572_recIdents;
                  }
                } else if (_source30.is_Array) {
                  DAST._IType _573___mcc_h189 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _574_recursiveGen;
                    bool _575_recOwned;
                    bool _576_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _577_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out218;
                    bool _out219;
                    bool _out220;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out221;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out218, out _out219, out _out220, out _out221);
                    _574_recursiveGen = _out218;
                    _575_recOwned = _out219;
                    _576_recErased = _out220;
                    _577_recIdents = _out221;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _575_recOwned;
                    isErased = _576_recErased;
                    readIdents = _577_recIdents;
                  }
                } else if (_source30.is_Seq) {
                  DAST._IType _578___mcc_h191 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _579_recursiveGen;
                    bool _580_recOwned;
                    bool _581_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _582_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out222;
                    bool _out223;
                    bool _out224;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out222, out _out223, out _out224, out _out225);
                    _579_recursiveGen = _out222;
                    _580_recOwned = _out223;
                    _581_recErased = _out224;
                    _582_recIdents = _out225;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _579_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _580_recOwned;
                    isErased = _581_recErased;
                    readIdents = _582_recIdents;
                  }
                } else if (_source30.is_Set) {
                  DAST._IType _583___mcc_h193 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _584_recursiveGen;
                    bool _585_recOwned;
                    bool _586_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _587_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out226;
                    bool _out227;
                    bool _out228;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out229;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out226, out _out227, out _out228, out _out229);
                    _584_recursiveGen = _out226;
                    _585_recOwned = _out227;
                    _586_recErased = _out228;
                    _587_recIdents = _out229;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _584_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _585_recOwned;
                    isErased = _586_recErased;
                    readIdents = _587_recIdents;
                  }
                } else if (_source30.is_Multiset) {
                  DAST._IType _588___mcc_h195 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _589_recursiveGen;
                    bool _590_recOwned;
                    bool _591_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _592_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out230;
                    bool _out231;
                    bool _out232;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out233;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out230, out _out231, out _out232, out _out233);
                    _589_recursiveGen = _out230;
                    _590_recOwned = _out231;
                    _591_recErased = _out232;
                    _592_recIdents = _out233;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _589_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _590_recOwned;
                    isErased = _591_recErased;
                    readIdents = _592_recIdents;
                  }
                } else if (_source30.is_Map) {
                  DAST._IType _593___mcc_h197 = _source30.dtor_key;
                  DAST._IType _594___mcc_h198 = _source30.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _595_recursiveGen;
                    bool _596_recOwned;
                    bool _597_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _598_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out234;
                    bool _out235;
                    bool _out236;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out237;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out234, out _out235, out _out236, out _out237);
                    _595_recursiveGen = _out234;
                    _596_recOwned = _out235;
                    _597_recErased = _out236;
                    _598_recIdents = _out237;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _595_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _596_recOwned;
                    isErased = _597_recErased;
                    readIdents = _598_recIdents;
                  }
                } else if (_source30.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _599___mcc_h201 = _source30.dtor_args;
                  DAST._IType _600___mcc_h202 = _source30.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _601_recursiveGen;
                    bool _602_recOwned;
                    bool _603_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _604_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out238;
                    bool _out239;
                    bool _out240;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out238, out _out239, out _out240, out _out241);
                    _601_recursiveGen = _out238;
                    _602_recOwned = _out239;
                    _603_recErased = _out240;
                    _604_recIdents = _out241;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _601_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _602_recOwned;
                    isErased = _603_recErased;
                    readIdents = _604_recIdents;
                  }
                } else if (_source30.is_Primitive) {
                  DAST._IPrimitive _605___mcc_h205 = _source30.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _606_recursiveGen;
                    bool _607_recOwned;
                    bool _608_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _609_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out242;
                    bool _out243;
                    bool _out244;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out242, out _out243, out _out244, out _out245);
                    _606_recursiveGen = _out242;
                    _607_recOwned = _out243;
                    _608_recErased = _out244;
                    _609_recIdents = _out245;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _606_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _607_recOwned;
                    isErased = _608_recErased;
                    readIdents = _609_recIdents;
                  }
                } else if (_source30.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _610___mcc_h207 = _source30.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _611_recursiveGen;
                    bool _612_recOwned;
                    bool _613_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _614_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out246;
                    bool _out247;
                    bool _out248;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out246, out _out247, out _out248, out _out249);
                    _611_recursiveGen = _out246;
                    _612_recOwned = _out247;
                    _613_recErased = _out248;
                    _614_recIdents = _out249;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _611_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _612_recOwned;
                    isErased = _613_recErased;
                    readIdents = _614_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _615___mcc_h209 = _source30.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _616_recursiveGen;
                    bool _617_recOwned;
                    bool _618_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _619_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out250;
                    bool _out251;
                    bool _out252;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out250, out _out251, out _out252, out _out253);
                    _616_recursiveGen = _out250;
                    _617_recOwned = _out251;
                    _618_recErased = _out252;
                    _619_recIdents = _out253;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _616_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _617_recOwned;
                    isErased = _618_recErased;
                    readIdents = _619_recIdents;
                  }
                }
              } else {
                DAST._IType _620___mcc_h211 = _source27.dtor_Newtype_a0;
                DAST._IType _source32 = _468___mcc_h121;
                if (_source32.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _621___mcc_h214 = _source32.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _622___mcc_h215 = _source32.dtor_typeArgs;
                  DAST._IResolvedType _623___mcc_h216 = _source32.dtor_resolved;
                  DAST._IResolvedType _source33 = _623___mcc_h216;
                  if (_source33.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _624___mcc_h223 = _source33.dtor_path;
                    DAST._IType _625_b = _620___mcc_h211;
                    {
                      if (object.Equals(_625_b, _460_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _626_recursiveGen;
                        bool _627_recOwned;
                        bool _628_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _629_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out254;
                        bool _out255;
                        bool _out256;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out254, out _out255, out _out256, out _out257);
                        _626_recursiveGen = _out254;
                        _627_recOwned = _out255;
                        _628_recErased = _out256;
                        _629_recIdents = _out257;
                        Dafny.ISequence<Dafny.Rune> _630_uneraseFn;
                        _630_uneraseFn = ((_627_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _630_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _626_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _627_recOwned;
                        isErased = true;
                        readIdents = _629_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out258;
                        bool _out259;
                        bool _out260;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _625_b), _625_b, _460_toTpe), @params, mustOwn, out _out258, out _out259, out _out260, out _out261);
                        s = _out258;
                        isOwned = _out259;
                        isErased = _out260;
                        readIdents = _out261;
                      }
                    }
                  } else if (_source33.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _631___mcc_h226 = _source33.dtor_path;
                    DAST._IType _632_b = _620___mcc_h211;
                    {
                      if (object.Equals(_632_b, _460_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _633_recursiveGen;
                        bool _634_recOwned;
                        bool _635_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _636_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out262;
                        bool _out263;
                        bool _out264;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out262, out _out263, out _out264, out _out265);
                        _633_recursiveGen = _out262;
                        _634_recOwned = _out263;
                        _635_recErased = _out264;
                        _636_recIdents = _out265;
                        Dafny.ISequence<Dafny.Rune> _637_uneraseFn;
                        _637_uneraseFn = ((_634_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _637_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _633_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _634_recOwned;
                        isErased = true;
                        readIdents = _636_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out266;
                        bool _out267;
                        bool _out268;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out269;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _632_b), _632_b, _460_toTpe), @params, mustOwn, out _out266, out _out267, out _out268, out _out269);
                        s = _out266;
                        isOwned = _out267;
                        isErased = _out268;
                        readIdents = _out269;
                      }
                    }
                  } else {
                    DAST._IType _638___mcc_h229 = _source33.dtor_Newtype_a0;
                    DAST._IType _639_b = _638___mcc_h229;
                    {
                      if (object.Equals(_461_fromTpe, _639_b)) {
                        Dafny.ISequence<Dafny.Rune> _640_recursiveGen;
                        bool _641_recOwned;
                        bool _642_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _643_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out270;
                        bool _out271;
                        bool _out272;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out273;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out270, out _out271, out _out272, out _out273);
                        _640_recursiveGen = _out270;
                        _641_recOwned = _out271;
                        _642_recErased = _out272;
                        _643_recIdents = _out273;
                        Dafny.ISequence<Dafny.Rune> _644_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out274;
                        _out274 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _644_rhsType = _out274;
                        Dafny.ISequence<Dafny.Rune> _645_uneraseFn;
                        _645_uneraseFn = ((_641_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _644_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _645_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _640_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _641_recOwned;
                        isErased = false;
                        readIdents = _643_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out275;
                        bool _out276;
                        bool _out277;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _639_b), _639_b, _460_toTpe), @params, mustOwn, out _out275, out _out276, out _out277, out _out278);
                        s = _out275;
                        isOwned = _out276;
                        isErased = _out277;
                        readIdents = _out278;
                      }
                    }
                  }
                } else if (_source32.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _646___mcc_h232 = _source32.dtor_Tuple_a0;
                  DAST._IType _647_b = _620___mcc_h211;
                  {
                    if (object.Equals(_647_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _648_recursiveGen;
                      bool _649_recOwned;
                      bool _650_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _651_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out279;
                      bool _out280;
                      bool _out281;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out279, out _out280, out _out281, out _out282);
                      _648_recursiveGen = _out279;
                      _649_recOwned = _out280;
                      _650_recErased = _out281;
                      _651_recIdents = _out282;
                      Dafny.ISequence<Dafny.Rune> _652_uneraseFn;
                      _652_uneraseFn = ((_649_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _652_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _648_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _649_recOwned;
                      isErased = true;
                      readIdents = _651_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out283;
                      bool _out284;
                      bool _out285;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _647_b), _647_b, _460_toTpe), @params, mustOwn, out _out283, out _out284, out _out285, out _out286);
                      s = _out283;
                      isOwned = _out284;
                      isErased = _out285;
                      readIdents = _out286;
                    }
                  }
                } else if (_source32.is_Array) {
                  DAST._IType _653___mcc_h235 = _source32.dtor_element;
                  DAST._IType _654_b = _620___mcc_h211;
                  {
                    if (object.Equals(_654_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _655_recursiveGen;
                      bool _656_recOwned;
                      bool _657_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _658_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out287;
                      bool _out288;
                      bool _out289;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out287, out _out288, out _out289, out _out290);
                      _655_recursiveGen = _out287;
                      _656_recOwned = _out288;
                      _657_recErased = _out289;
                      _658_recIdents = _out290;
                      Dafny.ISequence<Dafny.Rune> _659_uneraseFn;
                      _659_uneraseFn = ((_656_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _659_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _655_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _656_recOwned;
                      isErased = true;
                      readIdents = _658_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out291;
                      bool _out292;
                      bool _out293;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _654_b), _654_b, _460_toTpe), @params, mustOwn, out _out291, out _out292, out _out293, out _out294);
                      s = _out291;
                      isOwned = _out292;
                      isErased = _out293;
                      readIdents = _out294;
                    }
                  }
                } else if (_source32.is_Seq) {
                  DAST._IType _660___mcc_h238 = _source32.dtor_element;
                  DAST._IType _661_b = _620___mcc_h211;
                  {
                    if (object.Equals(_661_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _662_recursiveGen;
                      bool _663_recOwned;
                      bool _664_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _665_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out295;
                      bool _out296;
                      bool _out297;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out295, out _out296, out _out297, out _out298);
                      _662_recursiveGen = _out295;
                      _663_recOwned = _out296;
                      _664_recErased = _out297;
                      _665_recIdents = _out298;
                      Dafny.ISequence<Dafny.Rune> _666_uneraseFn;
                      _666_uneraseFn = ((_663_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _666_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _662_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _663_recOwned;
                      isErased = true;
                      readIdents = _665_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out299;
                      bool _out300;
                      bool _out301;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _661_b), _661_b, _460_toTpe), @params, mustOwn, out _out299, out _out300, out _out301, out _out302);
                      s = _out299;
                      isOwned = _out300;
                      isErased = _out301;
                      readIdents = _out302;
                    }
                  }
                } else if (_source32.is_Set) {
                  DAST._IType _667___mcc_h241 = _source32.dtor_element;
                  DAST._IType _668_b = _620___mcc_h211;
                  {
                    if (object.Equals(_668_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _669_recursiveGen;
                      bool _670_recOwned;
                      bool _671_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _672_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out303;
                      bool _out304;
                      bool _out305;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out303, out _out304, out _out305, out _out306);
                      _669_recursiveGen = _out303;
                      _670_recOwned = _out304;
                      _671_recErased = _out305;
                      _672_recIdents = _out306;
                      Dafny.ISequence<Dafny.Rune> _673_uneraseFn;
                      _673_uneraseFn = ((_670_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _673_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _669_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _670_recOwned;
                      isErased = true;
                      readIdents = _672_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out307;
                      bool _out308;
                      bool _out309;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out310;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _668_b), _668_b, _460_toTpe), @params, mustOwn, out _out307, out _out308, out _out309, out _out310);
                      s = _out307;
                      isOwned = _out308;
                      isErased = _out309;
                      readIdents = _out310;
                    }
                  }
                } else if (_source32.is_Multiset) {
                  DAST._IType _674___mcc_h244 = _source32.dtor_element;
                  DAST._IType _675_b = _620___mcc_h211;
                  {
                    if (object.Equals(_675_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _676_recursiveGen;
                      bool _677_recOwned;
                      bool _678_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _679_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out311;
                      bool _out312;
                      bool _out313;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out311, out _out312, out _out313, out _out314);
                      _676_recursiveGen = _out311;
                      _677_recOwned = _out312;
                      _678_recErased = _out313;
                      _679_recIdents = _out314;
                      Dafny.ISequence<Dafny.Rune> _680_uneraseFn;
                      _680_uneraseFn = ((_677_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _680_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _676_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _677_recOwned;
                      isErased = true;
                      readIdents = _679_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out315;
                      bool _out316;
                      bool _out317;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _675_b), _675_b, _460_toTpe), @params, mustOwn, out _out315, out _out316, out _out317, out _out318);
                      s = _out315;
                      isOwned = _out316;
                      isErased = _out317;
                      readIdents = _out318;
                    }
                  }
                } else if (_source32.is_Map) {
                  DAST._IType _681___mcc_h247 = _source32.dtor_key;
                  DAST._IType _682___mcc_h248 = _source32.dtor_value;
                  DAST._IType _683_b = _620___mcc_h211;
                  {
                    if (object.Equals(_683_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _684_recursiveGen;
                      bool _685_recOwned;
                      bool _686_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _687_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out319;
                      bool _out320;
                      bool _out321;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out319, out _out320, out _out321, out _out322);
                      _684_recursiveGen = _out319;
                      _685_recOwned = _out320;
                      _686_recErased = _out321;
                      _687_recIdents = _out322;
                      Dafny.ISequence<Dafny.Rune> _688_uneraseFn;
                      _688_uneraseFn = ((_685_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _688_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _684_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _685_recOwned;
                      isErased = true;
                      readIdents = _687_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out323;
                      bool _out324;
                      bool _out325;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _683_b), _683_b, _460_toTpe), @params, mustOwn, out _out323, out _out324, out _out325, out _out326);
                      s = _out323;
                      isOwned = _out324;
                      isErased = _out325;
                      readIdents = _out326;
                    }
                  }
                } else if (_source32.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _689___mcc_h253 = _source32.dtor_args;
                  DAST._IType _690___mcc_h254 = _source32.dtor_result;
                  DAST._IType _691_b = _620___mcc_h211;
                  {
                    if (object.Equals(_691_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _692_recursiveGen;
                      bool _693_recOwned;
                      bool _694_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _695_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out327;
                      bool _out328;
                      bool _out329;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out327, out _out328, out _out329, out _out330);
                      _692_recursiveGen = _out327;
                      _693_recOwned = _out328;
                      _694_recErased = _out329;
                      _695_recIdents = _out330;
                      Dafny.ISequence<Dafny.Rune> _696_uneraseFn;
                      _696_uneraseFn = ((_693_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _696_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _692_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _693_recOwned;
                      isErased = true;
                      readIdents = _695_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out331;
                      bool _out332;
                      bool _out333;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _691_b), _691_b, _460_toTpe), @params, mustOwn, out _out331, out _out332, out _out333, out _out334);
                      s = _out331;
                      isOwned = _out332;
                      isErased = _out333;
                      readIdents = _out334;
                    }
                  }
                } else if (_source32.is_Primitive) {
                  DAST._IPrimitive _697___mcc_h259 = _source32.dtor_Primitive_a0;
                  DAST._IType _698_b = _620___mcc_h211;
                  {
                    if (object.Equals(_698_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _699_recursiveGen;
                      bool _700_recOwned;
                      bool _701_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _702_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out335;
                      bool _out336;
                      bool _out337;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out338;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out335, out _out336, out _out337, out _out338);
                      _699_recursiveGen = _out335;
                      _700_recOwned = _out336;
                      _701_recErased = _out337;
                      _702_recIdents = _out338;
                      Dafny.ISequence<Dafny.Rune> _703_uneraseFn;
                      _703_uneraseFn = ((_700_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _703_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _699_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _700_recOwned;
                      isErased = true;
                      readIdents = _702_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out339;
                      bool _out340;
                      bool _out341;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _698_b), _698_b, _460_toTpe), @params, mustOwn, out _out339, out _out340, out _out341, out _out342);
                      s = _out339;
                      isOwned = _out340;
                      isErased = _out341;
                      readIdents = _out342;
                    }
                  }
                } else if (_source32.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _704___mcc_h262 = _source32.dtor_Passthrough_a0;
                  DAST._IType _705_b = _620___mcc_h211;
                  {
                    if (object.Equals(_705_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _706_recursiveGen;
                      bool _707_recOwned;
                      bool _708_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _709_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out343;
                      bool _out344;
                      bool _out345;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out343, out _out344, out _out345, out _out346);
                      _706_recursiveGen = _out343;
                      _707_recOwned = _out344;
                      _708_recErased = _out345;
                      _709_recIdents = _out346;
                      Dafny.ISequence<Dafny.Rune> _710_uneraseFn;
                      _710_uneraseFn = ((_707_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _710_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _706_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _707_recOwned;
                      isErased = true;
                      readIdents = _709_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out347;
                      bool _out348;
                      bool _out349;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out350;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _705_b), _705_b, _460_toTpe), @params, mustOwn, out _out347, out _out348, out _out349, out _out350);
                      s = _out347;
                      isOwned = _out348;
                      isErased = _out349;
                      readIdents = _out350;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _711___mcc_h265 = _source32.dtor_TypeArg_a0;
                  DAST._IType _712_b = _620___mcc_h211;
                  {
                    if (object.Equals(_712_b, _460_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _713_recursiveGen;
                      bool _714_recOwned;
                      bool _715_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _716_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out351;
                      bool _out352;
                      bool _out353;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out354;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out351, out _out352, out _out353, out _out354);
                      _713_recursiveGen = _out351;
                      _714_recOwned = _out352;
                      _715_recErased = _out353;
                      _716_recIdents = _out354;
                      Dafny.ISequence<Dafny.Rune> _717_uneraseFn;
                      _717_uneraseFn = ((_714_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _717_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _713_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _714_recOwned;
                      isErased = true;
                      readIdents = _716_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out355;
                      bool _out356;
                      bool _out357;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _712_b), _712_b, _460_toTpe), @params, mustOwn, out _out355, out _out356, out _out357, out _out358);
                      s = _out355;
                      isOwned = _out356;
                      isErased = _out357;
                      readIdents = _out358;
                    }
                  }
                }
              }
            } else if (_source26.is_Tuple) {
              Dafny.ISequence<DAST._IType> _718___mcc_h268 = _source26.dtor_Tuple_a0;
              DAST._IType _source34 = _468___mcc_h121;
              if (_source34.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _719___mcc_h271 = _source34.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _720___mcc_h272 = _source34.dtor_typeArgs;
                DAST._IResolvedType _721___mcc_h273 = _source34.dtor_resolved;
                DAST._IResolvedType _source35 = _721___mcc_h273;
                if (_source35.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _722___mcc_h277 = _source35.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _723_recursiveGen;
                    bool _724_recOwned;
                    bool _725_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _726_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out359;
                    bool _out360;
                    bool _out361;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out362;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out359, out _out360, out _out361, out _out362);
                    _723_recursiveGen = _out359;
                    _724_recOwned = _out360;
                    _725_recErased = _out361;
                    _726_recIdents = _out362;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _723_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _724_recOwned;
                    isErased = _725_recErased;
                    readIdents = _726_recIdents;
                  }
                } else if (_source35.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _727___mcc_h279 = _source35.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _728_recursiveGen;
                    bool _729_recOwned;
                    bool _730_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _731_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out363;
                    bool _out364;
                    bool _out365;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out366;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out363, out _out364, out _out365, out _out366);
                    _728_recursiveGen = _out363;
                    _729_recOwned = _out364;
                    _730_recErased = _out365;
                    _731_recIdents = _out366;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _728_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _729_recOwned;
                    isErased = _730_recErased;
                    readIdents = _731_recIdents;
                  }
                } else {
                  DAST._IType _732___mcc_h281 = _source35.dtor_Newtype_a0;
                  DAST._IType _733_b = _732___mcc_h281;
                  {
                    if (object.Equals(_461_fromTpe, _733_b)) {
                      Dafny.ISequence<Dafny.Rune> _734_recursiveGen;
                      bool _735_recOwned;
                      bool _736_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _737_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out367;
                      bool _out368;
                      bool _out369;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out370;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out367, out _out368, out _out369, out _out370);
                      _734_recursiveGen = _out367;
                      _735_recOwned = _out368;
                      _736_recErased = _out369;
                      _737_recIdents = _out370;
                      Dafny.ISequence<Dafny.Rune> _738_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out371;
                      _out371 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _738_rhsType = _out371;
                      Dafny.ISequence<Dafny.Rune> _739_uneraseFn;
                      _739_uneraseFn = ((_735_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _738_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _739_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _734_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _735_recOwned;
                      isErased = false;
                      readIdents = _737_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out372;
                      bool _out373;
                      bool _out374;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _733_b), _733_b, _460_toTpe), @params, mustOwn, out _out372, out _out373, out _out374, out _out375);
                      s = _out372;
                      isOwned = _out373;
                      isErased = _out374;
                      readIdents = _out375;
                    }
                  }
                }
              } else if (_source34.is_Tuple) {
                Dafny.ISequence<DAST._IType> _740___mcc_h283 = _source34.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _741_recursiveGen;
                  bool _742_recOwned;
                  bool _743_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _744_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out376;
                  bool _out377;
                  bool _out378;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out376, out _out377, out _out378, out _out379);
                  _741_recursiveGen = _out376;
                  _742_recOwned = _out377;
                  _743_recErased = _out378;
                  _744_recIdents = _out379;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _741_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _742_recOwned;
                  isErased = _743_recErased;
                  readIdents = _744_recIdents;
                }
              } else if (_source34.is_Array) {
                DAST._IType _745___mcc_h285 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _746_recursiveGen;
                  bool _747_recOwned;
                  bool _748_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _749_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out380;
                  bool _out381;
                  bool _out382;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out380, out _out381, out _out382, out _out383);
                  _746_recursiveGen = _out380;
                  _747_recOwned = _out381;
                  _748_recErased = _out382;
                  _749_recIdents = _out383;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _746_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _747_recOwned;
                  isErased = _748_recErased;
                  readIdents = _749_recIdents;
                }
              } else if (_source34.is_Seq) {
                DAST._IType _750___mcc_h287 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _751_recursiveGen;
                  bool _752_recOwned;
                  bool _753_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _754_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out384;
                  bool _out385;
                  bool _out386;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out384, out _out385, out _out386, out _out387);
                  _751_recursiveGen = _out384;
                  _752_recOwned = _out385;
                  _753_recErased = _out386;
                  _754_recIdents = _out387;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _751_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _752_recOwned;
                  isErased = _753_recErased;
                  readIdents = _754_recIdents;
                }
              } else if (_source34.is_Set) {
                DAST._IType _755___mcc_h289 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _756_recursiveGen;
                  bool _757_recOwned;
                  bool _758_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _759_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out388;
                  bool _out389;
                  bool _out390;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out388, out _out389, out _out390, out _out391);
                  _756_recursiveGen = _out388;
                  _757_recOwned = _out389;
                  _758_recErased = _out390;
                  _759_recIdents = _out391;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _756_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _757_recOwned;
                  isErased = _758_recErased;
                  readIdents = _759_recIdents;
                }
              } else if (_source34.is_Multiset) {
                DAST._IType _760___mcc_h291 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _761_recursiveGen;
                  bool _762_recOwned;
                  bool _763_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _764_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out392;
                  bool _out393;
                  bool _out394;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out392, out _out393, out _out394, out _out395);
                  _761_recursiveGen = _out392;
                  _762_recOwned = _out393;
                  _763_recErased = _out394;
                  _764_recIdents = _out395;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _761_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _762_recOwned;
                  isErased = _763_recErased;
                  readIdents = _764_recIdents;
                }
              } else if (_source34.is_Map) {
                DAST._IType _765___mcc_h293 = _source34.dtor_key;
                DAST._IType _766___mcc_h294 = _source34.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _767_recursiveGen;
                  bool _768_recOwned;
                  bool _769_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _770_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out396;
                  bool _out397;
                  bool _out398;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out396, out _out397, out _out398, out _out399);
                  _767_recursiveGen = _out396;
                  _768_recOwned = _out397;
                  _769_recErased = _out398;
                  _770_recIdents = _out399;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _767_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _768_recOwned;
                  isErased = _769_recErased;
                  readIdents = _770_recIdents;
                }
              } else if (_source34.is_Arrow) {
                Dafny.ISequence<DAST._IType> _771___mcc_h297 = _source34.dtor_args;
                DAST._IType _772___mcc_h298 = _source34.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _773_recursiveGen;
                  bool _774_recOwned;
                  bool _775_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _776_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out400;
                  bool _out401;
                  bool _out402;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out400, out _out401, out _out402, out _out403);
                  _773_recursiveGen = _out400;
                  _774_recOwned = _out401;
                  _775_recErased = _out402;
                  _776_recIdents = _out403;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _773_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _774_recOwned;
                  isErased = _775_recErased;
                  readIdents = _776_recIdents;
                }
              } else if (_source34.is_Primitive) {
                DAST._IPrimitive _777___mcc_h301 = _source34.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _778_recursiveGen;
                  bool _779_recOwned;
                  bool _780_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _781_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out404;
                  bool _out405;
                  bool _out406;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out404, out _out405, out _out406, out _out407);
                  _778_recursiveGen = _out404;
                  _779_recOwned = _out405;
                  _780_recErased = _out406;
                  _781_recIdents = _out407;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _778_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _779_recOwned;
                  isErased = _780_recErased;
                  readIdents = _781_recIdents;
                }
              } else if (_source34.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _782___mcc_h303 = _source34.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _783_recursiveGen;
                  bool _784_recOwned;
                  bool _785_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _786_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out408;
                  bool _out409;
                  bool _out410;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out408, out _out409, out _out410, out _out411);
                  _783_recursiveGen = _out408;
                  _784_recOwned = _out409;
                  _785_recErased = _out410;
                  _786_recIdents = _out411;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _783_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _784_recOwned;
                  isErased = _785_recErased;
                  readIdents = _786_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _787___mcc_h305 = _source34.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _788_recursiveGen;
                  bool _789_recOwned;
                  bool _790_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _791_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out412;
                  bool _out413;
                  bool _out414;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out412, out _out413, out _out414, out _out415);
                  _788_recursiveGen = _out412;
                  _789_recOwned = _out413;
                  _790_recErased = _out414;
                  _791_recIdents = _out415;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _788_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _789_recOwned;
                  isErased = _790_recErased;
                  readIdents = _791_recIdents;
                }
              }
            } else if (_source26.is_Array) {
              DAST._IType _792___mcc_h307 = _source26.dtor_element;
              DAST._IType _source36 = _468___mcc_h121;
              if (_source36.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _793___mcc_h310 = _source36.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _794___mcc_h311 = _source36.dtor_typeArgs;
                DAST._IResolvedType _795___mcc_h312 = _source36.dtor_resolved;
                DAST._IResolvedType _source37 = _795___mcc_h312;
                if (_source37.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _796___mcc_h316 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _797_recursiveGen;
                    bool _798_recOwned;
                    bool _799_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _800_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out416;
                    bool _out417;
                    bool _out418;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out416, out _out417, out _out418, out _out419);
                    _797_recursiveGen = _out416;
                    _798_recOwned = _out417;
                    _799_recErased = _out418;
                    _800_recIdents = _out419;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _797_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _798_recOwned;
                    isErased = _799_recErased;
                    readIdents = _800_recIdents;
                  }
                } else if (_source37.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _801___mcc_h318 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _802_recursiveGen;
                    bool _803_recOwned;
                    bool _804_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _805_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out420;
                    bool _out421;
                    bool _out422;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out420, out _out421, out _out422, out _out423);
                    _802_recursiveGen = _out420;
                    _803_recOwned = _out421;
                    _804_recErased = _out422;
                    _805_recIdents = _out423;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _802_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _803_recOwned;
                    isErased = _804_recErased;
                    readIdents = _805_recIdents;
                  }
                } else {
                  DAST._IType _806___mcc_h320 = _source37.dtor_Newtype_a0;
                  DAST._IType _807_b = _806___mcc_h320;
                  {
                    if (object.Equals(_461_fromTpe, _807_b)) {
                      Dafny.ISequence<Dafny.Rune> _808_recursiveGen;
                      bool _809_recOwned;
                      bool _810_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _811_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out424;
                      bool _out425;
                      bool _out426;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out424, out _out425, out _out426, out _out427);
                      _808_recursiveGen = _out424;
                      _809_recOwned = _out425;
                      _810_recErased = _out426;
                      _811_recIdents = _out427;
                      Dafny.ISequence<Dafny.Rune> _812_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out428;
                      _out428 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _812_rhsType = _out428;
                      Dafny.ISequence<Dafny.Rune> _813_uneraseFn;
                      _813_uneraseFn = ((_809_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _812_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _813_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _808_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _809_recOwned;
                      isErased = false;
                      readIdents = _811_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out429;
                      bool _out430;
                      bool _out431;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _807_b), _807_b, _460_toTpe), @params, mustOwn, out _out429, out _out430, out _out431, out _out432);
                      s = _out429;
                      isOwned = _out430;
                      isErased = _out431;
                      readIdents = _out432;
                    }
                  }
                }
              } else if (_source36.is_Tuple) {
                Dafny.ISequence<DAST._IType> _814___mcc_h322 = _source36.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _815_recursiveGen;
                  bool _816_recOwned;
                  bool _817_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _818_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out433;
                  bool _out434;
                  bool _out435;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out433, out _out434, out _out435, out _out436);
                  _815_recursiveGen = _out433;
                  _816_recOwned = _out434;
                  _817_recErased = _out435;
                  _818_recIdents = _out436;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _815_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _816_recOwned;
                  isErased = _817_recErased;
                  readIdents = _818_recIdents;
                }
              } else if (_source36.is_Array) {
                DAST._IType _819___mcc_h324 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _820_recursiveGen;
                  bool _821_recOwned;
                  bool _822_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _823_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out437;
                  bool _out438;
                  bool _out439;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out437, out _out438, out _out439, out _out440);
                  _820_recursiveGen = _out437;
                  _821_recOwned = _out438;
                  _822_recErased = _out439;
                  _823_recIdents = _out440;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _820_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _821_recOwned;
                  isErased = _822_recErased;
                  readIdents = _823_recIdents;
                }
              } else if (_source36.is_Seq) {
                DAST._IType _824___mcc_h326 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _825_recursiveGen;
                  bool _826_recOwned;
                  bool _827_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _828_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out441;
                  bool _out442;
                  bool _out443;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out441, out _out442, out _out443, out _out444);
                  _825_recursiveGen = _out441;
                  _826_recOwned = _out442;
                  _827_recErased = _out443;
                  _828_recIdents = _out444;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _825_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _826_recOwned;
                  isErased = _827_recErased;
                  readIdents = _828_recIdents;
                }
              } else if (_source36.is_Set) {
                DAST._IType _829___mcc_h328 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _830_recursiveGen;
                  bool _831_recOwned;
                  bool _832_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _833_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out445;
                  bool _out446;
                  bool _out447;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out445, out _out446, out _out447, out _out448);
                  _830_recursiveGen = _out445;
                  _831_recOwned = _out446;
                  _832_recErased = _out447;
                  _833_recIdents = _out448;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _830_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _831_recOwned;
                  isErased = _832_recErased;
                  readIdents = _833_recIdents;
                }
              } else if (_source36.is_Multiset) {
                DAST._IType _834___mcc_h330 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _835_recursiveGen;
                  bool _836_recOwned;
                  bool _837_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _838_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out449;
                  bool _out450;
                  bool _out451;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out452;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out449, out _out450, out _out451, out _out452);
                  _835_recursiveGen = _out449;
                  _836_recOwned = _out450;
                  _837_recErased = _out451;
                  _838_recIdents = _out452;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _835_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _836_recOwned;
                  isErased = _837_recErased;
                  readIdents = _838_recIdents;
                }
              } else if (_source36.is_Map) {
                DAST._IType _839___mcc_h332 = _source36.dtor_key;
                DAST._IType _840___mcc_h333 = _source36.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _841_recursiveGen;
                  bool _842_recOwned;
                  bool _843_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _844_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out453;
                  bool _out454;
                  bool _out455;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out453, out _out454, out _out455, out _out456);
                  _841_recursiveGen = _out453;
                  _842_recOwned = _out454;
                  _843_recErased = _out455;
                  _844_recIdents = _out456;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _841_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _842_recOwned;
                  isErased = _843_recErased;
                  readIdents = _844_recIdents;
                }
              } else if (_source36.is_Arrow) {
                Dafny.ISequence<DAST._IType> _845___mcc_h336 = _source36.dtor_args;
                DAST._IType _846___mcc_h337 = _source36.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _847_recursiveGen;
                  bool _848_recOwned;
                  bool _849_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _850_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out457;
                  bool _out458;
                  bool _out459;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out457, out _out458, out _out459, out _out460);
                  _847_recursiveGen = _out457;
                  _848_recOwned = _out458;
                  _849_recErased = _out459;
                  _850_recIdents = _out460;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _847_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _848_recOwned;
                  isErased = _849_recErased;
                  readIdents = _850_recIdents;
                }
              } else if (_source36.is_Primitive) {
                DAST._IPrimitive _851___mcc_h340 = _source36.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _852_recursiveGen;
                  bool _853_recOwned;
                  bool _854_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _855_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out461;
                  bool _out462;
                  bool _out463;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out461, out _out462, out _out463, out _out464);
                  _852_recursiveGen = _out461;
                  _853_recOwned = _out462;
                  _854_recErased = _out463;
                  _855_recIdents = _out464;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _852_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _853_recOwned;
                  isErased = _854_recErased;
                  readIdents = _855_recIdents;
                }
              } else if (_source36.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _856___mcc_h342 = _source36.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _857_recursiveGen;
                  bool _858_recOwned;
                  bool _859_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _860_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out465;
                  bool _out466;
                  bool _out467;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out465, out _out466, out _out467, out _out468);
                  _857_recursiveGen = _out465;
                  _858_recOwned = _out466;
                  _859_recErased = _out467;
                  _860_recIdents = _out468;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _857_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _858_recOwned;
                  isErased = _859_recErased;
                  readIdents = _860_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _861___mcc_h344 = _source36.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _862_recursiveGen;
                  bool _863_recOwned;
                  bool _864_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _865_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out469;
                  bool _out470;
                  bool _out471;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out469, out _out470, out _out471, out _out472);
                  _862_recursiveGen = _out469;
                  _863_recOwned = _out470;
                  _864_recErased = _out471;
                  _865_recIdents = _out472;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _862_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _863_recOwned;
                  isErased = _864_recErased;
                  readIdents = _865_recIdents;
                }
              }
            } else if (_source26.is_Seq) {
              DAST._IType _866___mcc_h346 = _source26.dtor_element;
              DAST._IType _source38 = _468___mcc_h121;
              if (_source38.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _867___mcc_h349 = _source38.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _868___mcc_h350 = _source38.dtor_typeArgs;
                DAST._IResolvedType _869___mcc_h351 = _source38.dtor_resolved;
                DAST._IResolvedType _source39 = _869___mcc_h351;
                if (_source39.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _870___mcc_h355 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _871_recursiveGen;
                    bool _872_recOwned;
                    bool _873_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _874_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out473;
                    bool _out474;
                    bool _out475;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out473, out _out474, out _out475, out _out476);
                    _871_recursiveGen = _out473;
                    _872_recOwned = _out474;
                    _873_recErased = _out475;
                    _874_recIdents = _out476;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _871_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _872_recOwned;
                    isErased = _873_recErased;
                    readIdents = _874_recIdents;
                  }
                } else if (_source39.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _875___mcc_h357 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _876_recursiveGen;
                    bool _877_recOwned;
                    bool _878_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _879_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out477;
                    bool _out478;
                    bool _out479;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out477, out _out478, out _out479, out _out480);
                    _876_recursiveGen = _out477;
                    _877_recOwned = _out478;
                    _878_recErased = _out479;
                    _879_recIdents = _out480;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _877_recOwned;
                    isErased = _878_recErased;
                    readIdents = _879_recIdents;
                  }
                } else {
                  DAST._IType _880___mcc_h359 = _source39.dtor_Newtype_a0;
                  DAST._IType _881_b = _880___mcc_h359;
                  {
                    if (object.Equals(_461_fromTpe, _881_b)) {
                      Dafny.ISequence<Dafny.Rune> _882_recursiveGen;
                      bool _883_recOwned;
                      bool _884_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _885_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out481;
                      bool _out482;
                      bool _out483;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out481, out _out482, out _out483, out _out484);
                      _882_recursiveGen = _out481;
                      _883_recOwned = _out482;
                      _884_recErased = _out483;
                      _885_recIdents = _out484;
                      Dafny.ISequence<Dafny.Rune> _886_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out485;
                      _out485 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _886_rhsType = _out485;
                      Dafny.ISequence<Dafny.Rune> _887_uneraseFn;
                      _887_uneraseFn = ((_883_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _886_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _887_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _882_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _883_recOwned;
                      isErased = false;
                      readIdents = _885_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out486;
                      bool _out487;
                      bool _out488;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out489;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _881_b), _881_b, _460_toTpe), @params, mustOwn, out _out486, out _out487, out _out488, out _out489);
                      s = _out486;
                      isOwned = _out487;
                      isErased = _out488;
                      readIdents = _out489;
                    }
                  }
                }
              } else if (_source38.is_Tuple) {
                Dafny.ISequence<DAST._IType> _888___mcc_h361 = _source38.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _889_recursiveGen;
                  bool _890_recOwned;
                  bool _891_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _892_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out490;
                  bool _out491;
                  bool _out492;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out490, out _out491, out _out492, out _out493);
                  _889_recursiveGen = _out490;
                  _890_recOwned = _out491;
                  _891_recErased = _out492;
                  _892_recIdents = _out493;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _889_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _890_recOwned;
                  isErased = _891_recErased;
                  readIdents = _892_recIdents;
                }
              } else if (_source38.is_Array) {
                DAST._IType _893___mcc_h363 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _894_recursiveGen;
                  bool _895_recOwned;
                  bool _896_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _897_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out494;
                  bool _out495;
                  bool _out496;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out494, out _out495, out _out496, out _out497);
                  _894_recursiveGen = _out494;
                  _895_recOwned = _out495;
                  _896_recErased = _out496;
                  _897_recIdents = _out497;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _894_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _895_recOwned;
                  isErased = _896_recErased;
                  readIdents = _897_recIdents;
                }
              } else if (_source38.is_Seq) {
                DAST._IType _898___mcc_h365 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _899_recursiveGen;
                  bool _900_recOwned;
                  bool _901_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _902_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out498;
                  bool _out499;
                  bool _out500;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out501;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out498, out _out499, out _out500, out _out501);
                  _899_recursiveGen = _out498;
                  _900_recOwned = _out499;
                  _901_recErased = _out500;
                  _902_recIdents = _out501;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _899_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _900_recOwned;
                  isErased = _901_recErased;
                  readIdents = _902_recIdents;
                }
              } else if (_source38.is_Set) {
                DAST._IType _903___mcc_h367 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _904_recursiveGen;
                  bool _905_recOwned;
                  bool _906_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _907_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out502;
                  bool _out503;
                  bool _out504;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out502, out _out503, out _out504, out _out505);
                  _904_recursiveGen = _out502;
                  _905_recOwned = _out503;
                  _906_recErased = _out504;
                  _907_recIdents = _out505;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _904_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _905_recOwned;
                  isErased = _906_recErased;
                  readIdents = _907_recIdents;
                }
              } else if (_source38.is_Multiset) {
                DAST._IType _908___mcc_h369 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _909_recursiveGen;
                  bool _910_recOwned;
                  bool _911_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _912_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out506;
                  bool _out507;
                  bool _out508;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out506, out _out507, out _out508, out _out509);
                  _909_recursiveGen = _out506;
                  _910_recOwned = _out507;
                  _911_recErased = _out508;
                  _912_recIdents = _out509;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _909_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _910_recOwned;
                  isErased = _911_recErased;
                  readIdents = _912_recIdents;
                }
              } else if (_source38.is_Map) {
                DAST._IType _913___mcc_h371 = _source38.dtor_key;
                DAST._IType _914___mcc_h372 = _source38.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _915_recursiveGen;
                  bool _916_recOwned;
                  bool _917_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _918_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out510;
                  bool _out511;
                  bool _out512;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out513;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out510, out _out511, out _out512, out _out513);
                  _915_recursiveGen = _out510;
                  _916_recOwned = _out511;
                  _917_recErased = _out512;
                  _918_recIdents = _out513;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _915_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _916_recOwned;
                  isErased = _917_recErased;
                  readIdents = _918_recIdents;
                }
              } else if (_source38.is_Arrow) {
                Dafny.ISequence<DAST._IType> _919___mcc_h375 = _source38.dtor_args;
                DAST._IType _920___mcc_h376 = _source38.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _921_recursiveGen;
                  bool _922_recOwned;
                  bool _923_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _924_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out514;
                  bool _out515;
                  bool _out516;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out514, out _out515, out _out516, out _out517);
                  _921_recursiveGen = _out514;
                  _922_recOwned = _out515;
                  _923_recErased = _out516;
                  _924_recIdents = _out517;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _921_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _922_recOwned;
                  isErased = _923_recErased;
                  readIdents = _924_recIdents;
                }
              } else if (_source38.is_Primitive) {
                DAST._IPrimitive _925___mcc_h379 = _source38.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _926_recursiveGen;
                  bool _927_recOwned;
                  bool _928_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _929_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out518;
                  bool _out519;
                  bool _out520;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out518, out _out519, out _out520, out _out521);
                  _926_recursiveGen = _out518;
                  _927_recOwned = _out519;
                  _928_recErased = _out520;
                  _929_recIdents = _out521;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _926_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _927_recOwned;
                  isErased = _928_recErased;
                  readIdents = _929_recIdents;
                }
              } else if (_source38.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _930___mcc_h381 = _source38.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _931_recursiveGen;
                  bool _932_recOwned;
                  bool _933_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _934_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out522;
                  bool _out523;
                  bool _out524;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out522, out _out523, out _out524, out _out525);
                  _931_recursiveGen = _out522;
                  _932_recOwned = _out523;
                  _933_recErased = _out524;
                  _934_recIdents = _out525;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _931_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _932_recOwned;
                  isErased = _933_recErased;
                  readIdents = _934_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _935___mcc_h383 = _source38.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _936_recursiveGen;
                  bool _937_recOwned;
                  bool _938_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _939_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out526;
                  bool _out527;
                  bool _out528;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out526, out _out527, out _out528, out _out529);
                  _936_recursiveGen = _out526;
                  _937_recOwned = _out527;
                  _938_recErased = _out528;
                  _939_recIdents = _out529;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _936_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _937_recOwned;
                  isErased = _938_recErased;
                  readIdents = _939_recIdents;
                }
              }
            } else if (_source26.is_Set) {
              DAST._IType _940___mcc_h385 = _source26.dtor_element;
              DAST._IType _source40 = _468___mcc_h121;
              if (_source40.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _941___mcc_h388 = _source40.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _942___mcc_h389 = _source40.dtor_typeArgs;
                DAST._IResolvedType _943___mcc_h390 = _source40.dtor_resolved;
                DAST._IResolvedType _source41 = _943___mcc_h390;
                if (_source41.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _944___mcc_h394 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _945_recursiveGen;
                    bool _946_recOwned;
                    bool _947_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _948_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out530;
                    bool _out531;
                    bool _out532;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out530, out _out531, out _out532, out _out533);
                    _945_recursiveGen = _out530;
                    _946_recOwned = _out531;
                    _947_recErased = _out532;
                    _948_recIdents = _out533;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _945_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _946_recOwned;
                    isErased = _947_recErased;
                    readIdents = _948_recIdents;
                  }
                } else if (_source41.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _949___mcc_h396 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _950_recursiveGen;
                    bool _951_recOwned;
                    bool _952_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _953_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out534;
                    bool _out535;
                    bool _out536;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out537;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out534, out _out535, out _out536, out _out537);
                    _950_recursiveGen = _out534;
                    _951_recOwned = _out535;
                    _952_recErased = _out536;
                    _953_recIdents = _out537;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _950_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _951_recOwned;
                    isErased = _952_recErased;
                    readIdents = _953_recIdents;
                  }
                } else {
                  DAST._IType _954___mcc_h398 = _source41.dtor_Newtype_a0;
                  DAST._IType _955_b = _954___mcc_h398;
                  {
                    if (object.Equals(_461_fromTpe, _955_b)) {
                      Dafny.ISequence<Dafny.Rune> _956_recursiveGen;
                      bool _957_recOwned;
                      bool _958_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _959_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out538;
                      bool _out539;
                      bool _out540;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out538, out _out539, out _out540, out _out541);
                      _956_recursiveGen = _out538;
                      _957_recOwned = _out539;
                      _958_recErased = _out540;
                      _959_recIdents = _out541;
                      Dafny.ISequence<Dafny.Rune> _960_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out542;
                      _out542 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _960_rhsType = _out542;
                      Dafny.ISequence<Dafny.Rune> _961_uneraseFn;
                      _961_uneraseFn = ((_957_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _960_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _961_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _956_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _957_recOwned;
                      isErased = false;
                      readIdents = _959_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out543;
                      bool _out544;
                      bool _out545;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _955_b), _955_b, _460_toTpe), @params, mustOwn, out _out543, out _out544, out _out545, out _out546);
                      s = _out543;
                      isOwned = _out544;
                      isErased = _out545;
                      readIdents = _out546;
                    }
                  }
                }
              } else if (_source40.is_Tuple) {
                Dafny.ISequence<DAST._IType> _962___mcc_h400 = _source40.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _963_recursiveGen;
                  bool _964_recOwned;
                  bool _965_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _966_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out547;
                  bool _out548;
                  bool _out549;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out547, out _out548, out _out549, out _out550);
                  _963_recursiveGen = _out547;
                  _964_recOwned = _out548;
                  _965_recErased = _out549;
                  _966_recIdents = _out550;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _963_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _964_recOwned;
                  isErased = _965_recErased;
                  readIdents = _966_recIdents;
                }
              } else if (_source40.is_Array) {
                DAST._IType _967___mcc_h402 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _968_recursiveGen;
                  bool _969_recOwned;
                  bool _970_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _971_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out551;
                  bool _out552;
                  bool _out553;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out551, out _out552, out _out553, out _out554);
                  _968_recursiveGen = _out551;
                  _969_recOwned = _out552;
                  _970_recErased = _out553;
                  _971_recIdents = _out554;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _968_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _969_recOwned;
                  isErased = _970_recErased;
                  readIdents = _971_recIdents;
                }
              } else if (_source40.is_Seq) {
                DAST._IType _972___mcc_h404 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _973_recursiveGen;
                  bool _974_recOwned;
                  bool _975_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _976_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out555;
                  bool _out556;
                  bool _out557;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out558;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out555, out _out556, out _out557, out _out558);
                  _973_recursiveGen = _out555;
                  _974_recOwned = _out556;
                  _975_recErased = _out557;
                  _976_recIdents = _out558;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _973_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _974_recOwned;
                  isErased = _975_recErased;
                  readIdents = _976_recIdents;
                }
              } else if (_source40.is_Set) {
                DAST._IType _977___mcc_h406 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _978_recursiveGen;
                  bool _979_recOwned;
                  bool _980_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _981_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out559;
                  bool _out560;
                  bool _out561;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out559, out _out560, out _out561, out _out562);
                  _978_recursiveGen = _out559;
                  _979_recOwned = _out560;
                  _980_recErased = _out561;
                  _981_recIdents = _out562;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _978_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _979_recOwned;
                  isErased = _980_recErased;
                  readIdents = _981_recIdents;
                }
              } else if (_source40.is_Multiset) {
                DAST._IType _982___mcc_h408 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _983_recursiveGen;
                  bool _984_recOwned;
                  bool _985_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _986_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out563;
                  bool _out564;
                  bool _out565;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out566;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out563, out _out564, out _out565, out _out566);
                  _983_recursiveGen = _out563;
                  _984_recOwned = _out564;
                  _985_recErased = _out565;
                  _986_recIdents = _out566;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _983_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _984_recOwned;
                  isErased = _985_recErased;
                  readIdents = _986_recIdents;
                }
              } else if (_source40.is_Map) {
                DAST._IType _987___mcc_h410 = _source40.dtor_key;
                DAST._IType _988___mcc_h411 = _source40.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _989_recursiveGen;
                  bool _990_recOwned;
                  bool _991_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _992_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out567;
                  bool _out568;
                  bool _out569;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out570;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out567, out _out568, out _out569, out _out570);
                  _989_recursiveGen = _out567;
                  _990_recOwned = _out568;
                  _991_recErased = _out569;
                  _992_recIdents = _out570;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _989_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _990_recOwned;
                  isErased = _991_recErased;
                  readIdents = _992_recIdents;
                }
              } else if (_source40.is_Arrow) {
                Dafny.ISequence<DAST._IType> _993___mcc_h414 = _source40.dtor_args;
                DAST._IType _994___mcc_h415 = _source40.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _995_recursiveGen;
                  bool _996_recOwned;
                  bool _997_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _998_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out571;
                  bool _out572;
                  bool _out573;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out571, out _out572, out _out573, out _out574);
                  _995_recursiveGen = _out571;
                  _996_recOwned = _out572;
                  _997_recErased = _out573;
                  _998_recIdents = _out574;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _995_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _996_recOwned;
                  isErased = _997_recErased;
                  readIdents = _998_recIdents;
                }
              } else if (_source40.is_Primitive) {
                DAST._IPrimitive _999___mcc_h418 = _source40.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1000_recursiveGen;
                  bool _1001_recOwned;
                  bool _1002_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1003_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out575;
                  bool _out576;
                  bool _out577;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out575, out _out576, out _out577, out _out578);
                  _1000_recursiveGen = _out575;
                  _1001_recOwned = _out576;
                  _1002_recErased = _out577;
                  _1003_recIdents = _out578;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1000_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1001_recOwned;
                  isErased = _1002_recErased;
                  readIdents = _1003_recIdents;
                }
              } else if (_source40.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1004___mcc_h420 = _source40.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1005_recursiveGen;
                  bool _1006_recOwned;
                  bool _1007_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1008_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out579;
                  bool _out580;
                  bool _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out579, out _out580, out _out581, out _out582);
                  _1005_recursiveGen = _out579;
                  _1006_recOwned = _out580;
                  _1007_recErased = _out581;
                  _1008_recIdents = _out582;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1005_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1006_recOwned;
                  isErased = _1007_recErased;
                  readIdents = _1008_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1009___mcc_h422 = _source40.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1010_recursiveGen;
                  bool _1011_recOwned;
                  bool _1012_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1013_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out583;
                  bool _out584;
                  bool _out585;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out583, out _out584, out _out585, out _out586);
                  _1010_recursiveGen = _out583;
                  _1011_recOwned = _out584;
                  _1012_recErased = _out585;
                  _1013_recIdents = _out586;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1010_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1011_recOwned;
                  isErased = _1012_recErased;
                  readIdents = _1013_recIdents;
                }
              }
            } else if (_source26.is_Multiset) {
              DAST._IType _1014___mcc_h424 = _source26.dtor_element;
              DAST._IType _source42 = _468___mcc_h121;
              if (_source42.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1015___mcc_h427 = _source42.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1016___mcc_h428 = _source42.dtor_typeArgs;
                DAST._IResolvedType _1017___mcc_h429 = _source42.dtor_resolved;
                DAST._IResolvedType _source43 = _1017___mcc_h429;
                if (_source43.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1018___mcc_h433 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1019_recursiveGen;
                    bool _1020_recOwned;
                    bool _1021_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1022_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out587;
                    bool _out588;
                    bool _out589;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out587, out _out588, out _out589, out _out590);
                    _1019_recursiveGen = _out587;
                    _1020_recOwned = _out588;
                    _1021_recErased = _out589;
                    _1022_recIdents = _out590;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1019_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1020_recOwned;
                    isErased = _1021_recErased;
                    readIdents = _1022_recIdents;
                  }
                } else if (_source43.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1023___mcc_h435 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1024_recursiveGen;
                    bool _1025_recOwned;
                    bool _1026_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1027_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out591;
                    bool _out592;
                    bool _out593;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out591, out _out592, out _out593, out _out594);
                    _1024_recursiveGen = _out591;
                    _1025_recOwned = _out592;
                    _1026_recErased = _out593;
                    _1027_recIdents = _out594;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1024_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1025_recOwned;
                    isErased = _1026_recErased;
                    readIdents = _1027_recIdents;
                  }
                } else {
                  DAST._IType _1028___mcc_h437 = _source43.dtor_Newtype_a0;
                  DAST._IType _1029_b = _1028___mcc_h437;
                  {
                    if (object.Equals(_461_fromTpe, _1029_b)) {
                      Dafny.ISequence<Dafny.Rune> _1030_recursiveGen;
                      bool _1031_recOwned;
                      bool _1032_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1033_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out595;
                      bool _out596;
                      bool _out597;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out595, out _out596, out _out597, out _out598);
                      _1030_recursiveGen = _out595;
                      _1031_recOwned = _out596;
                      _1032_recErased = _out597;
                      _1033_recIdents = _out598;
                      Dafny.ISequence<Dafny.Rune> _1034_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out599;
                      _out599 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _1034_rhsType = _out599;
                      Dafny.ISequence<Dafny.Rune> _1035_uneraseFn;
                      _1035_uneraseFn = ((_1031_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1034_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1035_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1030_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1031_recOwned;
                      isErased = false;
                      readIdents = _1033_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out600;
                      bool _out601;
                      bool _out602;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out603;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1029_b), _1029_b, _460_toTpe), @params, mustOwn, out _out600, out _out601, out _out602, out _out603);
                      s = _out600;
                      isOwned = _out601;
                      isErased = _out602;
                      readIdents = _out603;
                    }
                  }
                }
              } else if (_source42.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1036___mcc_h439 = _source42.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1037_recursiveGen;
                  bool _1038_recOwned;
                  bool _1039_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1040_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out604;
                  bool _out605;
                  bool _out606;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out604, out _out605, out _out606, out _out607);
                  _1037_recursiveGen = _out604;
                  _1038_recOwned = _out605;
                  _1039_recErased = _out606;
                  _1040_recIdents = _out607;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1037_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1038_recOwned;
                  isErased = _1039_recErased;
                  readIdents = _1040_recIdents;
                }
              } else if (_source42.is_Array) {
                DAST._IType _1041___mcc_h441 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1042_recursiveGen;
                  bool _1043_recOwned;
                  bool _1044_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1045_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out608;
                  bool _out609;
                  bool _out610;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out611;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out608, out _out609, out _out610, out _out611);
                  _1042_recursiveGen = _out608;
                  _1043_recOwned = _out609;
                  _1044_recErased = _out610;
                  _1045_recIdents = _out611;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1042_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1043_recOwned;
                  isErased = _1044_recErased;
                  readIdents = _1045_recIdents;
                }
              } else if (_source42.is_Seq) {
                DAST._IType _1046___mcc_h443 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1047_recursiveGen;
                  bool _1048_recOwned;
                  bool _1049_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1050_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out612;
                  bool _out613;
                  bool _out614;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out615;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out612, out _out613, out _out614, out _out615);
                  _1047_recursiveGen = _out612;
                  _1048_recOwned = _out613;
                  _1049_recErased = _out614;
                  _1050_recIdents = _out615;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1047_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1048_recOwned;
                  isErased = _1049_recErased;
                  readIdents = _1050_recIdents;
                }
              } else if (_source42.is_Set) {
                DAST._IType _1051___mcc_h445 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1052_recursiveGen;
                  bool _1053_recOwned;
                  bool _1054_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1055_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out616;
                  bool _out617;
                  bool _out618;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out616, out _out617, out _out618, out _out619);
                  _1052_recursiveGen = _out616;
                  _1053_recOwned = _out617;
                  _1054_recErased = _out618;
                  _1055_recIdents = _out619;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1052_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1053_recOwned;
                  isErased = _1054_recErased;
                  readIdents = _1055_recIdents;
                }
              } else if (_source42.is_Multiset) {
                DAST._IType _1056___mcc_h447 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1057_recursiveGen;
                  bool _1058_recOwned;
                  bool _1059_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1060_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out620;
                  bool _out621;
                  bool _out622;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out623;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out620, out _out621, out _out622, out _out623);
                  _1057_recursiveGen = _out620;
                  _1058_recOwned = _out621;
                  _1059_recErased = _out622;
                  _1060_recIdents = _out623;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1057_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1058_recOwned;
                  isErased = _1059_recErased;
                  readIdents = _1060_recIdents;
                }
              } else if (_source42.is_Map) {
                DAST._IType _1061___mcc_h449 = _source42.dtor_key;
                DAST._IType _1062___mcc_h450 = _source42.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1063_recursiveGen;
                  bool _1064_recOwned;
                  bool _1065_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1066_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out624;
                  bool _out625;
                  bool _out626;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out624, out _out625, out _out626, out _out627);
                  _1063_recursiveGen = _out624;
                  _1064_recOwned = _out625;
                  _1065_recErased = _out626;
                  _1066_recIdents = _out627;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1063_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1064_recOwned;
                  isErased = _1065_recErased;
                  readIdents = _1066_recIdents;
                }
              } else if (_source42.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1067___mcc_h453 = _source42.dtor_args;
                DAST._IType _1068___mcc_h454 = _source42.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1069_recursiveGen;
                  bool _1070_recOwned;
                  bool _1071_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1072_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out628;
                  bool _out629;
                  bool _out630;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out631;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out628, out _out629, out _out630, out _out631);
                  _1069_recursiveGen = _out628;
                  _1070_recOwned = _out629;
                  _1071_recErased = _out630;
                  _1072_recIdents = _out631;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1069_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1070_recOwned;
                  isErased = _1071_recErased;
                  readIdents = _1072_recIdents;
                }
              } else if (_source42.is_Primitive) {
                DAST._IPrimitive _1073___mcc_h457 = _source42.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1074_recursiveGen;
                  bool _1075_recOwned;
                  bool _1076_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1077_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out632;
                  bool _out633;
                  bool _out634;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out635;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out632, out _out633, out _out634, out _out635);
                  _1074_recursiveGen = _out632;
                  _1075_recOwned = _out633;
                  _1076_recErased = _out634;
                  _1077_recIdents = _out635;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1074_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1075_recOwned;
                  isErased = _1076_recErased;
                  readIdents = _1077_recIdents;
                }
              } else if (_source42.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1078___mcc_h459 = _source42.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1079_recursiveGen;
                  bool _1080_recOwned;
                  bool _1081_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1082_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out636;
                  bool _out637;
                  bool _out638;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out636, out _out637, out _out638, out _out639);
                  _1079_recursiveGen = _out636;
                  _1080_recOwned = _out637;
                  _1081_recErased = _out638;
                  _1082_recIdents = _out639;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1079_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1080_recOwned;
                  isErased = _1081_recErased;
                  readIdents = _1082_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1083___mcc_h461 = _source42.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1084_recursiveGen;
                  bool _1085_recOwned;
                  bool _1086_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1087_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out640;
                  bool _out641;
                  bool _out642;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out640, out _out641, out _out642, out _out643);
                  _1084_recursiveGen = _out640;
                  _1085_recOwned = _out641;
                  _1086_recErased = _out642;
                  _1087_recIdents = _out643;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1084_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1085_recOwned;
                  isErased = _1086_recErased;
                  readIdents = _1087_recIdents;
                }
              }
            } else if (_source26.is_Map) {
              DAST._IType _1088___mcc_h463 = _source26.dtor_key;
              DAST._IType _1089___mcc_h464 = _source26.dtor_value;
              DAST._IType _source44 = _468___mcc_h121;
              if (_source44.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1090___mcc_h469 = _source44.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1091___mcc_h470 = _source44.dtor_typeArgs;
                DAST._IResolvedType _1092___mcc_h471 = _source44.dtor_resolved;
                DAST._IResolvedType _source45 = _1092___mcc_h471;
                if (_source45.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1093___mcc_h475 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1094_recursiveGen;
                    bool _1095_recOwned;
                    bool _1096_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1097_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out644;
                    bool _out645;
                    bool _out646;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out644, out _out645, out _out646, out _out647);
                    _1094_recursiveGen = _out644;
                    _1095_recOwned = _out645;
                    _1096_recErased = _out646;
                    _1097_recIdents = _out647;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1094_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1095_recOwned;
                    isErased = _1096_recErased;
                    readIdents = _1097_recIdents;
                  }
                } else if (_source45.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1098___mcc_h477 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1099_recursiveGen;
                    bool _1100_recOwned;
                    bool _1101_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1102_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out648;
                    bool _out649;
                    bool _out650;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out651;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out648, out _out649, out _out650, out _out651);
                    _1099_recursiveGen = _out648;
                    _1100_recOwned = _out649;
                    _1101_recErased = _out650;
                    _1102_recIdents = _out651;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1099_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1100_recOwned;
                    isErased = _1101_recErased;
                    readIdents = _1102_recIdents;
                  }
                } else {
                  DAST._IType _1103___mcc_h479 = _source45.dtor_Newtype_a0;
                  DAST._IType _1104_b = _1103___mcc_h479;
                  {
                    if (object.Equals(_461_fromTpe, _1104_b)) {
                      Dafny.ISequence<Dafny.Rune> _1105_recursiveGen;
                      bool _1106_recOwned;
                      bool _1107_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1108_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out652;
                      bool _out653;
                      bool _out654;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out652, out _out653, out _out654, out _out655);
                      _1105_recursiveGen = _out652;
                      _1106_recOwned = _out653;
                      _1107_recErased = _out654;
                      _1108_recIdents = _out655;
                      Dafny.ISequence<Dafny.Rune> _1109_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out656;
                      _out656 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _1109_rhsType = _out656;
                      Dafny.ISequence<Dafny.Rune> _1110_uneraseFn;
                      _1110_uneraseFn = ((_1106_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1109_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1110_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1105_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1106_recOwned;
                      isErased = false;
                      readIdents = _1108_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out657;
                      bool _out658;
                      bool _out659;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1104_b), _1104_b, _460_toTpe), @params, mustOwn, out _out657, out _out658, out _out659, out _out660);
                      s = _out657;
                      isOwned = _out658;
                      isErased = _out659;
                      readIdents = _out660;
                    }
                  }
                }
              } else if (_source44.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1111___mcc_h481 = _source44.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1112_recursiveGen;
                  bool _1113_recOwned;
                  bool _1114_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1115_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out661;
                  bool _out662;
                  bool _out663;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out664;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out661, out _out662, out _out663, out _out664);
                  _1112_recursiveGen = _out661;
                  _1113_recOwned = _out662;
                  _1114_recErased = _out663;
                  _1115_recIdents = _out664;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1112_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1113_recOwned;
                  isErased = _1114_recErased;
                  readIdents = _1115_recIdents;
                }
              } else if (_source44.is_Array) {
                DAST._IType _1116___mcc_h483 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1117_recursiveGen;
                  bool _1118_recOwned;
                  bool _1119_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1120_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out665;
                  bool _out666;
                  bool _out667;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out668;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out665, out _out666, out _out667, out _out668);
                  _1117_recursiveGen = _out665;
                  _1118_recOwned = _out666;
                  _1119_recErased = _out667;
                  _1120_recIdents = _out668;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1117_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1118_recOwned;
                  isErased = _1119_recErased;
                  readIdents = _1120_recIdents;
                }
              } else if (_source44.is_Seq) {
                DAST._IType _1121___mcc_h485 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1122_recursiveGen;
                  bool _1123_recOwned;
                  bool _1124_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1125_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out669;
                  bool _out670;
                  bool _out671;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out672;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out669, out _out670, out _out671, out _out672);
                  _1122_recursiveGen = _out669;
                  _1123_recOwned = _out670;
                  _1124_recErased = _out671;
                  _1125_recIdents = _out672;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1122_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1123_recOwned;
                  isErased = _1124_recErased;
                  readIdents = _1125_recIdents;
                }
              } else if (_source44.is_Set) {
                DAST._IType _1126___mcc_h487 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1127_recursiveGen;
                  bool _1128_recOwned;
                  bool _1129_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1130_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out673;
                  bool _out674;
                  bool _out675;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out676;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out673, out _out674, out _out675, out _out676);
                  _1127_recursiveGen = _out673;
                  _1128_recOwned = _out674;
                  _1129_recErased = _out675;
                  _1130_recIdents = _out676;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1127_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1128_recOwned;
                  isErased = _1129_recErased;
                  readIdents = _1130_recIdents;
                }
              } else if (_source44.is_Multiset) {
                DAST._IType _1131___mcc_h489 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1132_recursiveGen;
                  bool _1133_recOwned;
                  bool _1134_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1135_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out677;
                  bool _out678;
                  bool _out679;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out680;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out677, out _out678, out _out679, out _out680);
                  _1132_recursiveGen = _out677;
                  _1133_recOwned = _out678;
                  _1134_recErased = _out679;
                  _1135_recIdents = _out680;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1132_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1133_recOwned;
                  isErased = _1134_recErased;
                  readIdents = _1135_recIdents;
                }
              } else if (_source44.is_Map) {
                DAST._IType _1136___mcc_h491 = _source44.dtor_key;
                DAST._IType _1137___mcc_h492 = _source44.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1138_recursiveGen;
                  bool _1139_recOwned;
                  bool _1140_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1141_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out681;
                  bool _out682;
                  bool _out683;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out684;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out681, out _out682, out _out683, out _out684);
                  _1138_recursiveGen = _out681;
                  _1139_recOwned = _out682;
                  _1140_recErased = _out683;
                  _1141_recIdents = _out684;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1138_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1139_recOwned;
                  isErased = _1140_recErased;
                  readIdents = _1141_recIdents;
                }
              } else if (_source44.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1142___mcc_h495 = _source44.dtor_args;
                DAST._IType _1143___mcc_h496 = _source44.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1144_recursiveGen;
                  bool _1145_recOwned;
                  bool _1146_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1147_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out685;
                  bool _out686;
                  bool _out687;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out688;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out685, out _out686, out _out687, out _out688);
                  _1144_recursiveGen = _out685;
                  _1145_recOwned = _out686;
                  _1146_recErased = _out687;
                  _1147_recIdents = _out688;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1144_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1145_recOwned;
                  isErased = _1146_recErased;
                  readIdents = _1147_recIdents;
                }
              } else if (_source44.is_Primitive) {
                DAST._IPrimitive _1148___mcc_h499 = _source44.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1149_recursiveGen;
                  bool _1150_recOwned;
                  bool _1151_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1152_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out689;
                  bool _out690;
                  bool _out691;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out692;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out689, out _out690, out _out691, out _out692);
                  _1149_recursiveGen = _out689;
                  _1150_recOwned = _out690;
                  _1151_recErased = _out691;
                  _1152_recIdents = _out692;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1149_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1150_recOwned;
                  isErased = _1151_recErased;
                  readIdents = _1152_recIdents;
                }
              } else if (_source44.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1153___mcc_h501 = _source44.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1154_recursiveGen;
                  bool _1155_recOwned;
                  bool _1156_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1157_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out693;
                  bool _out694;
                  bool _out695;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out696;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out693, out _out694, out _out695, out _out696);
                  _1154_recursiveGen = _out693;
                  _1155_recOwned = _out694;
                  _1156_recErased = _out695;
                  _1157_recIdents = _out696;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1154_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1155_recOwned;
                  isErased = _1156_recErased;
                  readIdents = _1157_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1158___mcc_h503 = _source44.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1159_recursiveGen;
                  bool _1160_recOwned;
                  bool _1161_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1162_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out697;
                  bool _out698;
                  bool _out699;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out697, out _out698, out _out699, out _out700);
                  _1159_recursiveGen = _out697;
                  _1160_recOwned = _out698;
                  _1161_recErased = _out699;
                  _1162_recIdents = _out700;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1159_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1160_recOwned;
                  isErased = _1161_recErased;
                  readIdents = _1162_recIdents;
                }
              }
            } else if (_source26.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1163___mcc_h505 = _source26.dtor_args;
              DAST._IType _1164___mcc_h506 = _source26.dtor_result;
              DAST._IType _source46 = _468___mcc_h121;
              if (_source46.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1165___mcc_h511 = _source46.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1166___mcc_h512 = _source46.dtor_typeArgs;
                DAST._IResolvedType _1167___mcc_h513 = _source46.dtor_resolved;
                DAST._IResolvedType _source47 = _1167___mcc_h513;
                if (_source47.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1168___mcc_h517 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1169_recursiveGen;
                    bool _1170_recOwned;
                    bool _1171_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1172_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out701;
                    bool _out702;
                    bool _out703;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out704;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out701, out _out702, out _out703, out _out704);
                    _1169_recursiveGen = _out701;
                    _1170_recOwned = _out702;
                    _1171_recErased = _out703;
                    _1172_recIdents = _out704;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1169_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1170_recOwned;
                    isErased = _1171_recErased;
                    readIdents = _1172_recIdents;
                  }
                } else if (_source47.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1173___mcc_h519 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1174_recursiveGen;
                    bool _1175_recOwned;
                    bool _1176_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1177_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out705;
                    bool _out706;
                    bool _out707;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out708;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out705, out _out706, out _out707, out _out708);
                    _1174_recursiveGen = _out705;
                    _1175_recOwned = _out706;
                    _1176_recErased = _out707;
                    _1177_recIdents = _out708;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1174_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1175_recOwned;
                    isErased = _1176_recErased;
                    readIdents = _1177_recIdents;
                  }
                } else {
                  DAST._IType _1178___mcc_h521 = _source47.dtor_Newtype_a0;
                  DAST._IType _1179_b = _1178___mcc_h521;
                  {
                    if (object.Equals(_461_fromTpe, _1179_b)) {
                      Dafny.ISequence<Dafny.Rune> _1180_recursiveGen;
                      bool _1181_recOwned;
                      bool _1182_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1183_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out709;
                      bool _out710;
                      bool _out711;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out709, out _out710, out _out711, out _out712);
                      _1180_recursiveGen = _out709;
                      _1181_recOwned = _out710;
                      _1182_recErased = _out711;
                      _1183_recIdents = _out712;
                      Dafny.ISequence<Dafny.Rune> _1184_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out713;
                      _out713 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _1184_rhsType = _out713;
                      Dafny.ISequence<Dafny.Rune> _1185_uneraseFn;
                      _1185_uneraseFn = ((_1181_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1184_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1185_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1180_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1181_recOwned;
                      isErased = false;
                      readIdents = _1183_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out714;
                      bool _out715;
                      bool _out716;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out717;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1179_b), _1179_b, _460_toTpe), @params, mustOwn, out _out714, out _out715, out _out716, out _out717);
                      s = _out714;
                      isOwned = _out715;
                      isErased = _out716;
                      readIdents = _out717;
                    }
                  }
                }
              } else if (_source46.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1186___mcc_h523 = _source46.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1187_recursiveGen;
                  bool _1188_recOwned;
                  bool _1189_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1190_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out718;
                  bool _out719;
                  bool _out720;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out721;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out718, out _out719, out _out720, out _out721);
                  _1187_recursiveGen = _out718;
                  _1188_recOwned = _out719;
                  _1189_recErased = _out720;
                  _1190_recIdents = _out721;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1187_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1188_recOwned;
                  isErased = _1189_recErased;
                  readIdents = _1190_recIdents;
                }
              } else if (_source46.is_Array) {
                DAST._IType _1191___mcc_h525 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1192_recursiveGen;
                  bool _1193_recOwned;
                  bool _1194_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1195_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out722;
                  bool _out723;
                  bool _out724;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out725;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out722, out _out723, out _out724, out _out725);
                  _1192_recursiveGen = _out722;
                  _1193_recOwned = _out723;
                  _1194_recErased = _out724;
                  _1195_recIdents = _out725;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1192_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1193_recOwned;
                  isErased = _1194_recErased;
                  readIdents = _1195_recIdents;
                }
              } else if (_source46.is_Seq) {
                DAST._IType _1196___mcc_h527 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1197_recursiveGen;
                  bool _1198_recOwned;
                  bool _1199_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1200_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out726;
                  bool _out727;
                  bool _out728;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out729;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out726, out _out727, out _out728, out _out729);
                  _1197_recursiveGen = _out726;
                  _1198_recOwned = _out727;
                  _1199_recErased = _out728;
                  _1200_recIdents = _out729;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1197_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1198_recOwned;
                  isErased = _1199_recErased;
                  readIdents = _1200_recIdents;
                }
              } else if (_source46.is_Set) {
                DAST._IType _1201___mcc_h529 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1202_recursiveGen;
                  bool _1203_recOwned;
                  bool _1204_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1205_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out730;
                  bool _out731;
                  bool _out732;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out733;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out730, out _out731, out _out732, out _out733);
                  _1202_recursiveGen = _out730;
                  _1203_recOwned = _out731;
                  _1204_recErased = _out732;
                  _1205_recIdents = _out733;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1202_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1203_recOwned;
                  isErased = _1204_recErased;
                  readIdents = _1205_recIdents;
                }
              } else if (_source46.is_Multiset) {
                DAST._IType _1206___mcc_h531 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1207_recursiveGen;
                  bool _1208_recOwned;
                  bool _1209_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1210_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out734;
                  bool _out735;
                  bool _out736;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out737;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out734, out _out735, out _out736, out _out737);
                  _1207_recursiveGen = _out734;
                  _1208_recOwned = _out735;
                  _1209_recErased = _out736;
                  _1210_recIdents = _out737;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1207_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1208_recOwned;
                  isErased = _1209_recErased;
                  readIdents = _1210_recIdents;
                }
              } else if (_source46.is_Map) {
                DAST._IType _1211___mcc_h533 = _source46.dtor_key;
                DAST._IType _1212___mcc_h534 = _source46.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1213_recursiveGen;
                  bool _1214_recOwned;
                  bool _1215_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1216_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out738;
                  bool _out739;
                  bool _out740;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out741;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out738, out _out739, out _out740, out _out741);
                  _1213_recursiveGen = _out738;
                  _1214_recOwned = _out739;
                  _1215_recErased = _out740;
                  _1216_recIdents = _out741;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1213_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1214_recOwned;
                  isErased = _1215_recErased;
                  readIdents = _1216_recIdents;
                }
              } else if (_source46.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1217___mcc_h537 = _source46.dtor_args;
                DAST._IType _1218___mcc_h538 = _source46.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1219_recursiveGen;
                  bool _1220_recOwned;
                  bool _1221_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1222_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out742;
                  bool _out743;
                  bool _out744;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out745;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out742, out _out743, out _out744, out _out745);
                  _1219_recursiveGen = _out742;
                  _1220_recOwned = _out743;
                  _1221_recErased = _out744;
                  _1222_recIdents = _out745;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1219_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1220_recOwned;
                  isErased = _1221_recErased;
                  readIdents = _1222_recIdents;
                }
              } else if (_source46.is_Primitive) {
                DAST._IPrimitive _1223___mcc_h541 = _source46.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1224_recursiveGen;
                  bool _1225_recOwned;
                  bool _1226_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1227_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out746;
                  bool _out747;
                  bool _out748;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out749;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out746, out _out747, out _out748, out _out749);
                  _1224_recursiveGen = _out746;
                  _1225_recOwned = _out747;
                  _1226_recErased = _out748;
                  _1227_recIdents = _out749;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1224_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1225_recOwned;
                  isErased = _1226_recErased;
                  readIdents = _1227_recIdents;
                }
              } else if (_source46.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1228___mcc_h543 = _source46.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1229_recursiveGen;
                  bool _1230_recOwned;
                  bool _1231_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1232_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out750;
                  bool _out751;
                  bool _out752;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out753;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out750, out _out751, out _out752, out _out753);
                  _1229_recursiveGen = _out750;
                  _1230_recOwned = _out751;
                  _1231_recErased = _out752;
                  _1232_recIdents = _out753;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1229_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1230_recOwned;
                  isErased = _1231_recErased;
                  readIdents = _1232_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1233___mcc_h545 = _source46.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1234_recursiveGen;
                  bool _1235_recOwned;
                  bool _1236_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1237_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out754;
                  bool _out755;
                  bool _out756;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out757;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out754, out _out755, out _out756, out _out757);
                  _1234_recursiveGen = _out754;
                  _1235_recOwned = _out755;
                  _1236_recErased = _out756;
                  _1237_recIdents = _out757;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1234_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1235_recOwned;
                  isErased = _1236_recErased;
                  readIdents = _1237_recIdents;
                }
              }
            } else if (_source26.is_Primitive) {
              DAST._IPrimitive _1238___mcc_h547 = _source26.dtor_Primitive_a0;
              DAST._IPrimitive _source48 = _1238___mcc_h547;
              if (_source48.is_Int) {
                DAST._IType _source49 = _468___mcc_h121;
                if (_source49.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1239___mcc_h550 = _source49.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1240___mcc_h551 = _source49.dtor_typeArgs;
                  DAST._IResolvedType _1241___mcc_h552 = _source49.dtor_resolved;
                  DAST._IResolvedType _source50 = _1241___mcc_h552;
                  if (_source50.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1242___mcc_h556 = _source50.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1243_recursiveGen;
                      bool _1244_recOwned;
                      bool _1245_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1246_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out758;
                      bool _out759;
                      bool _out760;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out761;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out758, out _out759, out _out760, out _out761);
                      _1243_recursiveGen = _out758;
                      _1244_recOwned = _out759;
                      _1245_recErased = _out760;
                      _1246_recIdents = _out761;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1243_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1244_recOwned;
                      isErased = _1245_recErased;
                      readIdents = _1246_recIdents;
                    }
                  } else if (_source50.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1247___mcc_h558 = _source50.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1248_recursiveGen;
                      bool _1249_recOwned;
                      bool _1250_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1251_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out762;
                      bool _out763;
                      bool _out764;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out762, out _out763, out _out764, out _out765);
                      _1248_recursiveGen = _out762;
                      _1249_recOwned = _out763;
                      _1250_recErased = _out764;
                      _1251_recIdents = _out765;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1248_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1249_recOwned;
                      isErased = _1250_recErased;
                      readIdents = _1251_recIdents;
                    }
                  } else {
                    DAST._IType _1252___mcc_h560 = _source50.dtor_Newtype_a0;
                    DAST._IType _1253_b = _1252___mcc_h560;
                    {
                      if (object.Equals(_461_fromTpe, _1253_b)) {
                        Dafny.ISequence<Dafny.Rune> _1254_recursiveGen;
                        bool _1255_recOwned;
                        bool _1256_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1257_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out766;
                        bool _out767;
                        bool _out768;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out766, out _out767, out _out768, out _out769);
                        _1254_recursiveGen = _out766;
                        _1255_recOwned = _out767;
                        _1256_recErased = _out768;
                        _1257_recIdents = _out769;
                        Dafny.ISequence<Dafny.Rune> _1258_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out770;
                        _out770 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _1258_rhsType = _out770;
                        Dafny.ISequence<Dafny.Rune> _1259_uneraseFn;
                        _1259_uneraseFn = ((_1255_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1258_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1259_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1254_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1255_recOwned;
                        isErased = false;
                        readIdents = _1257_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out771;
                        bool _out772;
                        bool _out773;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out774;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1253_b), _1253_b, _460_toTpe), @params, mustOwn, out _out771, out _out772, out _out773, out _out774);
                        s = _out771;
                        isOwned = _out772;
                        isErased = _out773;
                        readIdents = _out774;
                      }
                    }
                  }
                } else if (_source49.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1260___mcc_h562 = _source49.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1261_recursiveGen;
                    bool _1262_recOwned;
                    bool _1263_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1264_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out775;
                    bool _out776;
                    bool _out777;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out778;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out775, out _out776, out _out777, out _out778);
                    _1261_recursiveGen = _out775;
                    _1262_recOwned = _out776;
                    _1263_recErased = _out777;
                    _1264_recIdents = _out778;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1261_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1262_recOwned;
                    isErased = _1263_recErased;
                    readIdents = _1264_recIdents;
                  }
                } else if (_source49.is_Array) {
                  DAST._IType _1265___mcc_h564 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1266_recursiveGen;
                    bool _1267_recOwned;
                    bool _1268_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1269_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out779;
                    bool _out780;
                    bool _out781;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out782;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out779, out _out780, out _out781, out _out782);
                    _1266_recursiveGen = _out779;
                    _1267_recOwned = _out780;
                    _1268_recErased = _out781;
                    _1269_recIdents = _out782;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1266_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1267_recOwned;
                    isErased = _1268_recErased;
                    readIdents = _1269_recIdents;
                  }
                } else if (_source49.is_Seq) {
                  DAST._IType _1270___mcc_h566 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1271_recursiveGen;
                    bool _1272_recOwned;
                    bool _1273_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1274_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out783;
                    bool _out784;
                    bool _out785;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out786;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out783, out _out784, out _out785, out _out786);
                    _1271_recursiveGen = _out783;
                    _1272_recOwned = _out784;
                    _1273_recErased = _out785;
                    _1274_recIdents = _out786;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1271_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1272_recOwned;
                    isErased = _1273_recErased;
                    readIdents = _1274_recIdents;
                  }
                } else if (_source49.is_Set) {
                  DAST._IType _1275___mcc_h568 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1276_recursiveGen;
                    bool _1277_recOwned;
                    bool _1278_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1279_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out787;
                    bool _out788;
                    bool _out789;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out790;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out787, out _out788, out _out789, out _out790);
                    _1276_recursiveGen = _out787;
                    _1277_recOwned = _out788;
                    _1278_recErased = _out789;
                    _1279_recIdents = _out790;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1276_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1277_recOwned;
                    isErased = _1278_recErased;
                    readIdents = _1279_recIdents;
                  }
                } else if (_source49.is_Multiset) {
                  DAST._IType _1280___mcc_h570 = _source49.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1281_recursiveGen;
                    bool _1282_recOwned;
                    bool _1283_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1284_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out791;
                    bool _out792;
                    bool _out793;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out794;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out791, out _out792, out _out793, out _out794);
                    _1281_recursiveGen = _out791;
                    _1282_recOwned = _out792;
                    _1283_recErased = _out793;
                    _1284_recIdents = _out794;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1281_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1282_recOwned;
                    isErased = _1283_recErased;
                    readIdents = _1284_recIdents;
                  }
                } else if (_source49.is_Map) {
                  DAST._IType _1285___mcc_h572 = _source49.dtor_key;
                  DAST._IType _1286___mcc_h573 = _source49.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1287_recursiveGen;
                    bool _1288_recOwned;
                    bool _1289_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1290_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out795;
                    bool _out796;
                    bool _out797;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out798;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out795, out _out796, out _out797, out _out798);
                    _1287_recursiveGen = _out795;
                    _1288_recOwned = _out796;
                    _1289_recErased = _out797;
                    _1290_recIdents = _out798;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1287_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1288_recOwned;
                    isErased = _1289_recErased;
                    readIdents = _1290_recIdents;
                  }
                } else if (_source49.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1291___mcc_h576 = _source49.dtor_args;
                  DAST._IType _1292___mcc_h577 = _source49.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1293_recursiveGen;
                    bool _1294_recOwned;
                    bool _1295_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1296_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out799;
                    bool _out800;
                    bool _out801;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out802;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out799, out _out800, out _out801, out _out802);
                    _1293_recursiveGen = _out799;
                    _1294_recOwned = _out800;
                    _1295_recErased = _out801;
                    _1296_recIdents = _out802;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1293_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1294_recOwned;
                    isErased = _1295_recErased;
                    readIdents = _1296_recIdents;
                  }
                } else if (_source49.is_Primitive) {
                  DAST._IPrimitive _1297___mcc_h580 = _source49.dtor_Primitive_a0;
                  DAST._IPrimitive _source51 = _1297___mcc_h580;
                  if (_source51.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1298_recursiveGen;
                      bool _1299_recOwned;
                      bool _1300_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1301_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out803;
                      bool _out804;
                      bool _out805;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out806;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out803, out _out804, out _out805, out _out806);
                      _1298_recursiveGen = _out803;
                      _1299_recOwned = _out804;
                      _1300_recErased = _out805;
                      _1301_recIdents = _out806;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1298_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1299_recOwned;
                      isErased = _1300_recErased;
                      readIdents = _1301_recIdents;
                    }
                  } else if (_source51.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1302_recursiveGen;
                      bool _1303___v39;
                      bool _1304___v40;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1305_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out807;
                      bool _out808;
                      bool _out809;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out810;
                      DCOMP.COMP.GenExpr(_462_expr, @params, true, out _out807, out _out808, out _out809, out _out810);
                      _1302_recursiveGen = _out807;
                      _1303___v39 = _out808;
                      _1304___v40 = _out809;
                      _1305_recIdents = _out810;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1302_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1305_recIdents;
                    }
                  } else if (_source51.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1306_recursiveGen;
                      bool _1307_recOwned;
                      bool _1308_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1309_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out811;
                      bool _out812;
                      bool _out813;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out814;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out811, out _out812, out _out813, out _out814);
                      _1306_recursiveGen = _out811;
                      _1307_recOwned = _out812;
                      _1308_recErased = _out813;
                      _1309_recIdents = _out814;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1306_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1307_recOwned;
                      isErased = _1308_recErased;
                      readIdents = _1309_recIdents;
                    }
                  } else if (_source51.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1310_recursiveGen;
                      bool _1311_recOwned;
                      bool _1312_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1313_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out815;
                      bool _out816;
                      bool _out817;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out818;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out815, out _out816, out _out817, out _out818);
                      _1310_recursiveGen = _out815;
                      _1311_recOwned = _out816;
                      _1312_recErased = _out817;
                      _1313_recIdents = _out818;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1310_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1311_recOwned;
                      isErased = _1312_recErased;
                      readIdents = _1313_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1314_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out819;
                      _out819 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _1314_rhsType = _out819;
                      Dafny.ISequence<Dafny.Rune> _1315_recursiveGen;
                      bool _1316___v49;
                      bool _1317___v50;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1318_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out820;
                      bool _out821;
                      bool _out822;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out823;
                      DCOMP.COMP.GenExpr(_462_expr, @params, true, out _out820, out _out821, out _out822, out _out823);
                      _1315_recursiveGen = _out820;
                      _1316___v49 = _out821;
                      _1317___v50 = _out822;
                      _1318_recIdents = _out823;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1315_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1318_recIdents;
                    }
                  }
                } else if (_source49.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1319___mcc_h582 = _source49.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1320_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out824;
                    _out824 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                    _1320_rhsType = _out824;
                    Dafny.ISequence<Dafny.Rune> _1321_recursiveGen;
                    bool _1322___v44;
                    bool _1323___v45;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1324_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out825;
                    bool _out826;
                    bool _out827;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out828;
                    DCOMP.COMP.GenExpr(_462_expr, @params, true, out _out825, out _out826, out _out827, out _out828);
                    _1321_recursiveGen = _out825;
                    _1322___v44 = _out826;
                    _1323___v45 = _out827;
                    _1324_recIdents = _out828;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1320_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1321_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1324_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1325___mcc_h584 = _source49.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1326_recursiveGen;
                    bool _1327_recOwned;
                    bool _1328_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1329_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out829;
                    bool _out830;
                    bool _out831;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out832;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out829, out _out830, out _out831, out _out832);
                    _1326_recursiveGen = _out829;
                    _1327_recOwned = _out830;
                    _1328_recErased = _out831;
                    _1329_recIdents = _out832;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1326_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1327_recOwned;
                    isErased = _1328_recErased;
                    readIdents = _1329_recIdents;
                  }
                }
              } else if (_source48.is_Real) {
                DAST._IType _source52 = _468___mcc_h121;
                if (_source52.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1330___mcc_h586 = _source52.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1331___mcc_h587 = _source52.dtor_typeArgs;
                  DAST._IResolvedType _1332___mcc_h588 = _source52.dtor_resolved;
                  DAST._IResolvedType _source53 = _1332___mcc_h588;
                  if (_source53.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1333___mcc_h592 = _source53.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1334_recursiveGen;
                      bool _1335_recOwned;
                      bool _1336_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1337_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out833;
                      bool _out834;
                      bool _out835;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out836;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out833, out _out834, out _out835, out _out836);
                      _1334_recursiveGen = _out833;
                      _1335_recOwned = _out834;
                      _1336_recErased = _out835;
                      _1337_recIdents = _out836;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1334_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1335_recOwned;
                      isErased = _1336_recErased;
                      readIdents = _1337_recIdents;
                    }
                  } else if (_source53.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1338___mcc_h594 = _source53.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1339_recursiveGen;
                      bool _1340_recOwned;
                      bool _1341_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1342_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out837;
                      bool _out838;
                      bool _out839;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out840;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out837, out _out838, out _out839, out _out840);
                      _1339_recursiveGen = _out837;
                      _1340_recOwned = _out838;
                      _1341_recErased = _out839;
                      _1342_recIdents = _out840;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1339_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1340_recOwned;
                      isErased = _1341_recErased;
                      readIdents = _1342_recIdents;
                    }
                  } else {
                    DAST._IType _1343___mcc_h596 = _source53.dtor_Newtype_a0;
                    DAST._IType _1344_b = _1343___mcc_h596;
                    {
                      if (object.Equals(_461_fromTpe, _1344_b)) {
                        Dafny.ISequence<Dafny.Rune> _1345_recursiveGen;
                        bool _1346_recOwned;
                        bool _1347_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1348_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out841;
                        bool _out842;
                        bool _out843;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out844;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out841, out _out842, out _out843, out _out844);
                        _1345_recursiveGen = _out841;
                        _1346_recOwned = _out842;
                        _1347_recErased = _out843;
                        _1348_recIdents = _out844;
                        Dafny.ISequence<Dafny.Rune> _1349_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out845;
                        _out845 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _1349_rhsType = _out845;
                        Dafny.ISequence<Dafny.Rune> _1350_uneraseFn;
                        _1350_uneraseFn = ((_1346_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1349_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1350_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1345_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1346_recOwned;
                        isErased = false;
                        readIdents = _1348_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out846;
                        bool _out847;
                        bool _out848;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out849;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1344_b), _1344_b, _460_toTpe), @params, mustOwn, out _out846, out _out847, out _out848, out _out849);
                        s = _out846;
                        isOwned = _out847;
                        isErased = _out848;
                        readIdents = _out849;
                      }
                    }
                  }
                } else if (_source52.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1351___mcc_h598 = _source52.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1352_recursiveGen;
                    bool _1353_recOwned;
                    bool _1354_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1355_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out850;
                    bool _out851;
                    bool _out852;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out853;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out850, out _out851, out _out852, out _out853);
                    _1352_recursiveGen = _out850;
                    _1353_recOwned = _out851;
                    _1354_recErased = _out852;
                    _1355_recIdents = _out853;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1352_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1353_recOwned;
                    isErased = _1354_recErased;
                    readIdents = _1355_recIdents;
                  }
                } else if (_source52.is_Array) {
                  DAST._IType _1356___mcc_h600 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1357_recursiveGen;
                    bool _1358_recOwned;
                    bool _1359_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1360_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out854;
                    bool _out855;
                    bool _out856;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out857;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out854, out _out855, out _out856, out _out857);
                    _1357_recursiveGen = _out854;
                    _1358_recOwned = _out855;
                    _1359_recErased = _out856;
                    _1360_recIdents = _out857;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1357_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1358_recOwned;
                    isErased = _1359_recErased;
                    readIdents = _1360_recIdents;
                  }
                } else if (_source52.is_Seq) {
                  DAST._IType _1361___mcc_h602 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1362_recursiveGen;
                    bool _1363_recOwned;
                    bool _1364_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1365_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out858;
                    bool _out859;
                    bool _out860;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out861;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out858, out _out859, out _out860, out _out861);
                    _1362_recursiveGen = _out858;
                    _1363_recOwned = _out859;
                    _1364_recErased = _out860;
                    _1365_recIdents = _out861;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1362_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1363_recOwned;
                    isErased = _1364_recErased;
                    readIdents = _1365_recIdents;
                  }
                } else if (_source52.is_Set) {
                  DAST._IType _1366___mcc_h604 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1367_recursiveGen;
                    bool _1368_recOwned;
                    bool _1369_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1370_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out862;
                    bool _out863;
                    bool _out864;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out865;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out862, out _out863, out _out864, out _out865);
                    _1367_recursiveGen = _out862;
                    _1368_recOwned = _out863;
                    _1369_recErased = _out864;
                    _1370_recIdents = _out865;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1367_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1368_recOwned;
                    isErased = _1369_recErased;
                    readIdents = _1370_recIdents;
                  }
                } else if (_source52.is_Multiset) {
                  DAST._IType _1371___mcc_h606 = _source52.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1372_recursiveGen;
                    bool _1373_recOwned;
                    bool _1374_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1375_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out866;
                    bool _out867;
                    bool _out868;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out869;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out866, out _out867, out _out868, out _out869);
                    _1372_recursiveGen = _out866;
                    _1373_recOwned = _out867;
                    _1374_recErased = _out868;
                    _1375_recIdents = _out869;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1372_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1373_recOwned;
                    isErased = _1374_recErased;
                    readIdents = _1375_recIdents;
                  }
                } else if (_source52.is_Map) {
                  DAST._IType _1376___mcc_h608 = _source52.dtor_key;
                  DAST._IType _1377___mcc_h609 = _source52.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1378_recursiveGen;
                    bool _1379_recOwned;
                    bool _1380_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1381_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out870;
                    bool _out871;
                    bool _out872;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out873;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out870, out _out871, out _out872, out _out873);
                    _1378_recursiveGen = _out870;
                    _1379_recOwned = _out871;
                    _1380_recErased = _out872;
                    _1381_recIdents = _out873;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1378_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1379_recOwned;
                    isErased = _1380_recErased;
                    readIdents = _1381_recIdents;
                  }
                } else if (_source52.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1382___mcc_h612 = _source52.dtor_args;
                  DAST._IType _1383___mcc_h613 = _source52.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1384_recursiveGen;
                    bool _1385_recOwned;
                    bool _1386_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1387_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out874;
                    bool _out875;
                    bool _out876;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out877;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out874, out _out875, out _out876, out _out877);
                    _1384_recursiveGen = _out874;
                    _1385_recOwned = _out875;
                    _1386_recErased = _out876;
                    _1387_recIdents = _out877;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1384_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1385_recOwned;
                    isErased = _1386_recErased;
                    readIdents = _1387_recIdents;
                  }
                } else if (_source52.is_Primitive) {
                  DAST._IPrimitive _1388___mcc_h616 = _source52.dtor_Primitive_a0;
                  DAST._IPrimitive _source54 = _1388___mcc_h616;
                  if (_source54.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1389_recursiveGen;
                      bool _1390___v41;
                      bool _1391___v42;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1392_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out878;
                      bool _out879;
                      bool _out880;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out881;
                      DCOMP.COMP.GenExpr(_462_expr, @params, false, out _out878, out _out879, out _out880, out _out881);
                      _1389_recursiveGen = _out878;
                      _1390___v41 = _out879;
                      _1391___v42 = _out880;
                      _1392_recIdents = _out881;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1389_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1392_recIdents;
                    }
                  } else if (_source54.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1393_recursiveGen;
                      bool _1394_recOwned;
                      bool _1395_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1396_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out882;
                      bool _out883;
                      bool _out884;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out885;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out882, out _out883, out _out884, out _out885);
                      _1393_recursiveGen = _out882;
                      _1394_recOwned = _out883;
                      _1395_recErased = _out884;
                      _1396_recIdents = _out885;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1393_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1394_recOwned;
                      isErased = _1395_recErased;
                      readIdents = _1396_recIdents;
                    }
                  } else if (_source54.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1397_recursiveGen;
                      bool _1398_recOwned;
                      bool _1399_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1400_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out886;
                      bool _out887;
                      bool _out888;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out889;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out886, out _out887, out _out888, out _out889);
                      _1397_recursiveGen = _out886;
                      _1398_recOwned = _out887;
                      _1399_recErased = _out888;
                      _1400_recIdents = _out889;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1397_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1398_recOwned;
                      isErased = _1399_recErased;
                      readIdents = _1400_recIdents;
                    }
                  } else if (_source54.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1401_recursiveGen;
                      bool _1402_recOwned;
                      bool _1403_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1404_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out890;
                      bool _out891;
                      bool _out892;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out893;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out890, out _out891, out _out892, out _out893);
                      _1401_recursiveGen = _out890;
                      _1402_recOwned = _out891;
                      _1403_recErased = _out892;
                      _1404_recIdents = _out893;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1401_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1402_recOwned;
                      isErased = _1403_recErased;
                      readIdents = _1404_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1405_recursiveGen;
                      bool _1406_recOwned;
                      bool _1407_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1408_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out894;
                      bool _out895;
                      bool _out896;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out897;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out894, out _out895, out _out896, out _out897);
                      _1405_recursiveGen = _out894;
                      _1406_recOwned = _out895;
                      _1407_recErased = _out896;
                      _1408_recIdents = _out897;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1405_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1406_recOwned;
                      isErased = _1407_recErased;
                      readIdents = _1408_recIdents;
                    }
                  }
                } else if (_source52.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1409___mcc_h618 = _source52.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1410_recursiveGen;
                    bool _1411_recOwned;
                    bool _1412_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1413_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out898;
                    bool _out899;
                    bool _out900;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out901;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out898, out _out899, out _out900, out _out901);
                    _1410_recursiveGen = _out898;
                    _1411_recOwned = _out899;
                    _1412_recErased = _out900;
                    _1413_recIdents = _out901;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1410_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1411_recOwned;
                    isErased = _1412_recErased;
                    readIdents = _1413_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1414___mcc_h620 = _source52.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1415_recursiveGen;
                    bool _1416_recOwned;
                    bool _1417_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1418_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out902;
                    bool _out903;
                    bool _out904;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out905;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out902, out _out903, out _out904, out _out905);
                    _1415_recursiveGen = _out902;
                    _1416_recOwned = _out903;
                    _1417_recErased = _out904;
                    _1418_recIdents = _out905;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1415_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1416_recOwned;
                    isErased = _1417_recErased;
                    readIdents = _1418_recIdents;
                  }
                }
              } else if (_source48.is_String) {
                DAST._IType _source55 = _468___mcc_h121;
                if (_source55.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1419___mcc_h622 = _source55.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1420___mcc_h623 = _source55.dtor_typeArgs;
                  DAST._IResolvedType _1421___mcc_h624 = _source55.dtor_resolved;
                  DAST._IResolvedType _source56 = _1421___mcc_h624;
                  if (_source56.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1422___mcc_h628 = _source56.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1423_recursiveGen;
                      bool _1424_recOwned;
                      bool _1425_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1426_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out906;
                      bool _out907;
                      bool _out908;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out909;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out906, out _out907, out _out908, out _out909);
                      _1423_recursiveGen = _out906;
                      _1424_recOwned = _out907;
                      _1425_recErased = _out908;
                      _1426_recIdents = _out909;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1423_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1424_recOwned;
                      isErased = _1425_recErased;
                      readIdents = _1426_recIdents;
                    }
                  } else if (_source56.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1427___mcc_h630 = _source56.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1428_recursiveGen;
                      bool _1429_recOwned;
                      bool _1430_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1431_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out910;
                      bool _out911;
                      bool _out912;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out913;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out910, out _out911, out _out912, out _out913);
                      _1428_recursiveGen = _out910;
                      _1429_recOwned = _out911;
                      _1430_recErased = _out912;
                      _1431_recIdents = _out913;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1428_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1429_recOwned;
                      isErased = _1430_recErased;
                      readIdents = _1431_recIdents;
                    }
                  } else {
                    DAST._IType _1432___mcc_h632 = _source56.dtor_Newtype_a0;
                    DAST._IType _1433_b = _1432___mcc_h632;
                    {
                      if (object.Equals(_461_fromTpe, _1433_b)) {
                        Dafny.ISequence<Dafny.Rune> _1434_recursiveGen;
                        bool _1435_recOwned;
                        bool _1436_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1437_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out914;
                        bool _out915;
                        bool _out916;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out917;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out914, out _out915, out _out916, out _out917);
                        _1434_recursiveGen = _out914;
                        _1435_recOwned = _out915;
                        _1436_recErased = _out916;
                        _1437_recIdents = _out917;
                        Dafny.ISequence<Dafny.Rune> _1438_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out918;
                        _out918 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _1438_rhsType = _out918;
                        Dafny.ISequence<Dafny.Rune> _1439_uneraseFn;
                        _1439_uneraseFn = ((_1435_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1438_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1439_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1434_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1435_recOwned;
                        isErased = false;
                        readIdents = _1437_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out919;
                        bool _out920;
                        bool _out921;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out922;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1433_b), _1433_b, _460_toTpe), @params, mustOwn, out _out919, out _out920, out _out921, out _out922);
                        s = _out919;
                        isOwned = _out920;
                        isErased = _out921;
                        readIdents = _out922;
                      }
                    }
                  }
                } else if (_source55.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1440___mcc_h634 = _source55.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1441_recursiveGen;
                    bool _1442_recOwned;
                    bool _1443_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1444_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out923;
                    bool _out924;
                    bool _out925;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out926;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out923, out _out924, out _out925, out _out926);
                    _1441_recursiveGen = _out923;
                    _1442_recOwned = _out924;
                    _1443_recErased = _out925;
                    _1444_recIdents = _out926;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1441_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1442_recOwned;
                    isErased = _1443_recErased;
                    readIdents = _1444_recIdents;
                  }
                } else if (_source55.is_Array) {
                  DAST._IType _1445___mcc_h636 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1446_recursiveGen;
                    bool _1447_recOwned;
                    bool _1448_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1449_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out927;
                    bool _out928;
                    bool _out929;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out930;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out927, out _out928, out _out929, out _out930);
                    _1446_recursiveGen = _out927;
                    _1447_recOwned = _out928;
                    _1448_recErased = _out929;
                    _1449_recIdents = _out930;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1446_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1447_recOwned;
                    isErased = _1448_recErased;
                    readIdents = _1449_recIdents;
                  }
                } else if (_source55.is_Seq) {
                  DAST._IType _1450___mcc_h638 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1451_recursiveGen;
                    bool _1452_recOwned;
                    bool _1453_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1454_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out931;
                    bool _out932;
                    bool _out933;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out934;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out931, out _out932, out _out933, out _out934);
                    _1451_recursiveGen = _out931;
                    _1452_recOwned = _out932;
                    _1453_recErased = _out933;
                    _1454_recIdents = _out934;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1451_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1452_recOwned;
                    isErased = _1453_recErased;
                    readIdents = _1454_recIdents;
                  }
                } else if (_source55.is_Set) {
                  DAST._IType _1455___mcc_h640 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1456_recursiveGen;
                    bool _1457_recOwned;
                    bool _1458_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1459_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out935;
                    bool _out936;
                    bool _out937;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out938;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out935, out _out936, out _out937, out _out938);
                    _1456_recursiveGen = _out935;
                    _1457_recOwned = _out936;
                    _1458_recErased = _out937;
                    _1459_recIdents = _out938;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1456_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1457_recOwned;
                    isErased = _1458_recErased;
                    readIdents = _1459_recIdents;
                  }
                } else if (_source55.is_Multiset) {
                  DAST._IType _1460___mcc_h642 = _source55.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1461_recursiveGen;
                    bool _1462_recOwned;
                    bool _1463_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1464_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out939;
                    bool _out940;
                    bool _out941;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out942;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out939, out _out940, out _out941, out _out942);
                    _1461_recursiveGen = _out939;
                    _1462_recOwned = _out940;
                    _1463_recErased = _out941;
                    _1464_recIdents = _out942;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1461_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1462_recOwned;
                    isErased = _1463_recErased;
                    readIdents = _1464_recIdents;
                  }
                } else if (_source55.is_Map) {
                  DAST._IType _1465___mcc_h644 = _source55.dtor_key;
                  DAST._IType _1466___mcc_h645 = _source55.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1467_recursiveGen;
                    bool _1468_recOwned;
                    bool _1469_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1470_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out943;
                    bool _out944;
                    bool _out945;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out946;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out943, out _out944, out _out945, out _out946);
                    _1467_recursiveGen = _out943;
                    _1468_recOwned = _out944;
                    _1469_recErased = _out945;
                    _1470_recIdents = _out946;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1467_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1468_recOwned;
                    isErased = _1469_recErased;
                    readIdents = _1470_recIdents;
                  }
                } else if (_source55.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1471___mcc_h648 = _source55.dtor_args;
                  DAST._IType _1472___mcc_h649 = _source55.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1473_recursiveGen;
                    bool _1474_recOwned;
                    bool _1475_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1476_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out947;
                    bool _out948;
                    bool _out949;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out950;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out947, out _out948, out _out949, out _out950);
                    _1473_recursiveGen = _out947;
                    _1474_recOwned = _out948;
                    _1475_recErased = _out949;
                    _1476_recIdents = _out950;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1473_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1474_recOwned;
                    isErased = _1475_recErased;
                    readIdents = _1476_recIdents;
                  }
                } else if (_source55.is_Primitive) {
                  DAST._IPrimitive _1477___mcc_h652 = _source55.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1478_recursiveGen;
                    bool _1479_recOwned;
                    bool _1480_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1481_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out951;
                    bool _out952;
                    bool _out953;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out954;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out951, out _out952, out _out953, out _out954);
                    _1478_recursiveGen = _out951;
                    _1479_recOwned = _out952;
                    _1480_recErased = _out953;
                    _1481_recIdents = _out954;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1478_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1479_recOwned;
                    isErased = _1480_recErased;
                    readIdents = _1481_recIdents;
                  }
                } else if (_source55.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1482___mcc_h654 = _source55.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1483_recursiveGen;
                    bool _1484_recOwned;
                    bool _1485_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1486_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out955;
                    bool _out956;
                    bool _out957;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out958;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out955, out _out956, out _out957, out _out958);
                    _1483_recursiveGen = _out955;
                    _1484_recOwned = _out956;
                    _1485_recErased = _out957;
                    _1486_recIdents = _out958;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1483_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1484_recOwned;
                    isErased = _1485_recErased;
                    readIdents = _1486_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1487___mcc_h656 = _source55.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1488_recursiveGen;
                    bool _1489_recOwned;
                    bool _1490_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1491_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out959;
                    bool _out960;
                    bool _out961;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out962;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out959, out _out960, out _out961, out _out962);
                    _1488_recursiveGen = _out959;
                    _1489_recOwned = _out960;
                    _1490_recErased = _out961;
                    _1491_recIdents = _out962;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1488_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1489_recOwned;
                    isErased = _1490_recErased;
                    readIdents = _1491_recIdents;
                  }
                }
              } else if (_source48.is_Bool) {
                DAST._IType _source57 = _468___mcc_h121;
                if (_source57.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1492___mcc_h658 = _source57.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1493___mcc_h659 = _source57.dtor_typeArgs;
                  DAST._IResolvedType _1494___mcc_h660 = _source57.dtor_resolved;
                  DAST._IResolvedType _source58 = _1494___mcc_h660;
                  if (_source58.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1495___mcc_h664 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1496_recursiveGen;
                      bool _1497_recOwned;
                      bool _1498_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1499_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out963;
                      bool _out964;
                      bool _out965;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out963, out _out964, out _out965, out _out966);
                      _1496_recursiveGen = _out963;
                      _1497_recOwned = _out964;
                      _1498_recErased = _out965;
                      _1499_recIdents = _out966;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1496_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1497_recOwned;
                      isErased = _1498_recErased;
                      readIdents = _1499_recIdents;
                    }
                  } else if (_source58.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1500___mcc_h666 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1501_recursiveGen;
                      bool _1502_recOwned;
                      bool _1503_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1504_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out967;
                      bool _out968;
                      bool _out969;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out970;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out967, out _out968, out _out969, out _out970);
                      _1501_recursiveGen = _out967;
                      _1502_recOwned = _out968;
                      _1503_recErased = _out969;
                      _1504_recIdents = _out970;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1501_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1502_recOwned;
                      isErased = _1503_recErased;
                      readIdents = _1504_recIdents;
                    }
                  } else {
                    DAST._IType _1505___mcc_h668 = _source58.dtor_Newtype_a0;
                    DAST._IType _1506_b = _1505___mcc_h668;
                    {
                      if (object.Equals(_461_fromTpe, _1506_b)) {
                        Dafny.ISequence<Dafny.Rune> _1507_recursiveGen;
                        bool _1508_recOwned;
                        bool _1509_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out971;
                        bool _out972;
                        bool _out973;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out971, out _out972, out _out973, out _out974);
                        _1507_recursiveGen = _out971;
                        _1508_recOwned = _out972;
                        _1509_recErased = _out973;
                        _1510_recIdents = _out974;
                        Dafny.ISequence<Dafny.Rune> _1511_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out975;
                        _out975 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _1511_rhsType = _out975;
                        Dafny.ISequence<Dafny.Rune> _1512_uneraseFn;
                        _1512_uneraseFn = ((_1508_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1511_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1512_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1507_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1508_recOwned;
                        isErased = false;
                        readIdents = _1510_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out976;
                        bool _out977;
                        bool _out978;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out979;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1506_b), _1506_b, _460_toTpe), @params, mustOwn, out _out976, out _out977, out _out978, out _out979);
                        s = _out976;
                        isOwned = _out977;
                        isErased = _out978;
                        readIdents = _out979;
                      }
                    }
                  }
                } else if (_source57.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1513___mcc_h670 = _source57.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1514_recursiveGen;
                    bool _1515_recOwned;
                    bool _1516_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1517_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out980;
                    bool _out981;
                    bool _out982;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out983;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out980, out _out981, out _out982, out _out983);
                    _1514_recursiveGen = _out980;
                    _1515_recOwned = _out981;
                    _1516_recErased = _out982;
                    _1517_recIdents = _out983;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1514_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1515_recOwned;
                    isErased = _1516_recErased;
                    readIdents = _1517_recIdents;
                  }
                } else if (_source57.is_Array) {
                  DAST._IType _1518___mcc_h672 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1519_recursiveGen;
                    bool _1520_recOwned;
                    bool _1521_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out984;
                    bool _out985;
                    bool _out986;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out987;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out984, out _out985, out _out986, out _out987);
                    _1519_recursiveGen = _out984;
                    _1520_recOwned = _out985;
                    _1521_recErased = _out986;
                    _1522_recIdents = _out987;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1519_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1520_recOwned;
                    isErased = _1521_recErased;
                    readIdents = _1522_recIdents;
                  }
                } else if (_source57.is_Seq) {
                  DAST._IType _1523___mcc_h674 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1524_recursiveGen;
                    bool _1525_recOwned;
                    bool _1526_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1527_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out988;
                    bool _out989;
                    bool _out990;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out991;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out988, out _out989, out _out990, out _out991);
                    _1524_recursiveGen = _out988;
                    _1525_recOwned = _out989;
                    _1526_recErased = _out990;
                    _1527_recIdents = _out991;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1524_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1525_recOwned;
                    isErased = _1526_recErased;
                    readIdents = _1527_recIdents;
                  }
                } else if (_source57.is_Set) {
                  DAST._IType _1528___mcc_h676 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1529_recursiveGen;
                    bool _1530_recOwned;
                    bool _1531_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1532_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out992;
                    bool _out993;
                    bool _out994;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out995;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out992, out _out993, out _out994, out _out995);
                    _1529_recursiveGen = _out992;
                    _1530_recOwned = _out993;
                    _1531_recErased = _out994;
                    _1532_recIdents = _out995;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1529_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1530_recOwned;
                    isErased = _1531_recErased;
                    readIdents = _1532_recIdents;
                  }
                } else if (_source57.is_Multiset) {
                  DAST._IType _1533___mcc_h678 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1534_recursiveGen;
                    bool _1535_recOwned;
                    bool _1536_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1537_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out996;
                    bool _out997;
                    bool _out998;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out999;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out996, out _out997, out _out998, out _out999);
                    _1534_recursiveGen = _out996;
                    _1535_recOwned = _out997;
                    _1536_recErased = _out998;
                    _1537_recIdents = _out999;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1534_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1535_recOwned;
                    isErased = _1536_recErased;
                    readIdents = _1537_recIdents;
                  }
                } else if (_source57.is_Map) {
                  DAST._IType _1538___mcc_h680 = _source57.dtor_key;
                  DAST._IType _1539___mcc_h681 = _source57.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1540_recursiveGen;
                    bool _1541_recOwned;
                    bool _1542_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1543_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1000;
                    bool _out1001;
                    bool _out1002;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1003;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1000, out _out1001, out _out1002, out _out1003);
                    _1540_recursiveGen = _out1000;
                    _1541_recOwned = _out1001;
                    _1542_recErased = _out1002;
                    _1543_recIdents = _out1003;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1540_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1541_recOwned;
                    isErased = _1542_recErased;
                    readIdents = _1543_recIdents;
                  }
                } else if (_source57.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1544___mcc_h684 = _source57.dtor_args;
                  DAST._IType _1545___mcc_h685 = _source57.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1546_recursiveGen;
                    bool _1547_recOwned;
                    bool _1548_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1549_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1004;
                    bool _out1005;
                    bool _out1006;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1007;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1004, out _out1005, out _out1006, out _out1007);
                    _1546_recursiveGen = _out1004;
                    _1547_recOwned = _out1005;
                    _1548_recErased = _out1006;
                    _1549_recIdents = _out1007;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1546_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1547_recOwned;
                    isErased = _1548_recErased;
                    readIdents = _1549_recIdents;
                  }
                } else if (_source57.is_Primitive) {
                  DAST._IPrimitive _1550___mcc_h688 = _source57.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1551_recursiveGen;
                    bool _1552_recOwned;
                    bool _1553_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1008;
                    bool _out1009;
                    bool _out1010;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1011;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1008, out _out1009, out _out1010, out _out1011);
                    _1551_recursiveGen = _out1008;
                    _1552_recOwned = _out1009;
                    _1553_recErased = _out1010;
                    _1554_recIdents = _out1011;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1551_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1552_recOwned;
                    isErased = _1553_recErased;
                    readIdents = _1554_recIdents;
                  }
                } else if (_source57.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1555___mcc_h690 = _source57.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1556_recursiveGen;
                    bool _1557_recOwned;
                    bool _1558_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1012;
                    bool _out1013;
                    bool _out1014;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1015;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1012, out _out1013, out _out1014, out _out1015);
                    _1556_recursiveGen = _out1012;
                    _1557_recOwned = _out1013;
                    _1558_recErased = _out1014;
                    _1559_recIdents = _out1015;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1556_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1557_recOwned;
                    isErased = _1558_recErased;
                    readIdents = _1559_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1560___mcc_h692 = _source57.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1561_recursiveGen;
                    bool _1562_recOwned;
                    bool _1563_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1564_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1016;
                    bool _out1017;
                    bool _out1018;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1019;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1016, out _out1017, out _out1018, out _out1019);
                    _1561_recursiveGen = _out1016;
                    _1562_recOwned = _out1017;
                    _1563_recErased = _out1018;
                    _1564_recIdents = _out1019;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1561_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1562_recOwned;
                    isErased = _1563_recErased;
                    readIdents = _1564_recIdents;
                  }
                }
              } else {
                DAST._IType _source59 = _468___mcc_h121;
                if (_source59.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1565___mcc_h694 = _source59.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1566___mcc_h695 = _source59.dtor_typeArgs;
                  DAST._IResolvedType _1567___mcc_h696 = _source59.dtor_resolved;
                  DAST._IResolvedType _source60 = _1567___mcc_h696;
                  if (_source60.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1568___mcc_h700 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1569_recursiveGen;
                      bool _1570_recOwned;
                      bool _1571_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1572_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1020;
                      bool _out1021;
                      bool _out1022;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1023;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1020, out _out1021, out _out1022, out _out1023);
                      _1569_recursiveGen = _out1020;
                      _1570_recOwned = _out1021;
                      _1571_recErased = _out1022;
                      _1572_recIdents = _out1023;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1569_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1570_recOwned;
                      isErased = _1571_recErased;
                      readIdents = _1572_recIdents;
                    }
                  } else if (_source60.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1573___mcc_h702 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1574_recursiveGen;
                      bool _1575_recOwned;
                      bool _1576_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1577_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1024;
                      bool _out1025;
                      bool _out1026;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1027;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1024, out _out1025, out _out1026, out _out1027);
                      _1574_recursiveGen = _out1024;
                      _1575_recOwned = _out1025;
                      _1576_recErased = _out1026;
                      _1577_recIdents = _out1027;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1575_recOwned;
                      isErased = _1576_recErased;
                      readIdents = _1577_recIdents;
                    }
                  } else {
                    DAST._IType _1578___mcc_h704 = _source60.dtor_Newtype_a0;
                    DAST._IType _1579_b = _1578___mcc_h704;
                    {
                      if (object.Equals(_461_fromTpe, _1579_b)) {
                        Dafny.ISequence<Dafny.Rune> _1580_recursiveGen;
                        bool _1581_recOwned;
                        bool _1582_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1583_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1028;
                        bool _out1029;
                        bool _out1030;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1031;
                        DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1028, out _out1029, out _out1030, out _out1031);
                        _1580_recursiveGen = _out1028;
                        _1581_recOwned = _out1029;
                        _1582_recErased = _out1030;
                        _1583_recIdents = _out1031;
                        Dafny.ISequence<Dafny.Rune> _1584_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1032;
                        _out1032 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                        _1584_rhsType = _out1032;
                        Dafny.ISequence<Dafny.Rune> _1585_uneraseFn;
                        _1585_uneraseFn = ((_1581_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1584_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1585_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1580_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1581_recOwned;
                        isErased = false;
                        readIdents = _1583_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1033;
                        bool _out1034;
                        bool _out1035;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1036;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1579_b), _1579_b, _460_toTpe), @params, mustOwn, out _out1033, out _out1034, out _out1035, out _out1036);
                        s = _out1033;
                        isOwned = _out1034;
                        isErased = _out1035;
                        readIdents = _out1036;
                      }
                    }
                  }
                } else if (_source59.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1586___mcc_h706 = _source59.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1587_recursiveGen;
                    bool _1588_recOwned;
                    bool _1589_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1037;
                    bool _out1038;
                    bool _out1039;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1040;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1037, out _out1038, out _out1039, out _out1040);
                    _1587_recursiveGen = _out1037;
                    _1588_recOwned = _out1038;
                    _1589_recErased = _out1039;
                    _1590_recIdents = _out1040;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1587_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1588_recOwned;
                    isErased = _1589_recErased;
                    readIdents = _1590_recIdents;
                  }
                } else if (_source59.is_Array) {
                  DAST._IType _1591___mcc_h708 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1592_recursiveGen;
                    bool _1593_recOwned;
                    bool _1594_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1595_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1041;
                    bool _out1042;
                    bool _out1043;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1044;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1041, out _out1042, out _out1043, out _out1044);
                    _1592_recursiveGen = _out1041;
                    _1593_recOwned = _out1042;
                    _1594_recErased = _out1043;
                    _1595_recIdents = _out1044;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1592_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1593_recOwned;
                    isErased = _1594_recErased;
                    readIdents = _1595_recIdents;
                  }
                } else if (_source59.is_Seq) {
                  DAST._IType _1596___mcc_h710 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1597_recursiveGen;
                    bool _1598_recOwned;
                    bool _1599_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1600_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1045;
                    bool _out1046;
                    bool _out1047;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1048;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1045, out _out1046, out _out1047, out _out1048);
                    _1597_recursiveGen = _out1045;
                    _1598_recOwned = _out1046;
                    _1599_recErased = _out1047;
                    _1600_recIdents = _out1048;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1597_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1598_recOwned;
                    isErased = _1599_recErased;
                    readIdents = _1600_recIdents;
                  }
                } else if (_source59.is_Set) {
                  DAST._IType _1601___mcc_h712 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1602_recursiveGen;
                    bool _1603_recOwned;
                    bool _1604_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1605_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1049;
                    bool _out1050;
                    bool _out1051;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1052;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1049, out _out1050, out _out1051, out _out1052);
                    _1602_recursiveGen = _out1049;
                    _1603_recOwned = _out1050;
                    _1604_recErased = _out1051;
                    _1605_recIdents = _out1052;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1602_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1603_recOwned;
                    isErased = _1604_recErased;
                    readIdents = _1605_recIdents;
                  }
                } else if (_source59.is_Multiset) {
                  DAST._IType _1606___mcc_h714 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1607_recursiveGen;
                    bool _1608_recOwned;
                    bool _1609_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1610_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1053;
                    bool _out1054;
                    bool _out1055;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1056;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1053, out _out1054, out _out1055, out _out1056);
                    _1607_recursiveGen = _out1053;
                    _1608_recOwned = _out1054;
                    _1609_recErased = _out1055;
                    _1610_recIdents = _out1056;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1607_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1608_recOwned;
                    isErased = _1609_recErased;
                    readIdents = _1610_recIdents;
                  }
                } else if (_source59.is_Map) {
                  DAST._IType _1611___mcc_h716 = _source59.dtor_key;
                  DAST._IType _1612___mcc_h717 = _source59.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1613_recursiveGen;
                    bool _1614_recOwned;
                    bool _1615_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1616_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1057;
                    bool _out1058;
                    bool _out1059;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1060;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1057, out _out1058, out _out1059, out _out1060);
                    _1613_recursiveGen = _out1057;
                    _1614_recOwned = _out1058;
                    _1615_recErased = _out1059;
                    _1616_recIdents = _out1060;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1613_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1614_recOwned;
                    isErased = _1615_recErased;
                    readIdents = _1616_recIdents;
                  }
                } else if (_source59.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1617___mcc_h720 = _source59.dtor_args;
                  DAST._IType _1618___mcc_h721 = _source59.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1619_recursiveGen;
                    bool _1620_recOwned;
                    bool _1621_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1622_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1061;
                    bool _out1062;
                    bool _out1063;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1064;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1061, out _out1062, out _out1063, out _out1064);
                    _1619_recursiveGen = _out1061;
                    _1620_recOwned = _out1062;
                    _1621_recErased = _out1063;
                    _1622_recIdents = _out1064;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1619_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1620_recOwned;
                    isErased = _1621_recErased;
                    readIdents = _1622_recIdents;
                  }
                } else if (_source59.is_Primitive) {
                  DAST._IPrimitive _1623___mcc_h724 = _source59.dtor_Primitive_a0;
                  DAST._IPrimitive _source61 = _1623___mcc_h724;
                  if (_source61.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1624_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1065;
                      _out1065 = DCOMP.COMP.GenType(_461_fromTpe, true, false);
                      _1624_rhsType = _out1065;
                      Dafny.ISequence<Dafny.Rune> _1625_recursiveGen;
                      bool _1626___v51;
                      bool _1627___v52;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1066;
                      bool _out1067;
                      bool _out1068;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1069;
                      DCOMP.COMP.GenExpr(_462_expr, @params, true, out _out1066, out _out1067, out _out1068, out _out1069);
                      _1625_recursiveGen = _out1066;
                      _1626___v51 = _out1067;
                      _1627___v52 = _out1068;
                      _1628_recIdents = _out1069;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1625_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1628_recIdents;
                    }
                  } else if (_source61.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1629_recursiveGen;
                      bool _1630_recOwned;
                      bool _1631_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1632_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1070;
                      bool _out1071;
                      bool _out1072;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1073;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1070, out _out1071, out _out1072, out _out1073);
                      _1629_recursiveGen = _out1070;
                      _1630_recOwned = _out1071;
                      _1631_recErased = _out1072;
                      _1632_recIdents = _out1073;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1629_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1630_recOwned;
                      isErased = _1631_recErased;
                      readIdents = _1632_recIdents;
                    }
                  } else if (_source61.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1633_recursiveGen;
                      bool _1634_recOwned;
                      bool _1635_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1636_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1074;
                      bool _out1075;
                      bool _out1076;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1077;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1074, out _out1075, out _out1076, out _out1077);
                      _1633_recursiveGen = _out1074;
                      _1634_recOwned = _out1075;
                      _1635_recErased = _out1076;
                      _1636_recIdents = _out1077;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1633_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1634_recOwned;
                      isErased = _1635_recErased;
                      readIdents = _1636_recIdents;
                    }
                  } else if (_source61.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1637_recursiveGen;
                      bool _1638_recOwned;
                      bool _1639_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1640_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1078;
                      bool _out1079;
                      bool _out1080;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1081;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1078, out _out1079, out _out1080, out _out1081);
                      _1637_recursiveGen = _out1078;
                      _1638_recOwned = _out1079;
                      _1639_recErased = _out1080;
                      _1640_recIdents = _out1081;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1637_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1638_recOwned;
                      isErased = _1639_recErased;
                      readIdents = _1640_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1641_recursiveGen;
                      bool _1642_recOwned;
                      bool _1643_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1644_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1082;
                      bool _out1083;
                      bool _out1084;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1085;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1082, out _out1083, out _out1084, out _out1085);
                      _1641_recursiveGen = _out1082;
                      _1642_recOwned = _out1083;
                      _1643_recErased = _out1084;
                      _1644_recIdents = _out1085;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1641_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1642_recOwned;
                      isErased = _1643_recErased;
                      readIdents = _1644_recIdents;
                    }
                  }
                } else if (_source59.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1645___mcc_h726 = _source59.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1646_recursiveGen;
                    bool _1647_recOwned;
                    bool _1648_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1649_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1086;
                    bool _out1087;
                    bool _out1088;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1089;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1086, out _out1087, out _out1088, out _out1089);
                    _1646_recursiveGen = _out1086;
                    _1647_recOwned = _out1087;
                    _1648_recErased = _out1088;
                    _1649_recIdents = _out1089;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1646_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1647_recOwned;
                    isErased = _1648_recErased;
                    readIdents = _1649_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1650___mcc_h728 = _source59.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1651_recursiveGen;
                    bool _1652_recOwned;
                    bool _1653_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1654_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1090;
                    bool _out1091;
                    bool _out1092;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1093;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1090, out _out1091, out _out1092, out _out1093);
                    _1651_recursiveGen = _out1090;
                    _1652_recOwned = _out1091;
                    _1653_recErased = _out1092;
                    _1654_recIdents = _out1093;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1651_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1652_recOwned;
                    isErased = _1653_recErased;
                    readIdents = _1654_recIdents;
                  }
                }
              }
            } else if (_source26.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1655___mcc_h730 = _source26.dtor_Passthrough_a0;
              DAST._IType _source62 = _468___mcc_h121;
              if (_source62.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1656___mcc_h733 = _source62.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1657___mcc_h734 = _source62.dtor_typeArgs;
                DAST._IResolvedType _1658___mcc_h735 = _source62.dtor_resolved;
                DAST._IResolvedType _source63 = _1658___mcc_h735;
                if (_source63.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1659___mcc_h739 = _source63.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1660_recursiveGen;
                    bool _1661_recOwned;
                    bool _1662_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1663_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1094;
                    bool _out1095;
                    bool _out1096;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1097;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1094, out _out1095, out _out1096, out _out1097);
                    _1660_recursiveGen = _out1094;
                    _1661_recOwned = _out1095;
                    _1662_recErased = _out1096;
                    _1663_recIdents = _out1097;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1660_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1661_recOwned;
                    isErased = _1662_recErased;
                    readIdents = _1663_recIdents;
                  }
                } else if (_source63.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1664___mcc_h741 = _source63.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1665_recursiveGen;
                    bool _1666_recOwned;
                    bool _1667_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1668_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1098;
                    bool _out1099;
                    bool _out1100;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1101;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1098, out _out1099, out _out1100, out _out1101);
                    _1665_recursiveGen = _out1098;
                    _1666_recOwned = _out1099;
                    _1667_recErased = _out1100;
                    _1668_recIdents = _out1101;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1665_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1666_recOwned;
                    isErased = _1667_recErased;
                    readIdents = _1668_recIdents;
                  }
                } else {
                  DAST._IType _1669___mcc_h743 = _source63.dtor_Newtype_a0;
                  DAST._IType _1670_b = _1669___mcc_h743;
                  {
                    if (object.Equals(_461_fromTpe, _1670_b)) {
                      Dafny.ISequence<Dafny.Rune> _1671_recursiveGen;
                      bool _1672_recOwned;
                      bool _1673_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1674_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1102;
                      bool _out1103;
                      bool _out1104;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1105;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1102, out _out1103, out _out1104, out _out1105);
                      _1671_recursiveGen = _out1102;
                      _1672_recOwned = _out1103;
                      _1673_recErased = _out1104;
                      _1674_recIdents = _out1105;
                      Dafny.ISequence<Dafny.Rune> _1675_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1106;
                      _out1106 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _1675_rhsType = _out1106;
                      Dafny.ISequence<Dafny.Rune> _1676_uneraseFn;
                      _1676_uneraseFn = ((_1672_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1675_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1676_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1671_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1672_recOwned;
                      isErased = false;
                      readIdents = _1674_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1107;
                      bool _out1108;
                      bool _out1109;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1110;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1670_b), _1670_b, _460_toTpe), @params, mustOwn, out _out1107, out _out1108, out _out1109, out _out1110);
                      s = _out1107;
                      isOwned = _out1108;
                      isErased = _out1109;
                      readIdents = _out1110;
                    }
                  }
                }
              } else if (_source62.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1677___mcc_h745 = _source62.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1678_recursiveGen;
                  bool _1679_recOwned;
                  bool _1680_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1681_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1111;
                  bool _out1112;
                  bool _out1113;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1114;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1111, out _out1112, out _out1113, out _out1114);
                  _1678_recursiveGen = _out1111;
                  _1679_recOwned = _out1112;
                  _1680_recErased = _out1113;
                  _1681_recIdents = _out1114;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1678_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1679_recOwned;
                  isErased = _1680_recErased;
                  readIdents = _1681_recIdents;
                }
              } else if (_source62.is_Array) {
                DAST._IType _1682___mcc_h747 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1683_recursiveGen;
                  bool _1684_recOwned;
                  bool _1685_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1686_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1115;
                  bool _out1116;
                  bool _out1117;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1118;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1115, out _out1116, out _out1117, out _out1118);
                  _1683_recursiveGen = _out1115;
                  _1684_recOwned = _out1116;
                  _1685_recErased = _out1117;
                  _1686_recIdents = _out1118;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1683_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1684_recOwned;
                  isErased = _1685_recErased;
                  readIdents = _1686_recIdents;
                }
              } else if (_source62.is_Seq) {
                DAST._IType _1687___mcc_h749 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1688_recursiveGen;
                  bool _1689_recOwned;
                  bool _1690_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1691_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1119;
                  bool _out1120;
                  bool _out1121;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1122;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1119, out _out1120, out _out1121, out _out1122);
                  _1688_recursiveGen = _out1119;
                  _1689_recOwned = _out1120;
                  _1690_recErased = _out1121;
                  _1691_recIdents = _out1122;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1688_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1689_recOwned;
                  isErased = _1690_recErased;
                  readIdents = _1691_recIdents;
                }
              } else if (_source62.is_Set) {
                DAST._IType _1692___mcc_h751 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1693_recursiveGen;
                  bool _1694_recOwned;
                  bool _1695_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1123;
                  bool _out1124;
                  bool _out1125;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1126;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1123, out _out1124, out _out1125, out _out1126);
                  _1693_recursiveGen = _out1123;
                  _1694_recOwned = _out1124;
                  _1695_recErased = _out1125;
                  _1696_recIdents = _out1126;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1693_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1694_recOwned;
                  isErased = _1695_recErased;
                  readIdents = _1696_recIdents;
                }
              } else if (_source62.is_Multiset) {
                DAST._IType _1697___mcc_h753 = _source62.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1698_recursiveGen;
                  bool _1699_recOwned;
                  bool _1700_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1127;
                  bool _out1128;
                  bool _out1129;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1130;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1127, out _out1128, out _out1129, out _out1130);
                  _1698_recursiveGen = _out1127;
                  _1699_recOwned = _out1128;
                  _1700_recErased = _out1129;
                  _1701_recIdents = _out1130;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1698_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1699_recOwned;
                  isErased = _1700_recErased;
                  readIdents = _1701_recIdents;
                }
              } else if (_source62.is_Map) {
                DAST._IType _1702___mcc_h755 = _source62.dtor_key;
                DAST._IType _1703___mcc_h756 = _source62.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1704_recursiveGen;
                  bool _1705_recOwned;
                  bool _1706_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1707_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1131;
                  bool _out1132;
                  bool _out1133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1134;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1131, out _out1132, out _out1133, out _out1134);
                  _1704_recursiveGen = _out1131;
                  _1705_recOwned = _out1132;
                  _1706_recErased = _out1133;
                  _1707_recIdents = _out1134;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1704_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1705_recOwned;
                  isErased = _1706_recErased;
                  readIdents = _1707_recIdents;
                }
              } else if (_source62.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1708___mcc_h759 = _source62.dtor_args;
                DAST._IType _1709___mcc_h760 = _source62.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1710_recursiveGen;
                  bool _1711_recOwned;
                  bool _1712_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1713_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1135;
                  bool _out1136;
                  bool _out1137;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1138;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1135, out _out1136, out _out1137, out _out1138);
                  _1710_recursiveGen = _out1135;
                  _1711_recOwned = _out1136;
                  _1712_recErased = _out1137;
                  _1713_recIdents = _out1138;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1710_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1711_recOwned;
                  isErased = _1712_recErased;
                  readIdents = _1713_recIdents;
                }
              } else if (_source62.is_Primitive) {
                DAST._IPrimitive _1714___mcc_h763 = _source62.dtor_Primitive_a0;
                DAST._IPrimitive _source64 = _1714___mcc_h763;
                if (_source64.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1715_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1139;
                    _out1139 = DCOMP.COMP.GenType(_461_fromTpe, true, false);
                    _1715_rhsType = _out1139;
                    Dafny.ISequence<Dafny.Rune> _1716_recursiveGen;
                    bool _1717___v47;
                    bool _1718___v48;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1719_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1140;
                    bool _out1141;
                    bool _out1142;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1143;
                    DCOMP.COMP.GenExpr(_462_expr, @params, true, out _out1140, out _out1141, out _out1142, out _out1143);
                    _1716_recursiveGen = _out1140;
                    _1717___v47 = _out1141;
                    _1718___v48 = _out1142;
                    _1719_recIdents = _out1143;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1716_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1719_recIdents;
                  }
                } else if (_source64.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1720_recursiveGen;
                    bool _1721_recOwned;
                    bool _1722_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1723_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1144;
                    bool _out1145;
                    bool _out1146;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1147;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1144, out _out1145, out _out1146, out _out1147);
                    _1720_recursiveGen = _out1144;
                    _1721_recOwned = _out1145;
                    _1722_recErased = _out1146;
                    _1723_recIdents = _out1147;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1720_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1721_recOwned;
                    isErased = _1722_recErased;
                    readIdents = _1723_recIdents;
                  }
                } else if (_source64.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1724_recursiveGen;
                    bool _1725_recOwned;
                    bool _1726_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1727_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1148;
                    bool _out1149;
                    bool _out1150;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1151;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1148, out _out1149, out _out1150, out _out1151);
                    _1724_recursiveGen = _out1148;
                    _1725_recOwned = _out1149;
                    _1726_recErased = _out1150;
                    _1727_recIdents = _out1151;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1724_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1725_recOwned;
                    isErased = _1726_recErased;
                    readIdents = _1727_recIdents;
                  }
                } else if (_source64.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1728_recursiveGen;
                    bool _1729_recOwned;
                    bool _1730_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1731_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1152;
                    bool _out1153;
                    bool _out1154;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1155;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1152, out _out1153, out _out1154, out _out1155);
                    _1728_recursiveGen = _out1152;
                    _1729_recOwned = _out1153;
                    _1730_recErased = _out1154;
                    _1731_recIdents = _out1155;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1728_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1729_recOwned;
                    isErased = _1730_recErased;
                    readIdents = _1731_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _1732_recursiveGen;
                    bool _1733_recOwned;
                    bool _1734_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1735_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1156;
                    bool _out1157;
                    bool _out1158;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1159;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1156, out _out1157, out _out1158, out _out1159);
                    _1732_recursiveGen = _out1156;
                    _1733_recOwned = _out1157;
                    _1734_recErased = _out1158;
                    _1735_recIdents = _out1159;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1732_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1733_recOwned;
                    isErased = _1734_recErased;
                    readIdents = _1735_recIdents;
                  }
                }
              } else if (_source62.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1736___mcc_h765 = _source62.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1737_recursiveGen;
                  bool _1738___v55;
                  bool _1739___v56;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1740_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1160;
                  bool _out1161;
                  bool _out1162;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1163;
                  DCOMP.COMP.GenExpr(_462_expr, @params, true, out _out1160, out _out1161, out _out1162, out _out1163);
                  _1737_recursiveGen = _out1160;
                  _1738___v55 = _out1161;
                  _1739___v56 = _out1162;
                  _1740_recIdents = _out1163;
                  Dafny.ISequence<Dafny.Rune> _1741_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1164;
                  _out1164 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                  _1741_toTpeGen = _out1164;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _1737_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _1741_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _1740_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1742___mcc_h767 = _source62.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1743_recursiveGen;
                  bool _1744_recOwned;
                  bool _1745_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1746_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1165;
                  bool _out1166;
                  bool _out1167;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1168;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1165, out _out1166, out _out1167, out _out1168);
                  _1743_recursiveGen = _out1165;
                  _1744_recOwned = _out1166;
                  _1745_recErased = _out1167;
                  _1746_recIdents = _out1168;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1743_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1744_recOwned;
                  isErased = _1745_recErased;
                  readIdents = _1746_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _1747___mcc_h769 = _source26.dtor_TypeArg_a0;
              DAST._IType _source65 = _468___mcc_h121;
              if (_source65.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1748___mcc_h772 = _source65.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1749___mcc_h773 = _source65.dtor_typeArgs;
                DAST._IResolvedType _1750___mcc_h774 = _source65.dtor_resolved;
                DAST._IResolvedType _source66 = _1750___mcc_h774;
                if (_source66.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1751___mcc_h778 = _source66.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1752_recursiveGen;
                    bool _1753_recOwned;
                    bool _1754_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1169;
                    bool _out1170;
                    bool _out1171;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1172;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1169, out _out1170, out _out1171, out _out1172);
                    _1752_recursiveGen = _out1169;
                    _1753_recOwned = _out1170;
                    _1754_recErased = _out1171;
                    _1755_recIdents = _out1172;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1752_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1753_recOwned;
                    isErased = _1754_recErased;
                    readIdents = _1755_recIdents;
                  }
                } else if (_source66.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1756___mcc_h780 = _source66.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1757_recursiveGen;
                    bool _1758_recOwned;
                    bool _1759_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1173;
                    bool _out1174;
                    bool _out1175;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1176;
                    DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1173, out _out1174, out _out1175, out _out1176);
                    _1757_recursiveGen = _out1173;
                    _1758_recOwned = _out1174;
                    _1759_recErased = _out1175;
                    _1760_recIdents = _out1176;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1757_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1758_recOwned;
                    isErased = _1759_recErased;
                    readIdents = _1760_recIdents;
                  }
                } else {
                  DAST._IType _1761___mcc_h782 = _source66.dtor_Newtype_a0;
                  DAST._IType _1762_b = _1761___mcc_h782;
                  {
                    if (object.Equals(_461_fromTpe, _1762_b)) {
                      Dafny.ISequence<Dafny.Rune> _1763_recursiveGen;
                      bool _1764_recOwned;
                      bool _1765_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1766_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1177;
                      bool _out1178;
                      bool _out1179;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1180;
                      DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1177, out _out1178, out _out1179, out _out1180);
                      _1763_recursiveGen = _out1177;
                      _1764_recOwned = _out1178;
                      _1765_recErased = _out1179;
                      _1766_recIdents = _out1180;
                      Dafny.ISequence<Dafny.Rune> _1767_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1181;
                      _out1181 = DCOMP.COMP.GenType(_460_toTpe, true, false);
                      _1767_rhsType = _out1181;
                      Dafny.ISequence<Dafny.Rune> _1768_uneraseFn;
                      _1768_uneraseFn = ((_1764_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1767_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1768_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1763_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1764_recOwned;
                      isErased = false;
                      readIdents = _1766_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1182;
                      bool _out1183;
                      bool _out1184;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1185;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_462_expr, _461_fromTpe, _1762_b), _1762_b, _460_toTpe), @params, mustOwn, out _out1182, out _out1183, out _out1184, out _out1185);
                      s = _out1182;
                      isOwned = _out1183;
                      isErased = _out1184;
                      readIdents = _out1185;
                    }
                  }
                }
              } else if (_source65.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1769___mcc_h784 = _source65.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1770_recursiveGen;
                  bool _1771_recOwned;
                  bool _1772_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1773_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1186;
                  bool _out1187;
                  bool _out1188;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1189;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1186, out _out1187, out _out1188, out _out1189);
                  _1770_recursiveGen = _out1186;
                  _1771_recOwned = _out1187;
                  _1772_recErased = _out1188;
                  _1773_recIdents = _out1189;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1770_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1771_recOwned;
                  isErased = _1772_recErased;
                  readIdents = _1773_recIdents;
                }
              } else if (_source65.is_Array) {
                DAST._IType _1774___mcc_h786 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1775_recursiveGen;
                  bool _1776_recOwned;
                  bool _1777_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1190;
                  bool _out1191;
                  bool _out1192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1190, out _out1191, out _out1192, out _out1193);
                  _1775_recursiveGen = _out1190;
                  _1776_recOwned = _out1191;
                  _1777_recErased = _out1192;
                  _1778_recIdents = _out1193;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1775_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1776_recOwned;
                  isErased = _1777_recErased;
                  readIdents = _1778_recIdents;
                }
              } else if (_source65.is_Seq) {
                DAST._IType _1779___mcc_h788 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1780_recursiveGen;
                  bool _1781_recOwned;
                  bool _1782_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1783_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1194;
                  bool _out1195;
                  bool _out1196;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1197;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1194, out _out1195, out _out1196, out _out1197);
                  _1780_recursiveGen = _out1194;
                  _1781_recOwned = _out1195;
                  _1782_recErased = _out1196;
                  _1783_recIdents = _out1197;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1780_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1781_recOwned;
                  isErased = _1782_recErased;
                  readIdents = _1783_recIdents;
                }
              } else if (_source65.is_Set) {
                DAST._IType _1784___mcc_h790 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1785_recursiveGen;
                  bool _1786_recOwned;
                  bool _1787_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1198;
                  bool _out1199;
                  bool _out1200;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1201;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1198, out _out1199, out _out1200, out _out1201);
                  _1785_recursiveGen = _out1198;
                  _1786_recOwned = _out1199;
                  _1787_recErased = _out1200;
                  _1788_recIdents = _out1201;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1785_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1786_recOwned;
                  isErased = _1787_recErased;
                  readIdents = _1788_recIdents;
                }
              } else if (_source65.is_Multiset) {
                DAST._IType _1789___mcc_h792 = _source65.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1790_recursiveGen;
                  bool _1791_recOwned;
                  bool _1792_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1202;
                  bool _out1203;
                  bool _out1204;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1205;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1202, out _out1203, out _out1204, out _out1205);
                  _1790_recursiveGen = _out1202;
                  _1791_recOwned = _out1203;
                  _1792_recErased = _out1204;
                  _1793_recIdents = _out1205;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1790_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1791_recOwned;
                  isErased = _1792_recErased;
                  readIdents = _1793_recIdents;
                }
              } else if (_source65.is_Map) {
                DAST._IType _1794___mcc_h794 = _source65.dtor_key;
                DAST._IType _1795___mcc_h795 = _source65.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1796_recursiveGen;
                  bool _1797_recOwned;
                  bool _1798_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1799_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1206;
                  bool _out1207;
                  bool _out1208;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1209;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1206, out _out1207, out _out1208, out _out1209);
                  _1796_recursiveGen = _out1206;
                  _1797_recOwned = _out1207;
                  _1798_recErased = _out1208;
                  _1799_recIdents = _out1209;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1796_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1797_recOwned;
                  isErased = _1798_recErased;
                  readIdents = _1799_recIdents;
                }
              } else if (_source65.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1800___mcc_h798 = _source65.dtor_args;
                DAST._IType _1801___mcc_h799 = _source65.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1802_recursiveGen;
                  bool _1803_recOwned;
                  bool _1804_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1805_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1210;
                  bool _out1211;
                  bool _out1212;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1213;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1210, out _out1211, out _out1212, out _out1213);
                  _1802_recursiveGen = _out1210;
                  _1803_recOwned = _out1211;
                  _1804_recErased = _out1212;
                  _1805_recIdents = _out1213;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1802_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1803_recOwned;
                  isErased = _1804_recErased;
                  readIdents = _1805_recIdents;
                }
              } else if (_source65.is_Primitive) {
                DAST._IPrimitive _1806___mcc_h802 = _source65.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1807_recursiveGen;
                  bool _1808_recOwned;
                  bool _1809_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1810_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1214;
                  bool _out1215;
                  bool _out1216;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1217;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1214, out _out1215, out _out1216, out _out1217);
                  _1807_recursiveGen = _out1214;
                  _1808_recOwned = _out1215;
                  _1809_recErased = _out1216;
                  _1810_recIdents = _out1217;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1807_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1808_recOwned;
                  isErased = _1809_recErased;
                  readIdents = _1810_recIdents;
                }
              } else if (_source65.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1811___mcc_h804 = _source65.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1812_recursiveGen;
                  bool _1813_recOwned;
                  bool _1814_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1218;
                  bool _out1219;
                  bool _out1220;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1221;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1218, out _out1219, out _out1220, out _out1221);
                  _1812_recursiveGen = _out1218;
                  _1813_recOwned = _out1219;
                  _1814_recErased = _out1220;
                  _1815_recIdents = _out1221;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1812_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1813_recOwned;
                  isErased = _1814_recErased;
                  readIdents = _1815_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1816___mcc_h806 = _source65.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1817_recursiveGen;
                  bool _1818_recOwned;
                  bool _1819_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1222;
                  bool _out1223;
                  bool _out1224;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1225;
                  DCOMP.COMP.GenExpr(_462_expr, @params, mustOwn, out _out1222, out _out1223, out _out1224, out _out1225);
                  _1817_recursiveGen = _out1222;
                  _1818_recOwned = _out1223;
                  _1819_recErased = _out1224;
                  _1820_recIdents = _out1225;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1817_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1818_recOwned;
                  isErased = _1819_recErased;
                  readIdents = _1820_recIdents;
                }
              }
            }
          }
        }
      } else if (_source19.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _1821___mcc_h22 = _source19.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _1822_exprs = _1821___mcc_h22;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _1823_generatedValues;
          _1823_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _1824_i;
          _1824_i = BigInteger.Zero;
          bool _1825_allErased;
          _1825_allErased = true;
          while ((_1824_i) < (new BigInteger((_1822_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _1826_recursiveGen;
            bool _1827___v58;
            bool _1828_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1829_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1226;
            bool _out1227;
            bool _out1228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1229;
            DCOMP.COMP.GenExpr((_1822_exprs).Select(_1824_i), @params, true, out _out1226, out _out1227, out _out1228, out _out1229);
            _1826_recursiveGen = _out1226;
            _1827___v58 = _out1227;
            _1828_isErased = _out1228;
            _1829_recIdents = _out1229;
            _1825_allErased = (_1825_allErased) && (_1828_isErased);
            _1823_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_1823_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_1826_recursiveGen, _1828_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1829_recIdents);
            _1824_i = (_1824_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _1824_i = BigInteger.Zero;
          while ((_1824_i) < (new BigInteger((_1823_generatedValues).Count))) {
            if ((_1824_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _1830_gen;
            _1830_gen = ((_1823_generatedValues).Select(_1824_i)).dtor__0;
            if ((((_1823_generatedValues).Select(_1824_i)).dtor__1) && (!(_1825_allErased))) {
              _1830_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _1830_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1830_gen);
            _1824_i = (_1824_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _1825_allErased;
        }
      } else if (_source19.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _1831___mcc_h23 = _source19.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _1832_exprs = _1831___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _1833_generatedValues;
          _1833_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _1834_i;
          _1834_i = BigInteger.Zero;
          bool _1835_allErased;
          _1835_allErased = true;
          while ((_1834_i) < (new BigInteger((_1832_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _1836_recursiveGen;
            bool _1837___v59;
            bool _1838_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1839_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1230;
            bool _out1231;
            bool _out1232;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1233;
            DCOMP.COMP.GenExpr((_1832_exprs).Select(_1834_i), @params, true, out _out1230, out _out1231, out _out1232, out _out1233);
            _1836_recursiveGen = _out1230;
            _1837___v59 = _out1231;
            _1838_isErased = _out1232;
            _1839_recIdents = _out1233;
            _1835_allErased = (_1835_allErased) && (_1838_isErased);
            _1833_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_1833_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_1836_recursiveGen, _1838_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1839_recIdents);
            _1834_i = (_1834_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _1834_i = BigInteger.Zero;
          while ((_1834_i) < (new BigInteger((_1833_generatedValues).Count))) {
            if ((_1834_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _1840_gen;
            _1840_gen = ((_1833_generatedValues).Select(_1834_i)).dtor__0;
            if ((((_1833_generatedValues).Select(_1834_i)).dtor__1) && (!(_1835_allErased))) {
              _1840_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _1840_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _1840_gen);
            _1834_i = (_1834_i) + (BigInteger.One);
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
        DAST._IExpression _1841___mcc_h24 = _source19.dtor_cond;
        DAST._IExpression _1842___mcc_h25 = _source19.dtor_thn;
        DAST._IExpression _1843___mcc_h26 = _source19.dtor_els;
        DAST._IExpression _1844_f = _1843___mcc_h26;
        DAST._IExpression _1845_t = _1842___mcc_h25;
        DAST._IExpression _1846_cond = _1841___mcc_h24;
        {
          Dafny.ISequence<Dafny.Rune> _1847_condString;
          bool _1848___v60;
          bool _1849_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1850_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1234;
          bool _out1235;
          bool _out1236;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1237;
          DCOMP.COMP.GenExpr(_1846_cond, @params, true, out _out1234, out _out1235, out _out1236, out _out1237);
          _1847_condString = _out1234;
          _1848___v60 = _out1235;
          _1849_condErased = _out1236;
          _1850_recIdentsCond = _out1237;
          if (!(_1849_condErased)) {
            _1847_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1847_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _1851___v61;
          bool _1852_tHasToBeOwned;
          bool _1853___v62;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1854___v63;
          Dafny.ISequence<Dafny.Rune> _out1238;
          bool _out1239;
          bool _out1240;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1241;
          DCOMP.COMP.GenExpr(_1845_t, @params, mustOwn, out _out1238, out _out1239, out _out1240, out _out1241);
          _1851___v61 = _out1238;
          _1852_tHasToBeOwned = _out1239;
          _1853___v62 = _out1240;
          _1854___v63 = _out1241;
          Dafny.ISequence<Dafny.Rune> _1855_fString;
          bool _1856_fOwned;
          bool _1857_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1858_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1242;
          bool _out1243;
          bool _out1244;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1245;
          DCOMP.COMP.GenExpr(_1844_f, @params, _1852_tHasToBeOwned, out _out1242, out _out1243, out _out1244, out _out1245);
          _1855_fString = _out1242;
          _1856_fOwned = _out1243;
          _1857_fErased = _out1244;
          _1858_recIdentsF = _out1245;
          Dafny.ISequence<Dafny.Rune> _1859_tString;
          bool _1860___v64;
          bool _1861_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1862_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1246;
          bool _out1247;
          bool _out1248;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1249;
          DCOMP.COMP.GenExpr(_1845_t, @params, _1856_fOwned, out _out1246, out _out1247, out _out1248, out _out1249);
          _1859_tString = _out1246;
          _1860___v64 = _out1247;
          _1861_tErased = _out1248;
          _1862_recIdentsT = _out1249;
          if ((!(_1857_fErased)) || (!(_1861_tErased))) {
            if (_1857_fErased) {
              _1855_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1855_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_1861_tErased) {
              _1859_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1859_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _1847_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _1859_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _1855_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _1856_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1850_recIdentsCond, _1862_recIdentsT), _1858_recIdentsF);
          isErased = (_1857_fErased) || (_1861_tErased);
        }
      } else if (_source19.is_UnOp) {
        DAST._IUnaryOp _1863___mcc_h27 = _source19.dtor_unOp;
        DAST._IExpression _1864___mcc_h28 = _source19.dtor_expr;
        DAST._IUnaryOp _source67 = _1863___mcc_h27;
        if (_source67.is_Not) {
          DAST._IExpression _1865_e = _1864___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _1866_recursiveGen;
            bool _1867___v65;
            bool _1868_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1869_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1250;
            bool _out1251;
            bool _out1252;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1253;
            DCOMP.COMP.GenExpr(_1865_e, @params, true, out _out1250, out _out1251, out _out1252, out _out1253);
            _1866_recursiveGen = _out1250;
            _1867___v65 = _out1251;
            _1868_recErased = _out1252;
            _1869_recIdents = _out1253;
            if (!(_1868_recErased)) {
              _1866_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1866_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _1866_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _1869_recIdents;
            isErased = true;
          }
        } else if (_source67.is_BitwiseNot) {
          DAST._IExpression _1870_e = _1864___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _1871_recursiveGen;
            bool _1872___v66;
            bool _1873_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1254;
            bool _out1255;
            bool _out1256;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1257;
            DCOMP.COMP.GenExpr(_1870_e, @params, true, out _out1254, out _out1255, out _out1256, out _out1257);
            _1871_recursiveGen = _out1254;
            _1872___v66 = _out1255;
            _1873_recErased = _out1256;
            _1874_recIdents = _out1257;
            if (!(_1873_recErased)) {
              _1871_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1871_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _1871_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _1874_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _1875_e = _1864___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _1876_recursiveGen;
            bool _1877___v67;
            bool _1878_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1258;
            bool _out1259;
            bool _out1260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1261;
            DCOMP.COMP.GenExpr(_1875_e, @params, false, out _out1258, out _out1259, out _out1260, out _out1261);
            _1876_recursiveGen = _out1258;
            _1877___v67 = _out1259;
            _1878_recErased = _out1260;
            _1879_recIdents = _out1261;
            if (!(_1878_recErased)) {
              _1876_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len()"));
            isOwned = true;
            readIdents = _1879_recIdents;
            isErased = true;
          }
        }
      } else if (_source19.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _1880___mcc_h29 = _source19.dtor_op;
        DAST._IExpression _1881___mcc_h30 = _source19.dtor_left;
        DAST._IExpression _1882___mcc_h31 = _source19.dtor_right;
        DAST._IExpression _1883_r = _1882___mcc_h31;
        DAST._IExpression _1884_l = _1881___mcc_h30;
        Dafny.ISequence<Dafny.Rune> _1885_op = _1880___mcc_h29;
        {
          Dafny.ISequence<Dafny.Rune> _1886_left;
          bool _1887___v68;
          bool _1888_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1889_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1262;
          bool _out1263;
          bool _out1264;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1265;
          DCOMP.COMP.GenExpr(_1884_l, @params, true, out _out1262, out _out1263, out _out1264, out _out1265);
          _1886_left = _out1262;
          _1887___v68 = _out1263;
          _1888_leftErased = _out1264;
          _1889_recIdentsL = _out1265;
          Dafny.ISequence<Dafny.Rune> _1890_right;
          bool _1891___v69;
          bool _1892_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1266;
          bool _out1267;
          bool _out1268;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1269;
          DCOMP.COMP.GenExpr(_1883_r, @params, true, out _out1266, out _out1267, out _out1268, out _out1269);
          _1890_right = _out1266;
          _1891___v69 = _out1267;
          _1892_rightErased = _out1268;
          _1893_recIdentsR = _out1269;
          if (!(_1888_leftErased)) {
            _1886_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1886_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_1892_rightErased)) {
            _1890_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _1890_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_1885_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _1886_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _1890_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_1885_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _1886_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _1890_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1886_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _1885_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _1890_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1889_recIdentsL, _1893_recIdentsR);
          isErased = true;
        }
      } else if (_source19.is_Select) {
        DAST._IExpression _1894___mcc_h32 = _source19.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1895___mcc_h33 = _source19.dtor_field;
        bool _1896___mcc_h34 = _source19.dtor_isConstant;
        bool _1897___mcc_h35 = _source19.dtor_onDatatype;
        bool _1898_isDatatype = _1897___mcc_h35;
        bool _1899_isConstant = _1896___mcc_h34;
        Dafny.ISequence<Dafny.Rune> _1900_field = _1895___mcc_h33;
        DAST._IExpression _1901_on = _1894___mcc_h32;
        {
          Dafny.ISequence<Dafny.Rune> _1902_onString;
          bool _1903_onOwned;
          bool _1904_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1905_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1270;
          bool _out1271;
          bool _out1272;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1273;
          DCOMP.COMP.GenExpr(_1901_on, @params, false, out _out1270, out _out1271, out _out1272, out _out1273);
          _1902_onString = _out1270;
          _1903_onOwned = _out1271;
          _1904_onErased = _out1272;
          _1905_recIdents = _out1273;
          if (!(_1904_onErased)) {
            Dafny.ISequence<Dafny.Rune> _1906_eraseFn;
            _1906_eraseFn = ((_1903_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _1902_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _1906_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1902_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_1898_isDatatype) || (_1899_isConstant)) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1902_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _1900_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            if (_1899_isConstant) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            }
            if (mustOwn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            } else {
              isOwned = false;
            }
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _1902_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _1900_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          }
          isErased = false;
          readIdents = _1905_recIdents;
        }
      } else if (_source19.is_SelectFn) {
        DAST._IExpression _1907___mcc_h36 = _source19.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _1908___mcc_h37 = _source19.dtor_field;
        bool _1909___mcc_h38 = _source19.dtor_onDatatype;
        bool _1910___mcc_h39 = _source19.dtor_isStatic;
        BigInteger _1911___mcc_h40 = _source19.dtor_arity;
        BigInteger _1912_arity = _1911___mcc_h40;
        bool _1913_isStatic = _1910___mcc_h39;
        bool _1914_isDatatype = _1909___mcc_h38;
        Dafny.ISequence<Dafny.Rune> _1915_field = _1908___mcc_h37;
        DAST._IExpression _1916_on = _1907___mcc_h36;
        {
          Dafny.ISequence<Dafny.Rune> _1917_onString;
          bool _1918_onOwned;
          bool _1919___v70;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1920_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1274;
          bool _out1275;
          bool _out1276;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1277;
          DCOMP.COMP.GenExpr(_1916_on, @params, false, out _out1274, out _out1275, out _out1276, out _out1277);
          _1917_onString = _out1274;
          _1918_onOwned = _out1275;
          _1919___v70 = _out1276;
          _1920_recIdents = _out1277;
          if (_1913_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1917_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1915_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1917_onString), ((_1918_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _1921_args;
            _1921_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _1922_i;
            _1922_i = BigInteger.Zero;
            while ((_1922_i) < (_1912_arity)) {
              if ((_1922_i).Sign == 1) {
                _1921_args = Dafny.Sequence<Dafny.Rune>.Concat(_1921_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1921_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1921_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_1922_i));
              _1922_i = (_1922_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1921_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _1915_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1921_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = true;
          readIdents = _1920_recIdents;
        }
      } else if (_source19.is_TupleSelect) {
        DAST._IExpression _1923___mcc_h41 = _source19.dtor_expr;
        BigInteger _1924___mcc_h42 = _source19.dtor_index;
        BigInteger _1925_idx = _1924___mcc_h42;
        DAST._IExpression _1926_on = _1923___mcc_h41;
        {
          Dafny.ISequence<Dafny.Rune> _1927_onString;
          bool _1928___v71;
          bool _1929_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1930_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1278;
          bool _out1279;
          bool _out1280;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1281;
          DCOMP.COMP.GenExpr(_1926_on, @params, false, out _out1278, out _out1279, out _out1280, out _out1281);
          _1927_onString = _out1278;
          _1928___v71 = _out1279;
          _1929_tupErased = _out1280;
          _1930_recIdents = _out1281;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1927_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_1925_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _1929_tupErased;
          readIdents = _1930_recIdents;
        }
      } else if (_source19.is_Call) {
        DAST._IExpression _1931___mcc_h43 = _source19.dtor_on;
        Dafny.ISequence<Dafny.Rune> _1932___mcc_h44 = _source19.dtor_name;
        Dafny.ISequence<DAST._IType> _1933___mcc_h45 = _source19.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _1934___mcc_h46 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _1935_args = _1934___mcc_h46;
        Dafny.ISequence<DAST._IType> _1936_typeArgs = _1933___mcc_h45;
        Dafny.ISequence<Dafny.Rune> _1937_name = _1932___mcc_h44;
        DAST._IExpression _1938_on = _1931___mcc_h43;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _1939_typeArgString;
          _1939_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_1936_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _1940_typeI;
            _1940_typeI = BigInteger.Zero;
            _1939_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_1940_typeI) < (new BigInteger((_1936_typeArgs).Count))) {
              if ((_1940_typeI).Sign == 1) {
                _1939_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_1939_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _1941_typeString;
              Dafny.ISequence<Dafny.Rune> _out1282;
              _out1282 = DCOMP.COMP.GenType((_1936_typeArgs).Select(_1940_typeI), false, false);
              _1941_typeString = _out1282;
              _1939_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_1939_typeArgString, _1941_typeString);
              _1940_typeI = (_1940_typeI) + (BigInteger.One);
            }
            _1939_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_1939_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _1942_argString;
          _1942_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _1943_i;
          _1943_i = BigInteger.Zero;
          while ((_1943_i) < (new BigInteger((_1935_args).Count))) {
            if ((_1943_i).Sign == 1) {
              _1942_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1942_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _1944_argExpr;
            bool _1945_isOwned;
            bool _1946_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1947_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1283;
            bool _out1284;
            bool _out1285;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1286;
            DCOMP.COMP.GenExpr((_1935_args).Select(_1943_i), @params, false, out _out1283, out _out1284, out _out1285, out _out1286);
            _1944_argExpr = _out1283;
            _1945_isOwned = _out1284;
            _1946_argErased = _out1285;
            _1947_argIdents = _out1286;
            if (_1945_isOwned) {
              _1944_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _1944_argExpr);
            }
            _1942_argString = Dafny.Sequence<Dafny.Rune>.Concat(_1942_argString, _1944_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1947_argIdents);
            _1943_i = (_1943_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _1948_enclosingString;
          bool _1949___v72;
          bool _1950___v73;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1951_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1287;
          bool _out1288;
          bool _out1289;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1290;
          DCOMP.COMP.GenExpr(_1938_on, @params, false, out _out1287, out _out1288, out _out1289, out _out1290);
          _1948_enclosingString = _out1287;
          _1949___v72 = _out1288;
          _1950___v73 = _out1289;
          _1951_recIdents = _out1290;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1951_recIdents);
          DAST._IExpression _source68 = _1938_on;
          if (_source68.is_Literal) {
            DAST._ILiteral _1952___mcc_h808 = _source68.dtor_Literal_a0;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _1953___mcc_h810 = _source68.dtor_Ident_a0;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1954___mcc_h812 = _source68.dtor_Companion_a0;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_1948_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source68.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _1955___mcc_h814 = _source68.dtor_Tuple_a0;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1956___mcc_h816 = _source68.dtor_path;
            Dafny.ISequence<DAST._IExpression> _1957___mcc_h817 = _source68.dtor_args;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _1958___mcc_h820 = _source68.dtor_dims;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1959___mcc_h822 = _source68.dtor_path;
            Dafny.ISequence<Dafny.Rune> _1960___mcc_h823 = _source68.dtor_variant;
            bool _1961___mcc_h824 = _source68.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1962___mcc_h825 = _source68.dtor_contents;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Convert) {
            DAST._IExpression _1963___mcc_h830 = _source68.dtor_value;
            DAST._IType _1964___mcc_h831 = _source68.dtor_from;
            DAST._IType _1965___mcc_h832 = _source68.dtor_typ;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _1966___mcc_h836 = _source68.dtor_elements;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _1967___mcc_h838 = _source68.dtor_elements;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_This) {
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Ite) {
            DAST._IExpression _1968___mcc_h840 = _source68.dtor_cond;
            DAST._IExpression _1969___mcc_h841 = _source68.dtor_thn;
            DAST._IExpression _1970___mcc_h842 = _source68.dtor_els;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_UnOp) {
            DAST._IUnaryOp _1971___mcc_h846 = _source68.dtor_unOp;
            DAST._IExpression _1972___mcc_h847 = _source68.dtor_expr;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _1973___mcc_h850 = _source68.dtor_op;
            DAST._IExpression _1974___mcc_h851 = _source68.dtor_left;
            DAST._IExpression _1975___mcc_h852 = _source68.dtor_right;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Select) {
            DAST._IExpression _1976___mcc_h856 = _source68.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _1977___mcc_h857 = _source68.dtor_field;
            bool _1978___mcc_h858 = _source68.dtor_isConstant;
            bool _1979___mcc_h859 = _source68.dtor_onDatatype;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_SelectFn) {
            DAST._IExpression _1980___mcc_h864 = _source68.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _1981___mcc_h865 = _source68.dtor_field;
            bool _1982___mcc_h866 = _source68.dtor_onDatatype;
            bool _1983___mcc_h867 = _source68.dtor_isStatic;
            BigInteger _1984___mcc_h868 = _source68.dtor_arity;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_TupleSelect) {
            DAST._IExpression _1985___mcc_h874 = _source68.dtor_expr;
            BigInteger _1986___mcc_h875 = _source68.dtor_index;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Call) {
            DAST._IExpression _1987___mcc_h878 = _source68.dtor_on;
            Dafny.ISequence<Dafny.Rune> _1988___mcc_h879 = _source68.dtor_name;
            Dafny.ISequence<DAST._IType> _1989___mcc_h880 = _source68.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _1990___mcc_h881 = _source68.dtor_args;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _1991___mcc_h886 = _source68.dtor_params;
            DAST._IType _1992___mcc_h887 = _source68.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _1993___mcc_h888 = _source68.dtor_body;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _1994___mcc_h892 = _source68.dtor_name;
            DAST._IType _1995___mcc_h893 = _source68.dtor_typ;
            DAST._IExpression _1996___mcc_h894 = _source68.dtor_value;
            DAST._IExpression _1997___mcc_h895 = _source68.dtor_iifeBody;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_Apply) {
            DAST._IExpression _1998___mcc_h900 = _source68.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _1999___mcc_h901 = _source68.dtor_args;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source68.is_TypeTest) {
            DAST._IExpression _2000___mcc_h904 = _source68.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2001___mcc_h905 = _source68.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2002___mcc_h906 = _source68.dtor_variant;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _2003___mcc_h910 = _source68.dtor_typ;
            {
              _1948_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1948_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1948_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_1937_name)), _1939_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1942_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source19.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2004___mcc_h47 = _source19.dtor_params;
        DAST._IType _2005___mcc_h48 = _source19.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2006___mcc_h49 = _source19.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2007_body = _2006___mcc_h49;
        DAST._IType _2008_retType = _2005___mcc_h48;
        Dafny.ISequence<DAST._IFormal> _2009_params = _2004___mcc_h47;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2010_paramNames;
          _2010_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2011_i;
          _2011_i = BigInteger.Zero;
          while ((_2011_i) < (new BigInteger((_2009_params).Count))) {
            _2010_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2010_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2009_params).Select(_2011_i)).dtor_name));
            _2011_i = (_2011_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2012_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1291;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
          DCOMP.COMP.GenStmts(_2007_body, _2010_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1291, out _out1292);
          _2012_recursiveGen = _out1291;
          _2013_recIdents = _out1292;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2014_allReadCloned;
          _2014_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2013_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2015_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2013_recIdents).Elements) {
              _2015_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2013_recIdents).Contains(_2015_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1475)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2010_paramNames).Contains(_2015_next))) {
              _2014_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2014_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2015_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2015_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2015_next));
            }
            _2013_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2013_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2015_next));
          }
          Dafny.ISequence<Dafny.Rune> _2016_paramsString;
          _2016_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2011_i = BigInteger.Zero;
          while ((_2011_i) < (new BigInteger((_2009_params).Count))) {
            if ((_2011_i).Sign == 1) {
              _2016_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2016_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2017_typStr;
            Dafny.ISequence<Dafny.Rune> _out1293;
            _out1293 = DCOMP.COMP.GenType(((_2009_params).Select(_2011_i)).dtor_typ, false, true);
            _2017_typStr = _out1293;
            _2016_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2016_paramsString, ((_2009_params).Select(_2011_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2017_typStr);
            _2011_i = (_2011_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2018_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1294;
          _out1294 = DCOMP.COMP.GenType(_2008_retType, false, true);
          _2018_retTypeGen = _out1294;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper({\n"), _2014_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::boxed::Box::new(move |")), _2016_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2018_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2012_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2019___mcc_h50 = _source19.dtor_name;
        DAST._IType _2020___mcc_h51 = _source19.dtor_typ;
        DAST._IExpression _2021___mcc_h52 = _source19.dtor_value;
        DAST._IExpression _2022___mcc_h53 = _source19.dtor_iifeBody;
        DAST._IExpression _2023_iifeBody = _2022___mcc_h53;
        DAST._IExpression _2024_value = _2021___mcc_h52;
        DAST._IType _2025_tpe = _2020___mcc_h51;
        Dafny.ISequence<Dafny.Rune> _2026_name = _2019___mcc_h50;
        {
          Dafny.ISequence<Dafny.Rune> _2027_valueGen;
          bool _2028_valueOwned;
          bool _2029_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2030_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1295;
          bool _out1296;
          bool _out1297;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1298;
          DCOMP.COMP.GenExpr(_2024_value, @params, false, out _out1295, out _out1296, out _out1297, out _out1298);
          _2027_valueGen = _out1295;
          _2028_valueOwned = _out1296;
          _2029_valueErased = _out1297;
          _2030_recIdents = _out1298;
          if (_2029_valueErased) {
            Dafny.ISequence<Dafny.Rune> _2031_eraseFn;
            _2031_eraseFn = ((_2028_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
            _2027_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::"), _2031_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2027_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2030_recIdents;
          Dafny.ISequence<Dafny.Rune> _2032_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1299;
          _out1299 = DCOMP.COMP.GenType(_2025_tpe, false, true);
          _2032_valueTypeGen = _out1299;
          Dafny.ISequence<Dafny.Rune> _2033_bodyGen;
          bool _2034_bodyOwned;
          bool _2035_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2036_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1300;
          bool _out1301;
          bool _out1302;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1303;
          DCOMP.COMP.GenExpr(_2023_iifeBody, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, ((_2028_valueOwned) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2026_name))))), mustOwn, out _out1300, out _out1301, out _out1302, out _out1303);
          _2033_bodyGen = _out1300;
          _2034_bodyOwned = _out1301;
          _2035_bodyErased = _out1302;
          _2036_bodyIdents = _out1303;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2036_bodyIdents);
          Dafny.ISequence<Dafny.Rune> _2037_eraseFn;
          _2037_eraseFn = ((_2028_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2026_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((_2028_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")))), _2032_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2027_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2033_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2034_bodyOwned;
          isErased = _2035_bodyErased;
        }
      } else if (_source19.is_Apply) {
        DAST._IExpression _2038___mcc_h54 = _source19.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2039___mcc_h55 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2040_args = _2039___mcc_h55;
        DAST._IExpression _2041_func = _2038___mcc_h54;
        {
          Dafny.ISequence<Dafny.Rune> _2042_funcString;
          bool _2043___v76;
          bool _2044_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2045_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1304;
          bool _out1305;
          bool _out1306;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1307;
          DCOMP.COMP.GenExpr(_2041_func, @params, false, out _out1304, out _out1305, out _out1306, out _out1307);
          _2042_funcString = _out1304;
          _2043___v76 = _out1305;
          _2044_funcErased = _out1306;
          _2045_recIdents = _out1307;
          readIdents = _2045_recIdents;
          Dafny.ISequence<Dafny.Rune> _2046_argString;
          _2046_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2047_i;
          _2047_i = BigInteger.Zero;
          while ((_2047_i) < (new BigInteger((_2040_args).Count))) {
            if ((_2047_i).Sign == 1) {
              _2046_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2046_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2048_argExpr;
            bool _2049_isOwned;
            bool _2050_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2051_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1308;
            bool _out1309;
            bool _out1310;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1311;
            DCOMP.COMP.GenExpr((_2040_args).Select(_2047_i), @params, false, out _out1308, out _out1309, out _out1310, out _out1311);
            _2048_argExpr = _out1308;
            _2049_isOwned = _out1309;
            _2050_argErased = _out1310;
            _2051_argIdents = _out1311;
            if (_2049_isOwned) {
              _2048_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2048_argExpr);
            }
            _2046_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2046_argString, _2048_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2051_argIdents);
            _2047_i = (_2047_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2042_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2046_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source19.is_TypeTest) {
        DAST._IExpression _2052___mcc_h56 = _source19.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2053___mcc_h57 = _source19.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2054___mcc_h58 = _source19.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2055_variant = _2054___mcc_h58;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2056_dType = _2053___mcc_h57;
        DAST._IExpression _2057_on = _2052___mcc_h56;
        {
          Dafny.ISequence<Dafny.Rune> _2058_exprGen;
          bool _2059___v77;
          bool _2060_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2061_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1312;
          bool _out1313;
          bool _out1314;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1315;
          DCOMP.COMP.GenExpr(_2057_on, @params, false, out _out1312, out _out1313, out _out1314, out _out1315);
          _2058_exprGen = _out1312;
          _2059___v77 = _out1313;
          _2060_exprErased = _out1314;
          _2061_recIdents = _out1315;
          Dafny.ISequence<Dafny.Rune> _2062_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1316;
          _out1316 = DCOMP.COMP.GenPath(_2056_dType);
          _2062_dTypePath = _out1316;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2058_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2062_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2055_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2061_recIdents;
        }
      } else {
        DAST._IType _2063___mcc_h59 = _source19.dtor_typ;
        DAST._IType _2064_typ = _2063___mcc_h59;
        {
          Dafny.ISequence<Dafny.Rune> _2065_typString;
          Dafny.ISequence<Dafny.Rune> _out1317;
          _out1317 = DCOMP.COMP.GenType(_2064_typ, false, false);
          _2065_typString = _out1317;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2065_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
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
      BigInteger _2066_i;
      _2066_i = BigInteger.Zero;
      while ((_2066_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2067_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1318;
        _out1318 = DCOMP.COMP.GenModule((p).Select(_2066_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2067_generated = _out1318;
        if ((_2066_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2067_generated);
        _2066_i = (_2066_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2068_i;
      _2068_i = BigInteger.Zero;
      while ((_2068_i) < (new BigInteger((fullName).Count))) {
        if ((_2068_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2068_i));
        _2068_i = (_2068_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

