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
    bool is_Nullable { get; }
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
    DAST._IType dtor_Nullable_a0 { get; }
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
    public static _IType create_Nullable(DAST._IType _a0) {
      return new Type_Nullable(_a0);
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
    public bool is_Nullable { get { return this is Type_Nullable; } }
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
    public DAST._IType dtor_Nullable_a0 {
      get {
        var d = this;
        return ((Type_Nullable)d)._a0;
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
  public class Type_Nullable : Type {
    public readonly DAST._IType _a0;
    public Type_Nullable(DAST._IType _a0) : base() {
      this._a0 = _a0;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Nullable(_a0);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Type_Nullable;
      return oth != null && object.Equals(this._a0, oth._a0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Type.Nullable";
      s += "(";
      s += Dafny.Helpers.ToString(this._a0);
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
      hash = ((hash << 5) + hash) + 2;
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
      hash = ((hash << 5) + hash) + 3;
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
      hash = ((hash << 5) + hash) + 4;
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
      hash = ((hash << 5) + hash) + 5;
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
      hash = ((hash << 5) + hash) + 6;
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
      hash = ((hash << 5) + hash) + 7;
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
      hash = ((hash << 5) + hash) + 8;
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
      hash = ((hash << 5) + hash) + 9;
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
      hash = ((hash << 5) + hash) + 10;
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
      hash = ((hash << 5) + hash) + 11;
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
    Dafny.ISequence<Dafny.Rune> dtor_enclosingModule { get; }
    Dafny.ISequence<DAST._IType> dtor_typeParams { get; }
    Dafny.ISequence<DAST._IType> dtor_superClasses { get; }
    Dafny.ISequence<DAST._IField> dtor_fields { get; }
    Dafny.ISequence<DAST._IMethod> dtor_body { get; }
    _IClass DowncastClone();
  }
  public class Class : _IClass {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.Rune> _enclosingModule;
    public readonly Dafny.ISequence<DAST._IType> _typeParams;
    public readonly Dafny.ISequence<DAST._IType> _superClasses;
    public readonly Dafny.ISequence<DAST._IField> _fields;
    public readonly Dafny.ISequence<DAST._IMethod> _body;
    public Class(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<DAST._IType> typeParams, Dafny.ISequence<DAST._IType> superClasses, Dafny.ISequence<DAST._IField> fields, Dafny.ISequence<DAST._IMethod> body) {
      this._name = name;
      this._enclosingModule = enclosingModule;
      this._typeParams = typeParams;
      this._superClasses = superClasses;
      this._fields = fields;
      this._body = body;
    }
    public _IClass DowncastClone() {
      if (this is _IClass dt) { return dt; }
      return new Class(_name, _enclosingModule, _typeParams, _superClasses, _fields, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Class;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._enclosingModule, oth._enclosingModule) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._superClasses, oth._superClasses) && object.Equals(this._fields, oth._fields) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enclosingModule));
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
      s += Dafny.Helpers.ToString(this._enclosingModule);
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
    bool is_Break { get; }
    bool is_TailRecursive { get; }
    bool is_JumpTailCallStart { get; }
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
    DAST._IOptional<Dafny.ISequence<Dafny.Rune>> dtor_lbl { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    DAST._IExpression dtor_on { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<DAST._IExpression> dtor_args { get; }
    DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> dtor_outs { get; }
    DAST._IExpression dtor_expr { get; }
    DAST._IOptional<Dafny.ISequence<Dafny.Rune>> dtor_toLabel { get; }
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
    public static _IStatement create_While(DAST._IOptional<Dafny.ISequence<Dafny.Rune>> lbl, DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> body) {
      return new Statement_While(lbl, cond, body);
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
    public static _IStatement create_Break(DAST._IOptional<Dafny.ISequence<Dafny.Rune>> toLabel) {
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
    public bool is_While { get { return this is Statement_While; } }
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
    public DAST._IOptional<Dafny.ISequence<Dafny.Rune>> dtor_lbl {
      get {
        var d = this;
        return ((Statement_While)d)._lbl;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        var d = this;
        if (d is Statement_While) { return ((Statement_While)d)._body; }
        return ((Statement_TailRecursive)d)._body;
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
    public DAST._IOptional<Dafny.ISequence<Dafny.Rune>> dtor_toLabel {
      get {
        var d = this;
        return ((Statement_Break)d)._toLabel;
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
    public readonly DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _lbl;
    public readonly DAST._IExpression _cond;
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public Statement_While(DAST._IOptional<Dafny.ISequence<Dafny.Rune>> lbl, DAST._IExpression cond, Dafny.ISequence<DAST._IStatement> body) : base() {
      this._lbl = lbl;
      this._cond = cond;
      this._body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_While(_lbl, _cond, _body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_While;
      return oth != null && object.Equals(this._lbl, oth._lbl) && object.Equals(this._cond, oth._cond) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lbl));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.While";
      s += "(";
      s += Dafny.Helpers.ToString(this._lbl);
      s += ", ";
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
  public class Statement_Break : Statement {
    public readonly DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _toLabel;
    public Statement_Break(DAST._IOptional<Dafny.ISequence<Dafny.Rune>> toLabel) : base() {
      this._toLabel = toLabel;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_Break(_toLabel);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_Break;
      return oth != null && object.Equals(this._toLabel, oth._toLabel);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._toLabel));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.Break";
      s += "(";
      s += Dafny.Helpers.ToString(this._toLabel);
      s += ")";
      return s;
    }
  }
  public class Statement_TailRecursive : Statement {
    public readonly Dafny.ISequence<DAST._IStatement> _body;
    public Statement_TailRecursive(Dafny.ISequence<DAST._IStatement> body) : base() {
      this._body = body;
    }
    public override _IStatement DowncastClone() {
      if (this is _IStatement dt) { return dt; }
      return new Statement_TailRecursive(_body);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Statement_TailRecursive;
      return oth != null && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Statement.TailRecursive";
      s += "(";
      s += Dafny.Helpers.ToString(this._body);
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
      hash = ((hash << 5) + hash) + 9;
      return (int)hash;
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
      hash = ((hash << 5) + hash) + 10;
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
      hash = ((hash << 5) + hash) + 11;
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
    bool is_Index { get; }
    Dafny.ISequence<Dafny.Rune> dtor_Ident_a0 { get; }
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
    public Dafny.ISequence<Dafny.Rune> dtor_Ident_a0 {
      get {
        var d = this;
        return ((AssignLhs_Ident)d)._a0;
      }
    }
    public DAST._IExpression dtor_expr {
      get {
        var d = this;
        if (d is AssignLhs_Select) { return ((AssignLhs_Select)d)._expr; }
        return ((AssignLhs_Index)d)._expr;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        return ((AssignLhs_Select)d)._field;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_indices {
      get {
        var d = this;
        return ((AssignLhs_Index)d)._indices;
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
  public class AssignLhs_Index : AssignLhs {
    public readonly DAST._IExpression _expr;
    public readonly Dafny.ISequence<DAST._IExpression> _indices;
    public AssignLhs_Index(DAST._IExpression expr, Dafny.ISequence<DAST._IExpression> indices) : base() {
      this._expr = expr;
      this._indices = indices;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Index(_expr, _indices);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Index;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._indices, oth._indices);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indices));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._indices);
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
    bool is_ArrayLen { get; }
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
    bool dtor_isArray { get; }
    Dafny.ISequence<DAST._IExpression> dtor_indices { get; }
    DAST._IOptional<DAST._IExpression> dtor_low { get; }
    DAST._IOptional<DAST._IExpression> dtor_high { get; }
    BigInteger dtor_index { get; }
    DAST._IExpression dtor_on { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<DAST._IType> dtor_typeArgs { get; }
    Dafny.ISequence<DAST._IFormal> dtor_params { get; }
    DAST._IType dtor_retType { get; }
    Dafny.ISequence<DAST._IStatement> dtor_body { get; }
    Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> dtor_values { get; }
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
    public static _IExpression create_ArrayLen(DAST._IExpression expr) {
      return new Expression_ArrayLen(expr);
    }
    public static _IExpression create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant, bool onDatatype) {
      return new Expression_Select(expr, field, isConstant, onDatatype);
    }
    public static _IExpression create_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, BigInteger arity) {
      return new Expression_SelectFn(expr, field, onDatatype, isStatic, arity);
    }
    public static _IExpression create_Index(DAST._IExpression expr, bool isArray, Dafny.ISequence<DAST._IExpression> indices) {
      return new Expression_Index(expr, isArray, indices);
    }
    public static _IExpression create_IndexRange(DAST._IExpression expr, bool isArray, DAST._IOptional<DAST._IExpression> low, DAST._IOptional<DAST._IExpression> high) {
      return new Expression_IndexRange(expr, isArray, low, high);
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
    public bool is_ArrayLen { get { return this is Expression_ArrayLen; } }
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
        if (d is Expression_ArrayLen) { return ((Expression_ArrayLen)d)._expr; }
        if (d is Expression_Select) { return ((Expression_Select)d)._expr; }
        if (d is Expression_SelectFn) { return ((Expression_SelectFn)d)._expr; }
        if (d is Expression_Index) { return ((Expression_Index)d)._expr; }
        if (d is Expression_IndexRange) { return ((Expression_IndexRange)d)._expr; }
        if (d is Expression_TupleSelect) { return ((Expression_TupleSelect)d)._expr; }
        if (d is Expression_BetaRedex) { return ((Expression_BetaRedex)d)._expr; }
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
    public bool dtor_isArray {
      get {
        var d = this;
        if (d is Expression_Index) { return ((Expression_Index)d)._isArray; }
        return ((Expression_IndexRange)d)._isArray;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_indices {
      get {
        var d = this;
        return ((Expression_Index)d)._indices;
      }
    }
    public DAST._IOptional<DAST._IExpression> dtor_low {
      get {
        var d = this;
        return ((Expression_IndexRange)d)._low;
      }
    }
    public DAST._IOptional<DAST._IExpression> dtor_high {
      get {
        var d = this;
        return ((Expression_IndexRange)d)._high;
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
        if (d is Expression_Lambda) { return ((Expression_Lambda)d)._retType; }
        return ((Expression_BetaRedex)d)._retType;
      }
    }
    public Dafny.ISequence<DAST._IStatement> dtor_body {
      get {
        var d = this;
        return ((Expression_Lambda)d)._body;
      }
    }
    public Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> dtor_values {
      get {
        var d = this;
        return ((Expression_BetaRedex)d)._values;
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
  public class Expression_ArrayLen : Expression {
    public readonly DAST._IExpression _expr;
    public Expression_ArrayLen(DAST._IExpression expr) : base() {
      this._expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_ArrayLen(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_ArrayLen;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.ArrayLen";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
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
      hash = ((hash << 5) + hash) + 15;
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
      hash = ((hash << 5) + hash) + 16;
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
  public class Expression_Index : Expression {
    public readonly DAST._IExpression _expr;
    public readonly bool _isArray;
    public readonly Dafny.ISequence<DAST._IExpression> _indices;
    public Expression_Index(DAST._IExpression expr, bool isArray, Dafny.ISequence<DAST._IExpression> indices) : base() {
      this._expr = expr;
      this._isArray = isArray;
      this._indices = indices;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Index(_expr, _isArray, _indices);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Index;
      return oth != null && object.Equals(this._expr, oth._expr) && this._isArray == oth._isArray && object.Equals(this._indices, oth._indices);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isArray));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indices));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isArray);
      s += ", ";
      s += Dafny.Helpers.ToString(this._indices);
      s += ")";
      return s;
    }
  }
  public class Expression_IndexRange : Expression {
    public readonly DAST._IExpression _expr;
    public readonly bool _isArray;
    public readonly DAST._IOptional<DAST._IExpression> _low;
    public readonly DAST._IOptional<DAST._IExpression> _high;
    public Expression_IndexRange(DAST._IExpression expr, bool isArray, DAST._IOptional<DAST._IExpression> low, DAST._IOptional<DAST._IExpression> high) : base() {
      this._expr = expr;
      this._isArray = isArray;
      this._low = low;
      this._high = high;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_IndexRange(_expr, _isArray, _low, _high);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_IndexRange;
      return oth != null && object.Equals(this._expr, oth._expr) && this._isArray == oth._isArray && object.Equals(this._low, oth._low) && object.Equals(this._high, oth._high);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._isArray));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._low));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._high));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.IndexRange";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._isArray);
      s += ", ";
      s += Dafny.Helpers.ToString(this._low);
      s += ", ";
      s += Dafny.Helpers.ToString(this._high);
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
      hash = ((hash << 5) + hash) + 19;
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
      hash = ((hash << 5) + hash) + 20;
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
      hash = ((hash << 5) + hash) + 21;
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
  public class Expression_BetaRedex : Expression {
    public readonly Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _values;
    public readonly DAST._IType _retType;
    public readonly DAST._IExpression _expr;
    public Expression_BetaRedex(Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> values, DAST._IType retType, DAST._IExpression expr) : base() {
      this._values = values;
      this._retType = retType;
      this._expr = expr;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_BetaRedex(_values, _retType, _expr);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_BetaRedex;
      return oth != null && object.Equals(this._values, oth._values) && object.Equals(this._retType, oth._retType) && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._values));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.BetaRedex";
      s += "(";
      s += Dafny.Helpers.ToString(this._values);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._expr);
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
      hash = ((hash << 5) + hash) + 23;
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
      hash = ((hash << 5) + hash) + 24;
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
      hash = ((hash << 5) + hash) + 25;
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
      hash = ((hash << 5) + hash) + 26;
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
            DCOMP.COMP.GenExpr(_25_e, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out11, out _out12, out _out13, out _out14);
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
          } else if (_source2.is_Nullable) {
            DAST._IType _48___mcc_h13 = _source2.dtor_Nullable_a0;
          } else if (_source2.is_Tuple) {
            Dafny.ISequence<DAST._IType> _49___mcc_h15 = _source2.dtor_Tuple_a0;
          } else if (_source2.is_Array) {
            DAST._IType _50___mcc_h17 = _source2.dtor_element;
          } else if (_source2.is_Seq) {
            DAST._IType _51___mcc_h19 = _source2.dtor_element;
          } else if (_source2.is_Set) {
            DAST._IType _52___mcc_h21 = _source2.dtor_element;
          } else if (_source2.is_Multiset) {
            DAST._IType _53___mcc_h23 = _source2.dtor_element;
          } else if (_source2.is_Map) {
            DAST._IType _54___mcc_h25 = _source2.dtor_key;
            DAST._IType _55___mcc_h26 = _source2.dtor_value;
          } else if (_source2.is_Arrow) {
            Dafny.ISequence<DAST._IType> _56___mcc_h29 = _source2.dtor_args;
            DAST._IType _57___mcc_h30 = _source2.dtor_result;
          } else if (_source2.is_Primitive) {
            DAST._IPrimitive _58___mcc_h33 = _source2.dtor_Primitive_a0;
          } else if (_source2.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _59___mcc_h35 = _source2.dtor_Passthrough_a0;
          } else {
            Dafny.ISequence<Dafny.Rune> _60___mcc_h37 = _source2.dtor_TypeArg_a0;
          }
          _34_i = (_34_i) + (BigInteger.One);
        }
      }
      Dafny.ISequence<Dafny.Rune> _61_defaultImpl;
      _61_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      _61_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n"));
      _61_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_61_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new()\n"));
      _61_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      _61_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_61_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      Dafny.ISequence<Dafny.Rune> _62_printImpl;
      _62_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n"));
      _62_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_62_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(__fmt_print_formatter, \"")), ((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (c).dtor_name), (((new BigInteger(((c).dtor_fields).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"));
      BigInteger _63_i;
      _63_i = BigInteger.Zero;
      while ((_63_i) < (new BigInteger(((c).dtor_fields).Count))) {
        DAST._IField _64_field;
        _64_field = ((c).dtor_fields).Select(_63_i);
        if ((_63_i).Sign == 1) {
          _62_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_62_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \", \")?;"));
        }
        _62_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_62_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(::std::ops::Deref::deref(&(self.r#")), ((_64_field).dtor_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow())), __fmt_print_formatter, false)?;"));
        _63_i = (_63_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_fields).Count)).Sign == 1) {
        _62_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_62_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \")\")?;"));
      }
      _62_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_62_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nOk(())\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _65_ptrPartialEqImpl;
      _65_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _18_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::cmp::PartialEq for r#")), (c).dtor_name), _17_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      _65_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_65_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn eq(&self, other: &Self) -> bool {\n"));
      _65_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_65_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ptr::eq(self, other)"));
      _65_ptrPartialEqImpl = Dafny.Sequence<Dafny.Rune>.Concat(_65_ptrPartialEqImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _61_defaultImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _62_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _65_ptrPartialEqImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _66_typeParamsSet;
      _66_typeParamsSet = Dafny.Set<DAST._IType>.FromElements();
      Dafny.ISequence<Dafny.Rune> _67_typeParams;
      _67_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _68_tpI;
      _68_tpI = BigInteger.Zero;
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        _67_typeParams = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<");
        while ((_68_tpI) < (new BigInteger(((t).dtor_typeParams).Count))) {
          DAST._IType _69_tp;
          _69_tp = ((t).dtor_typeParams).Select(_68_tpI);
          _66_typeParamsSet = Dafny.Set<DAST._IType>.Union(_66_typeParamsSet, Dafny.Set<DAST._IType>.FromElements(_69_tp));
          Dafny.ISequence<Dafny.Rune> _70_genTp;
          Dafny.ISequence<Dafny.Rune> _out21;
          _out21 = DCOMP.COMP.GenType(_69_tp, false, false);
          _70_genTp = _out21;
          _67_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_67_typeParams, _70_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          _68_tpI = (_68_tpI) + (BigInteger.One);
        }
        _67_typeParams = Dafny.Sequence<Dafny.Rune>.Concat(_67_typeParams, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _71_fullPath;
      _71_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<Dafny.Rune> _72_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _73___v6;
      Dafny.ISequence<Dafny.Rune> _out22;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out23;
      DCOMP.COMP.GenClassImplBody((t).dtor_body, true, DAST.Type.create_Path(_71_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Trait(_71_fullPath)), _66_typeParamsSet, out _out22, out _out23);
      _72_implBody = _out22;
      _73___v6 = _out23;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub trait r#"), (t).dtor_name), _67_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _72_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenNewtype(DAST._INewtype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _74_typeParamsSet;
      Dafny.ISequence<Dafny.Rune> _75_typeParams;
      Dafny.ISequence<Dafny.Rune> _76_constrainedTypeParams;
      Dafny.ISet<DAST._IType> _out24;
      Dafny.ISequence<Dafny.Rune> _out25;
      Dafny.ISequence<Dafny.Rune> _out26;
      DCOMP.COMP.GenTypeParameters((c).dtor_typeParams, out _out24, out _out25, out _out26);
      _74_typeParamsSet = _out24;
      _75_typeParams = _out25;
      _76_constrainedTypeParams = _out26;
      Dafny.ISequence<Dafny.Rune> _77_underlyingType;
      Dafny.ISequence<Dafny.Rune> _out27;
      _out27 = DCOMP.COMP.GenType((c).dtor_base, false, false);
      _77_underlyingType = _out27;
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]\n#[repr(transparent)]\npub struct r#"), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(pub ")), _77_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _76_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyErasable for r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Erased = ")), _77_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn erase(&self) -> &Self::Erased {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn erase_owned(self) -> Self::Erased {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self.0\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _76_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<")), _77_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase(x: &")), _77_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> &Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe { &*(x as *const ")), _77_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as *const r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") }\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase_owned(x: ")), _77_underlyingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(x)\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _76_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase(x: &r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> &Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[inline]\nfn unerase_owned(x: r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> Self {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _76_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n"));
      DAST._IOptional<DAST._IExpression> _source4 = (c).dtor_witnessExpr;
      if (_source4.is_Some) {
        DAST._IExpression _78___mcc_h0 = _source4.dtor_Some_a0;
        DAST._IExpression _79_e = _78___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _80_eStr;
          bool _81___v7;
          bool _82___v8;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _83___v9;
          Dafny.ISequence<Dafny.Rune> _out28;
          bool _out29;
          bool _out30;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out31;
          DCOMP.COMP.GenExpr(_79_e, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out28, out _out29, out _out30, out _out31);
          _80_eStr = _out28;
          _81___v7 = _out29;
          _82___v8 = _out30;
          _83___v9 = _out31;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _80_eStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
        }
      } else {
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(::std::default::Default::default())\n"));
        }
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _76_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _75_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, __fmt_print_formatter, in_seq)\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenDatatype(DAST._IDatatype c) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISet<DAST._IType> _84_typeParamsSet;
      Dafny.ISequence<Dafny.Rune> _85_typeParams;
      Dafny.ISequence<Dafny.Rune> _86_constrainedTypeParams;
      Dafny.ISet<DAST._IType> _out32;
      Dafny.ISequence<Dafny.Rune> _out33;
      Dafny.ISequence<Dafny.Rune> _out34;
      DCOMP.COMP.GenTypeParameters((c).dtor_typeParams, out _out32, out _out33, out _out34);
      _84_typeParamsSet = _out32;
      _85_typeParams = _out33;
      _86_constrainedTypeParams = _out34;
      Dafny.ISequence<Dafny.Rune> _87_ctors;
      _87_ctors = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _88_i;
      _88_i = BigInteger.Zero;
      while ((_88_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _89_ctor;
        _89_ctor = ((c).dtor_ctors).Select(_88_i);
        Dafny.ISequence<Dafny.Rune> _90_ctorBody;
        _90_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_89_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        BigInteger _91_j;
        _91_j = BigInteger.Zero;
        while ((_91_j) < (new BigInteger(((_89_ctor).dtor_args).Count))) {
          DAST._IFormal _92_formal;
          _92_formal = ((_89_ctor).dtor_args).Select(_91_j);
          Dafny.ISequence<Dafny.Rune> _93_formalType;
          Dafny.ISequence<Dafny.Rune> _out35;
          _out35 = DCOMP.COMP.GenType((_92_formal).dtor_typ, false, false);
          _93_formalType = _out35;
          if ((c).dtor_isCo) {
            _90_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_90_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_92_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper<")), _93_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">, "));
          } else {
            _90_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_90_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_92_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _93_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          _91_j = (_91_j) + (BigInteger.One);
        }
        _90_ctorBody = Dafny.Sequence<Dafny.Rune>.Concat(_90_ctorBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        _87_ctors = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_87_ctors, _90_ctorBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
        _88_i = (_88_i) + (BigInteger.One);
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _94_selfPath;
      _94_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _95_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _96_traitBodies;
      Dafny.ISequence<Dafny.Rune> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _out37;
      DCOMP.COMP.GenClassImplBody((c).dtor_body, false, DAST.Type.create_Path(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedType.create_Datatype(_94_selfPath)), _84_typeParamsSet, out _out36, out _out37);
      _95_implBody = _out36;
      _96_traitBodies = _out37;
      _88_i = BigInteger.Zero;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _97_emittedFields;
      _97_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      while ((_88_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _98_ctor;
        _98_ctor = ((c).dtor_ctors).Select(_88_i);
        BigInteger _99_j;
        _99_j = BigInteger.Zero;
        while ((_99_j) < (new BigInteger(((_98_ctor).dtor_args).Count))) {
          DAST._IFormal _100_formal;
          _100_formal = ((_98_ctor).dtor_args).Select(_99_j);
          if (!((_97_emittedFields).Contains((_100_formal).dtor_name))) {
            _97_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_97_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_100_formal).dtor_name));
            Dafny.ISequence<Dafny.Rune> _101_formalType;
            Dafny.ISequence<Dafny.Rune> _out38;
            _out38 = DCOMP.COMP.GenType((_100_formal).dtor_typ, false, false);
            _101_formalType = _out38;
            Dafny.ISequence<Dafny.Rune> _102_methodBody;
            _102_methodBody = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n");
            BigInteger _103_k;
            _103_k = BigInteger.Zero;
            while ((_103_k) < (new BigInteger(((c).dtor_ctors).Count))) {
              DAST._IDatatypeCtor _104_ctor2;
              _104_ctor2 = ((c).dtor_ctors).Select(_103_k);
              Dafny.ISequence<Dafny.Rune> _105_ctorMatch;
              _105_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_104_ctor2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
              BigInteger _106_l;
              _106_l = BigInteger.Zero;
              bool _107_hasMatchingField;
              _107_hasMatchingField = false;
              while ((_106_l) < (new BigInteger(((_104_ctor2).dtor_args).Count))) {
                DAST._IFormal _108_formal2;
                _108_formal2 = ((_104_ctor2).dtor_args).Select(_106_l);
                if (((_100_formal).dtor_name).Equals((_108_formal2).dtor_name)) {
                  _107_hasMatchingField = true;
                }
                _105_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_105_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_108_formal2).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                _106_l = (_106_l) + (BigInteger.One);
              }
              if (_107_hasMatchingField) {
                if ((c).dtor_isCo) {
                  _105_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_105_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ::std::ops::Deref::deref(&")), (_100_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0),\n"));
                } else {
                  _105_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_105_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => ")), (_100_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"));
                }
              } else {
                _105_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_105_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("} => panic!(\"field does not exist on this variant\"),\n"));
              }
              _102_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_102_methodBody, _105_ctorMatch);
              _103_k = (_103_k) + (BigInteger.One);
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _102_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_102_methodBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..) => panic!(),\n"));
            }
            _102_methodBody = Dafny.Sequence<Dafny.Rune>.Concat(_102_methodBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            _95_implBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_95_implBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#")), (_100_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&self) -> &")), _101_formalType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _102_methodBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
          }
          _99_j = (_99_j) + (BigInteger.One);
        }
        _88_i = (_88_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _87_ctors = Dafny.Sequence<Dafny.Rune>.Concat(_87_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant("));
        BigInteger _109_typeI;
        _109_typeI = BigInteger.Zero;
        while ((_109_typeI) < (new BigInteger(((c).dtor_typeParams).Count))) {
          if ((_109_typeI).Sign == 1) {
            _87_ctors = Dafny.Sequence<Dafny.Rune>.Concat(_87_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _110_genTp;
          Dafny.ISequence<Dafny.Rune> _out39;
          _out39 = DCOMP.COMP.GenType(((c).dtor_typeParams).Select(_109_typeI), false, false);
          _110_genTp = _out39;
          _87_ctors = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_87_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData::<")), _110_genTp), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          _109_typeI = (_109_typeI) + (BigInteger.One);
        }
        _87_ctors = Dafny.Sequence<Dafny.Rune>.Concat(_87_ctors, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      Dafny.ISequence<Dafny.Rune> _111_enumBody;
      _111_enumBody = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq)]\npub enum r#"), (c).dtor_name), _85_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _87_ctors), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _86_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" r#")), (c).dtor_name), _85_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _95_implBody), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
      Dafny.ISequence<Dafny.Rune> _112_identEraseImpls;
      _112_identEraseImpls = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _86_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyErasable for r#")), (c).dtor_name), _85_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Erased = Self;\nfn erase(&self) -> &Self::Erased { self }\nfn erase_owned(self) -> Self::Erased { self }}\n"));
      _112_identEraseImpls = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_112_identEraseImpls, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl ")), _86_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyUnerasable<r#")), (c).dtor_name), _85_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> for r#")), (c).dtor_name), _85_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn unerase(x: &Self) -> &Self { x }\nfn unerase_owned(x: Self) -> Self { x }}\n"));
      Dafny.ISequence<Dafny.Rune> _113_printImpl;
      _113_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _86_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::dafny_runtime::DafnyPrint for r#")), (c).dtor_name), _85_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match self {\n"));
      _88_i = BigInteger.Zero;
      while ((_88_i) < (new BigInteger(((c).dtor_ctors).Count))) {
        DAST._IDatatypeCtor _114_ctor;
        _114_ctor = ((c).dtor_ctors).Select(_88_i);
        Dafny.ISequence<Dafny.Rune> _115_ctorMatch;
        _115_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), (_114_ctor).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" { "));
        Dafny.ISequence<Dafny.Rune> _116_modulePrefix;
        _116_modulePrefix = (((((c).dtor_enclosingModule)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(((c).dtor_enclosingModule), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _117_printRhs;
        _117_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(__fmt_print_formatter, \""), _116_modulePrefix), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), (_114_ctor).dtor_name), (((_114_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?;")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?;"))));
        BigInteger _118_j;
        _118_j = BigInteger.Zero;
        while ((_118_j) < (new BigInteger(((_114_ctor).dtor_args).Count))) {
          DAST._IFormal _119_formal;
          _119_formal = ((_114_ctor).dtor_args).Select(_118_j);
          _115_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_115_ctorMatch, (_119_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_118_j).Sign == 1) {
            _117_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_117_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \", \")?;"));
          }
          _117_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_117_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n::dafny_runtime::DafnyPrint::fmt_print(")), (_119_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", __fmt_print_formatter, false)?;"));
          _118_j = (_118_j) + (BigInteger.One);
        }
        _115_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(_115_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        if ((_114_ctor).dtor_hasAnyArgs) {
          _117_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_117_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nwrite!(__fmt_print_formatter, \")\")?;"));
        }
        _117_printRhs = Dafny.Sequence<Dafny.Rune>.Concat(_117_printRhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nOk(())"));
        _113_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_113_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _115_ctorMatch), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" => {\n")), _117_printRhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
        _88_i = (_88_i) + (BigInteger.One);
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _113_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_113_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..) => {panic!()\n}\n"));
      }
      _113_printImpl = Dafny.Sequence<Dafny.Rune>.Concat(_113_printImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      Dafny.ISequence<Dafny.Rune> _120_defaultImpl;
      _120_defaultImpl = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        _120_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), _86_constrainedTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ::std::default::Default for r#")), (c).dtor_name), _85_typeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn default() -> Self {\n")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (c).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"));
        _88_i = BigInteger.Zero;
        while ((_88_i) < (new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count))) {
          DAST._IFormal _121_formal;
          _121_formal = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_88_i);
          _120_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_120_defaultImpl, (_121_formal).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": std::default::Default::default(),\n"));
          _88_i = (_88_i) + (BigInteger.One);
        }
        _120_defaultImpl = Dafny.Sequence<Dafny.Rune>.Concat(_120_defaultImpl, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n}\n}\n"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_111_enumBody, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _112_identEraseImpls), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _113_printImpl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _120_defaultImpl);
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((new BigInteger((p).Count)).Sign == 0) {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        return s;
      } else {
        s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super::");
        BigInteger _122_i;
        _122_i = BigInteger.Zero;
        while ((_122_i) < (new BigInteger((p).Count))) {
          if ((_122_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), ((p).Select(_122_i)));
          _122_i = (_122_i) + (BigInteger.One);
        }
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool inBinding, bool inFn) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((args).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _123_i;
        _123_i = BigInteger.Zero;
        while ((_123_i) < (new BigInteger((args).Count))) {
          if ((_123_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _124_genTp;
          Dafny.ISequence<Dafny.Rune> _out40;
          _out40 = DCOMP.COMP.GenType((args).Select(_123_i), inBinding, inFn);
          _124_genTp = _out40;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _124_genTp);
          _123_i = (_123_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenType(DAST._IType c, bool inBinding, bool inFn) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      DAST._IType _source5 = c;
      if (_source5.is_Path) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _125___mcc_h0 = _source5.dtor_Path_a0;
        Dafny.ISequence<DAST._IType> _126___mcc_h1 = _source5.dtor_typeArgs;
        DAST._IResolvedType _127___mcc_h2 = _source5.dtor_resolved;
        DAST._IResolvedType _128_resolved = _127___mcc_h2;
        Dafny.ISequence<DAST._IType> _129_args = _126___mcc_h1;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _130_p = _125___mcc_h0;
        {
          Dafny.ISequence<Dafny.Rune> _out41;
          _out41 = DCOMP.COMP.GenPath(_130_p);
          s = _out41;
          Dafny.ISequence<Dafny.Rune> _131_typeArgs;
          Dafny.ISequence<Dafny.Rune> _out42;
          _out42 = DCOMP.COMP.GenTypeArgs(_129_args, inBinding, inFn);
          _131_typeArgs = _out42;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, _131_typeArgs);
          DAST._IResolvedType _source6 = _128_resolved;
          if (_source6.is_Datatype) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _132___mcc_h17 = _source6.dtor_path;
            {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            }
          } else if (_source6.is_Trait) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _133___mcc_h19 = _source6.dtor_path;
            {
              if (inBinding) {
                s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_");
              } else {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              }
            }
          } else {
            DAST._IType _134___mcc_h21 = _source6.dtor_Newtype_a0;
            DAST._IResolvedType _135_Primitive = _128_resolved;
          }
        }
      } else if (_source5.is_Nullable) {
        DAST._IType _136___mcc_h3 = _source5.dtor_Nullable_a0;
        DAST._IType _137_inner = _136___mcc_h3;
        {
          Dafny.ISequence<Dafny.Rune> _138_innerStr;
          Dafny.ISequence<Dafny.Rune> _out43;
          _out43 = DCOMP.COMP.GenType(_137_inner, inBinding, inFn);
          _138_innerStr = _out43;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::option::Option<"), _138_innerStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Tuple) {
        Dafny.ISequence<DAST._IType> _139___mcc_h4 = _source5.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IType> _140_types = _139___mcc_h4;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          BigInteger _141_i;
          _141_i = BigInteger.Zero;
          while ((_141_i) < (new BigInteger((_140_types).Count))) {
            if ((_141_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _142_generated;
            Dafny.ISequence<Dafny.Rune> _out44;
            _out44 = DCOMP.COMP.GenType((_140_types).Select(_141_i), inBinding, inFn);
            _142_generated = _out44;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _142_generated), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            _141_i = (_141_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      } else if (_source5.is_Array) {
        DAST._IType _143___mcc_h5 = _source5.dtor_element;
        DAST._IType _144_element = _143___mcc_h5;
        {
          Dafny.ISequence<Dafny.Rune> _145_elemStr;
          Dafny.ISequence<Dafny.Rune> _out45;
          _out45 = DCOMP.COMP.GenType(_144_element, inBinding, inFn);
          _145_elemStr = _out45;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc<::std::cell::RefCell<::std::vec::Vec<"), _145_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>>"));
        }
      } else if (_source5.is_Seq) {
        DAST._IType _146___mcc_h6 = _source5.dtor_element;
        DAST._IType _147_element = _146___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _148_elemStr;
          Dafny.ISequence<Dafny.Rune> _out46;
          _out46 = DCOMP.COMP.GenType(_147_element, inBinding, inFn);
          _148_elemStr = _out46;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::vec::Vec<"), _148_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Set) {
        DAST._IType _149___mcc_h7 = _source5.dtor_element;
        DAST._IType _150_element = _149___mcc_h7;
        {
          Dafny.ISequence<Dafny.Rune> _151_elemStr;
          Dafny.ISequence<Dafny.Rune> _out47;
          _out47 = DCOMP.COMP.GenType(_150_element, inBinding, inFn);
          _151_elemStr = _out47;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashSet<"), _151_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Multiset) {
        DAST._IType _152___mcc_h8 = _source5.dtor_element;
        DAST._IType _153_element = _152___mcc_h8;
        {
          Dafny.ISequence<Dafny.Rune> _154_elemStr;
          Dafny.ISequence<Dafny.Rune> _out48;
          _out48 = DCOMP.COMP.GenType(_153_element, inBinding, inFn);
          _154_elemStr = _out48;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _154_elemStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", u64>"));
        }
      } else if (_source5.is_Map) {
        DAST._IType _155___mcc_h9 = _source5.dtor_key;
        DAST._IType _156___mcc_h10 = _source5.dtor_value;
        DAST._IType _157_value = _156___mcc_h10;
        DAST._IType _158_key = _155___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _159_keyStr;
          Dafny.ISequence<Dafny.Rune> _out49;
          _out49 = DCOMP.COMP.GenType(_158_key, inBinding, inFn);
          _159_keyStr = _out49;
          Dafny.ISequence<Dafny.Rune> _160_valueStr;
          Dafny.ISequence<Dafny.Rune> _out50;
          _out50 = DCOMP.COMP.GenType(_157_value, inBinding, inFn);
          _160_valueStr = _out50;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::collections::HashMap<"), _159_keyStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _160_valueStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      } else if (_source5.is_Arrow) {
        Dafny.ISequence<DAST._IType> _161___mcc_h11 = _source5.dtor_args;
        DAST._IType _162___mcc_h12 = _source5.dtor_result;
        DAST._IType _163_result = _162___mcc_h12;
        Dafny.ISequence<DAST._IType> _164_args = _161___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(");
          BigInteger _165_i;
          _165_i = BigInteger.Zero;
          while ((_165_i) < (new BigInteger((_164_args).Count))) {
            if ((_165_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _166_generated;
            Dafny.ISequence<Dafny.Rune> _out51;
            _out51 = DCOMP.COMP.GenType((_164_args).Select(_165_i), inBinding, true);
            _166_generated = _out51;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), _166_generated);
            _165_i = (_165_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _167_resultType;
          Dafny.ISequence<Dafny.Rune> _out52;
          _out52 = DCOMP.COMP.GenType(_163_result, inBinding, (inFn) || (inBinding));
          _167_resultType = _out52;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _167_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + 'static>>"));
        }
      } else if (_source5.is_Primitive) {
        DAST._IPrimitive _168___mcc_h13 = _source5.dtor_Primitive_a0;
        DAST._IPrimitive _169_p = _168___mcc_h13;
        {
          DAST._IPrimitive _source7 = _169_p;
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
        Dafny.ISequence<Dafny.Rune> _170___mcc_h14 = _source5.dtor_Passthrough_a0;
        Dafny.ISequence<Dafny.Rune> _171_v = _170___mcc_h14;
        s = _171_v;
      } else {
        Dafny.ISequence<Dafny.Rune> _172___mcc_h15 = _source5.dtor_TypeArg_a0;
        Dafny.ISequence<Dafny.Rune> _source8 = _172___mcc_h15;
        Dafny.ISequence<Dafny.Rune> _173___mcc_h16 = _source8;
        Dafny.ISequence<Dafny.Rune> _174_name = _173___mcc_h16;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _174_name);
      }
      return s;
    }
    public static void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams, out Dafny.ISequence<Dafny.Rune> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> traitBodies) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _175_i;
      _175_i = BigInteger.Zero;
      while ((_175_i) < (new BigInteger((body).Count))) {
        DAST._IMethod _source9 = (body).Select(_175_i);
        DAST._IMethod _176___mcc_h0 = _source9;
        DAST._IMethod _177_m = _176___mcc_h0;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source10 = (_177_m).dtor_overridingPath;
          if (_source10.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _178___mcc_h1 = _source10.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _179_p = _178___mcc_h1;
            {
              Dafny.ISequence<Dafny.Rune> _180_existing;
              _180_existing = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              if ((traitBodies).Contains(_179_p)) {
                _180_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Select(traitBodies, _179_p);
              }
              if ((new BigInteger((_180_existing).Count)).Sign == 1) {
                _180_existing = Dafny.Sequence<Dafny.Rune>.Concat(_180_existing, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
              }
              Dafny.ISequence<Dafny.Rune> _181_genMethod;
              Dafny.ISequence<Dafny.Rune> _out53;
              _out53 = DCOMP.COMP.GenMethod(_177_m, true, enclosingType, enclosingTypeParams);
              _181_genMethod = _out53;
              _180_existing = Dafny.Sequence<Dafny.Rune>.Concat(_180_existing, _181_genMethod);
              traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>(_179_p, _180_existing)));
            }
          } else {
            {
              Dafny.ISequence<Dafny.Rune> _182_generated;
              Dafny.ISequence<Dafny.Rune> _out54;
              _out54 = DCOMP.COMP.GenMethod(_177_m, forTrait, enclosingType, enclosingTypeParams);
              _182_generated = _out54;
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, _182_generated);
            }
          }
        }
        if ((new BigInteger((s).Count)).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        _175_i = (_175_i) + (BigInteger.One);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GenParams(Dafny.ISequence<DAST._IFormal> @params) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      BigInteger _183_i;
      _183_i = BigInteger.Zero;
      while ((_183_i) < (new BigInteger((@params).Count))) {
        DAST._IFormal _184_param;
        _184_param = (@params).Select(_183_i);
        Dafny.ISequence<Dafny.Rune> _185_paramType;
        Dafny.ISequence<Dafny.Rune> _out55;
        _out55 = DCOMP.COMP.GenType((_184_param).dtor_typ, false, false);
        _185_paramType = _out55;
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_184_param).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _185_paramType);
        if ((_183_i) < ((new BigInteger((@params).Count)) - (BigInteger.One))) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        _183_i = (_183_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISet<DAST._IType> enclosingTypeParams) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      Dafny.ISequence<Dafny.Rune> _186_params;
      Dafny.ISequence<Dafny.Rune> _out56;
      _out56 = DCOMP.COMP.GenParams((m).dtor_params);
      _186_params = _out56;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _187_paramNames;
      _187_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _188_paramI;
      _188_paramI = BigInteger.Zero;
      while ((_188_paramI) < (new BigInteger(((m).dtor_params).Count))) {
        _187_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_187_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((m).dtor_params).Select(_188_paramI)).dtor_name));
        _188_paramI = (_188_paramI) + (BigInteger.One);
      }
      if (!((m).dtor_isStatic)) {
        if (forTrait) {
          _186_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _186_params);
        } else {
          Dafny.ISequence<Dafny.Rune> _189_enclosingTypeString;
          Dafny.ISequence<Dafny.Rune> _out57;
          _out57 = DCOMP.COMP.GenType(enclosingType, false, false);
          _189_enclosingTypeString = _out57;
          _186_params = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self: &"), _189_enclosingTypeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _186_params);
        }
      }
      Dafny.ISequence<Dafny.Rune> _190_retType;
      _190_retType = (((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      BigInteger _191_typeI;
      _191_typeI = BigInteger.Zero;
      while ((_191_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        if ((_191_typeI).Sign == 1) {
          _190_retType = Dafny.Sequence<Dafny.Rune>.Concat(_190_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
        }
        Dafny.ISequence<Dafny.Rune> _192_typeString;
        Dafny.ISequence<Dafny.Rune> _out58;
        _out58 = DCOMP.COMP.GenType(((m).dtor_outTypes).Select(_191_typeI), false, false);
        _192_typeString = _out58;
        _190_retType = Dafny.Sequence<Dafny.Rune>.Concat(_190_retType, _192_typeString);
        _191_typeI = (_191_typeI) + (BigInteger.One);
      }
      if ((new BigInteger(((m).dtor_outTypes).Count)) != (BigInteger.One)) {
        _190_retType = Dafny.Sequence<Dafny.Rune>.Concat(_190_retType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
      if (forTrait) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn r#"), (m).dtor_name);
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub fn r#"), (m).dtor_name);
      }
      Dafny.ISequence<DAST._IType> _193_typeParamsFiltered;
      _193_typeParamsFiltered = Dafny.Sequence<DAST._IType>.FromElements();
      BigInteger _194_typeParamI;
      _194_typeParamI = BigInteger.Zero;
      while ((_194_typeParamI) < (new BigInteger(((m).dtor_typeParams).Count))) {
        DAST._IType _195_typeParam;
        _195_typeParam = ((m).dtor_typeParams).Select(_194_typeParamI);
        if (!((enclosingTypeParams).Contains(_195_typeParam))) {
          _193_typeParamsFiltered = Dafny.Sequence<DAST._IType>.Concat(_193_typeParamsFiltered, Dafny.Sequence<DAST._IType>.FromElements(_195_typeParam));
        }
        _194_typeParamI = (_194_typeParamI) + (BigInteger.One);
      }
      if ((new BigInteger((_193_typeParamsFiltered).Count)).Sign == 1) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"));
        BigInteger _196_i;
        _196_i = BigInteger.Zero;
        while ((_196_i) < (new BigInteger((_193_typeParamsFiltered).Count))) {
          if ((_196_i).Sign == 1) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          }
          Dafny.ISequence<Dafny.Rune> _197_typeString;
          Dafny.ISequence<Dafny.Rune> _out59;
          _out59 = DCOMP.COMP.GenType((_193_typeParamsFiltered).Select(_196_i), false, false);
          _197_typeString = _out59;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _197_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<")), _197_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("> + Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static"));
          _196_i = (_196_i) + (BigInteger.One);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _186_params), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _190_retType);
      if ((m).dtor_hasBody) {
        Dafny.ISequence<Dafny.Rune> _198_earlyReturn;
        _198_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return;");
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source11 = (m).dtor_outVars;
        if (_source11.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _199___mcc_h0 = _source11.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _200_outVars = _199___mcc_h0;
          {
            _198_earlyReturn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return (");
            BigInteger _201_outI;
            _201_outI = BigInteger.Zero;
            while ((_201_outI) < (new BigInteger((_200_outVars).Count))) {
              if ((_201_outI).Sign == 1) {
                _198_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_198_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _202_outVar;
              _202_outVar = (_200_outVars).Select(_201_outI);
              _198_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_198_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_202_outVar));
              _201_outI = (_201_outI) + (BigInteger.One);
            }
            _198_earlyReturn = Dafny.Sequence<Dafny.Rune>.Concat(_198_earlyReturn, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
          }
        } else {
        }
        Dafny.ISequence<Dafny.Rune> _203_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _204___v12;
        Dafny.ISequence<Dafny.Rune> _out60;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out61;
        DCOMP.COMP.GenStmts((m).dtor_body, (((m).dtor_isStatic) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None()) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))), _187_paramNames, true, _198_earlyReturn, out _out60, out _out61);
        _203_body = _out60;
        _204___v12 = _out61;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source12 = (m).dtor_outVars;
        if (_source12.is_Some) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _205___mcc_h1 = _source12.dtor_Some_a0;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _206_outVars = _205___mcc_h1;
          {
            _203_body = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_203_body, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _198_earlyReturn);
          }
        } else {
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _203_body), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}\n"));
      } else {
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
      }
      return s;
    }
    public static void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, Dafny.ISequence<Dafny.Rune> earlyReturn, out Dafny.ISequence<Dafny.Rune> generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _207_declarations;
      _207_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _208_i;
      _208_i = BigInteger.Zero;
      while ((_208_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _209_stmt;
        _209_stmt = (stmts).Select(_208_i);
        Dafny.ISequence<Dafny.Rune> _210_stmtString;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _211_recIdents;
        Dafny.ISequence<Dafny.Rune> _out62;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
        DCOMP.COMP.GenStmt(_209_stmt, selfIdent, @params, (isLast) && ((_208_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out62, out _out63);
        _210_stmtString = _out62;
        _211_recIdents = _out63;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_211_recIdents, _207_declarations));
        DAST._IStatement _source13 = _209_stmt;
        if (_source13.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _212___mcc_h0 = _source13.dtor_name;
          DAST._IType _213___mcc_h1 = _source13.dtor_typ;
          DAST._IOptional<DAST._IExpression> _214___mcc_h2 = _source13.dtor_maybeValue;
          Dafny.ISequence<Dafny.Rune> _215_name = _212___mcc_h0;
          {
            _207_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_207_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_215_name));
          }
        } else if (_source13.is_Assign) {
          DAST._IAssignLhs _216___mcc_h6 = _source13.dtor_lhs;
          DAST._IExpression _217___mcc_h7 = _source13.dtor_value;
        } else if (_source13.is_If) {
          DAST._IExpression _218___mcc_h10 = _source13.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _219___mcc_h11 = _source13.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _220___mcc_h12 = _source13.dtor_els;
        } else if (_source13.is_While) {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _221___mcc_h16 = _source13.dtor_lbl;
          DAST._IExpression _222___mcc_h17 = _source13.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _223___mcc_h18 = _source13.dtor_body;
        } else if (_source13.is_Call) {
          DAST._IExpression _224___mcc_h22 = _source13.dtor_on;
          Dafny.ISequence<Dafny.Rune> _225___mcc_h23 = _source13.dtor_name;
          Dafny.ISequence<DAST._IType> _226___mcc_h24 = _source13.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _227___mcc_h25 = _source13.dtor_args;
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _228___mcc_h26 = _source13.dtor_outs;
        } else if (_source13.is_Return) {
          DAST._IExpression _229___mcc_h32 = _source13.dtor_expr;
        } else if (_source13.is_EarlyReturn) {
        } else if (_source13.is_Break) {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _230___mcc_h34 = _source13.dtor_toLabel;
        } else if (_source13.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _231___mcc_h36 = _source13.dtor_body;
        } else if (_source13.is_JumpTailCallStart) {
        } else if (_source13.is_Halt) {
        } else {
          DAST._IExpression _232___mcc_h38 = _source13.dtor_Print_a0;
        }
        if ((_208_i).Sign == 1) {
          generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, _210_stmtString);
        _208_i = (_208_i) + (BigInteger.One);
      }
    }
    public static void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.Rune> rhs, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source14 = lhs;
      if (_source14.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _233___mcc_h0 = _source14.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source15 = _233___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _234___mcc_h1 = _source15;
        Dafny.ISequence<Dafny.Rune> _235_id = _234___mcc_h1;
        {
          if ((@params).Contains(_235_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*r#"), _235_id);
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _235_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_235_id);
          needsIIFE = false;
        }
      } else if (_source14.is_Select) {
        DAST._IExpression _236___mcc_h2 = _source14.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _237___mcc_h3 = _source14.dtor_field;
        Dafny.ISequence<Dafny.Rune> _238_field = _237___mcc_h3;
        DAST._IExpression _239_on = _236___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _240_onExpr;
          bool _241_onOwned;
          bool _242_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _243_recIdents;
          Dafny.ISequence<Dafny.Rune> _out64;
          bool _out65;
          bool _out66;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out67;
          DCOMP.COMP.GenExpr(_239_on, selfIdent, @params, false, out _out64, out _out65, out _out66, out _out67);
          _240_onExpr = _out64;
          _241_onOwned = _out65;
          _242_onErased = _out66;
          _243_recIdents = _out67;
          if (!(_242_onErased)) {
            Dafny.ISequence<Dafny.Rune> _244_eraseFn;
            _244_eraseFn = ((_241_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _240_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _244_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _240_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), _240_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _238_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          readIdents = _243_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _245___mcc_h4 = _source14.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _246___mcc_h5 = _source14.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _247_indices = _246___mcc_h5;
        DAST._IExpression _248_on = _245___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _249_onExpr;
          bool _250_onOwned;
          bool _251_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _252_recIdents;
          Dafny.ISequence<Dafny.Rune> _out68;
          bool _out69;
          bool _out70;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out71;
          DCOMP.COMP.GenExpr(_248_on, selfIdent, @params, false, out _out68, out _out69, out _out70, out _out71);
          _249_onExpr = _out68;
          _250_onOwned = _out69;
          _251_onErased = _out70;
          _252_recIdents = _out71;
          readIdents = _252_recIdents;
          if (!(_251_onErased)) {
            Dafny.ISequence<Dafny.Rune> _253_eraseFn;
            _253_eraseFn = ((_250_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _249_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _253_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _249_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          BigInteger _254_i;
          _254_i = BigInteger.Zero;
          while ((_254_i) < (new BigInteger((_247_indices).Count))) {
            Dafny.ISequence<Dafny.Rune> _255_idx;
            bool _256___v16;
            bool _257_idxErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _258_recIdentsIdx;
            Dafny.ISequence<Dafny.Rune> _out72;
            bool _out73;
            bool _out74;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out75;
            DCOMP.COMP.GenExpr((_247_indices).Select(_254_i), selfIdent, @params, true, out _out72, out _out73, out _out74, out _out75);
            _255_idx = _out72;
            _256___v16 = _out73;
            _257_idxErased = _out74;
            _258_recIdentsIdx = _out75;
            if (!(_257_idxErased)) {
              _255_idx = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _255_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let __idx")), DCOMP.__default.natToString(_254_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = <usize as ::dafny_runtime::NumCast>::from(")), _255_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _258_recIdentsIdx);
            _254_i = (_254_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, _249_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()"));
          _254_i = BigInteger.Zero;
          while ((_254_i) < (new BigInteger((_247_indices).Count))) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[__idx")), DCOMP.__default.natToString(_254_i)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
            _254_i = (_254_i) + (BigInteger.One);
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}"));
          needsIIFE = true;
        }
      }
    }
    public static void GenStmt(DAST._IStatement stmt, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, Dafny.ISequence<Dafny.Rune> earlyReturn, out Dafny.ISequence<Dafny.Rune> generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IStatement _source16 = stmt;
      if (_source16.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _259___mcc_h0 = _source16.dtor_name;
        DAST._IType _260___mcc_h1 = _source16.dtor_typ;
        DAST._IOptional<DAST._IExpression> _261___mcc_h2 = _source16.dtor_maybeValue;
        DAST._IOptional<DAST._IExpression> _source17 = _261___mcc_h2;
        if (_source17.is_Some) {
          DAST._IExpression _262___mcc_h3 = _source17.dtor_Some_a0;
          DAST._IExpression _263_expression = _262___mcc_h3;
          DAST._IType _264_typ = _260___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _265_name = _259___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _266_expr;
            bool _267___v17;
            bool _268_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _269_recIdents;
            Dafny.ISequence<Dafny.Rune> _out76;
            bool _out77;
            bool _out78;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out79;
            DCOMP.COMP.GenExpr(_263_expression, selfIdent, @params, true, out _out76, out _out77, out _out78, out _out79);
            _266_expr = _out76;
            _267___v17 = _out77;
            _268_recErased = _out78;
            _269_recIdents = _out79;
            if (_268_recErased) {
              _266_expr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _266_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            Dafny.ISequence<Dafny.Rune> _270_typeString;
            Dafny.ISequence<Dafny.Rune> _out80;
            _out80 = DCOMP.COMP.GenType(_264_typ, true, false);
            _270_typeString = _out80;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _265_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _270_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _266_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = _269_recIdents;
          }
        } else {
          DAST._IType _271_typ = _260___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _272_name = _259___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _273_typeString;
            Dafny.ISequence<Dafny.Rune> _out81;
            _out81 = DCOMP.COMP.GenType(_271_typ, true, false);
            _273_typeString = _out81;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _272_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _273_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source16.is_Assign) {
        DAST._IAssignLhs _274___mcc_h4 = _source16.dtor_lhs;
        DAST._IExpression _275___mcc_h5 = _source16.dtor_value;
        DAST._IExpression _276_expression = _275___mcc_h5;
        DAST._IAssignLhs _277_lhs = _274___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _278_lhsGen;
          bool _279_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _280_recIdents;
          Dafny.ISequence<Dafny.Rune> _out82;
          bool _out83;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out84;
          DCOMP.COMP.GenAssignLhs(_277_lhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), selfIdent, @params, out _out82, out _out83, out _out84);
          _278_lhsGen = _out82;
          _279_needsIIFE = _out83;
          _280_recIdents = _out84;
          Dafny.ISequence<Dafny.Rune> _281_exprGen;
          bool _282___v18;
          bool _283_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _284_exprIdents;
          Dafny.ISequence<Dafny.Rune> _out85;
          bool _out86;
          bool _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          DCOMP.COMP.GenExpr(_276_expression, selfIdent, @params, true, out _out85, out _out86, out _out87, out _out88);
          _281_exprGen = _out85;
          _282___v18 = _out86;
          _283_exprErased = _out87;
          _284_exprIdents = _out88;
          if (_283_exprErased) {
            _281_exprGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _281_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (_279_needsIIFE) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet __rhs = "), _281_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _278_lhsGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_278_lhsGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _281_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_280_recIdents, _284_exprIdents);
        }
      } else if (_source16.is_If) {
        DAST._IExpression _285___mcc_h6 = _source16.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _286___mcc_h7 = _source16.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _287___mcc_h8 = _source16.dtor_els;
        Dafny.ISequence<DAST._IStatement> _288_els = _287___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _289_thn = _286___mcc_h7;
        DAST._IExpression _290_cond = _285___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _291_condString;
          bool _292___v19;
          bool _293_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _294_recIdents;
          Dafny.ISequence<Dafny.Rune> _out89;
          bool _out90;
          bool _out91;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out92;
          DCOMP.COMP.GenExpr(_290_cond, selfIdent, @params, true, out _out89, out _out90, out _out91, out _out92);
          _291_condString = _out89;
          _292___v19 = _out90;
          _293_condErased = _out91;
          _294_recIdents = _out92;
          if (!(_293_condErased)) {
            _291_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _291_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _294_recIdents;
          Dafny.ISequence<Dafny.Rune> _295_thnString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _296_thnIdents;
          Dafny.ISequence<Dafny.Rune> _out93;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out94;
          DCOMP.COMP.GenStmts(_289_thn, selfIdent, @params, isLast, earlyReturn, out _out93, out _out94);
          _295_thnString = _out93;
          _296_thnIdents = _out94;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _296_thnIdents);
          Dafny.ISequence<Dafny.Rune> _297_elsString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _298_elsIdents;
          Dafny.ISequence<Dafny.Rune> _out95;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
          DCOMP.COMP.GenStmts(_288_els, selfIdent, @params, isLast, earlyReturn, out _out95, out _out96);
          _297_elsString = _out95;
          _298_elsIdents = _out96;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _298_elsIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), _291_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _295_thnString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _297_elsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source16.is_While) {
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _299___mcc_h9 = _source16.dtor_lbl;
        DAST._IExpression _300___mcc_h10 = _source16.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _301___mcc_h11 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _302_body = _301___mcc_h11;
        DAST._IExpression _303_cond = _300___mcc_h10;
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _304_lbl = _299___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _305_condString;
          bool _306___v20;
          bool _307_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _308_recIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          bool _out98;
          bool _out99;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
          DCOMP.COMP.GenExpr(_303_cond, selfIdent, @params, true, out _out97, out _out98, out _out99, out _out100);
          _305_condString = _out97;
          _306___v20 = _out98;
          _307_condErased = _out99;
          _308_recIdents = _out100;
          if (!(_307_condErased)) {
            _305_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase("), _305_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _308_recIdents;
          Dafny.ISequence<Dafny.Rune> _309_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _310_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          DCOMP.COMP.GenStmts(_302_body, selfIdent, @params, false, earlyReturn, out _out101, out _out102);
          _309_bodyString = _out101;
          _310_bodyIdents = _out102;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _310_bodyIdents);
          Dafny.ISequence<Dafny.Rune> _311_lblString;
          _311_lblString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source18 = _304_lbl;
          if (_source18.is_Some) {
            Dafny.ISequence<Dafny.Rune> _312___mcc_h21 = _source18.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _313_id = _312___mcc_h21;
            {
              _311_lblString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'label_"), _313_id), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "));
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_311_lblString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while ")), _305_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _309_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source16.is_Call) {
        DAST._IExpression _314___mcc_h12 = _source16.dtor_on;
        Dafny.ISequence<Dafny.Rune> _315___mcc_h13 = _source16.dtor_name;
        Dafny.ISequence<DAST._IType> _316___mcc_h14 = _source16.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _317___mcc_h15 = _source16.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _318___mcc_h16 = _source16.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _319_maybeOutVars = _318___mcc_h16;
        Dafny.ISequence<DAST._IExpression> _320_args = _317___mcc_h15;
        Dafny.ISequence<DAST._IType> _321_typeArgs = _316___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _322_name = _315___mcc_h13;
        DAST._IExpression _323_on = _314___mcc_h12;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _324_typeArgString;
          _324_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_321_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _325_typeI;
            _325_typeI = BigInteger.Zero;
            _324_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_325_typeI) < (new BigInteger((_321_typeArgs).Count))) {
              if ((_325_typeI).Sign == 1) {
                _324_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_324_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _326_typeString;
              Dafny.ISequence<Dafny.Rune> _out103;
              _out103 = DCOMP.COMP.GenType((_321_typeArgs).Select(_325_typeI), false, false);
              _326_typeString = _out103;
              _324_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_324_typeArgString, _326_typeString);
              _325_typeI = (_325_typeI) + (BigInteger.One);
            }
            _324_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_324_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _327_argString;
          _327_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _328_i;
          _328_i = BigInteger.Zero;
          while ((_328_i) < (new BigInteger((_320_args).Count))) {
            if ((_328_i).Sign == 1) {
              _327_argString = Dafny.Sequence<Dafny.Rune>.Concat(_327_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _329_argExpr;
            bool _330_isOwned;
            bool _331_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _332_argIdents;
            Dafny.ISequence<Dafny.Rune> _out104;
            bool _out105;
            bool _out106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
            DCOMP.COMP.GenExpr((_320_args).Select(_328_i), selfIdent, @params, false, out _out104, out _out105, out _out106, out _out107);
            _329_argExpr = _out104;
            _330_isOwned = _out105;
            _331_argErased = _out106;
            _332_argIdents = _out107;
            if (_330_isOwned) {
              _329_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _329_argExpr);
            }
            _327_argString = Dafny.Sequence<Dafny.Rune>.Concat(_327_argString, _329_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _332_argIdents);
            _328_i = (_328_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _333_enclosingString;
          bool _334___v21;
          bool _335___v22;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _336_enclosingIdents;
          Dafny.ISequence<Dafny.Rune> _out108;
          bool _out109;
          bool _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          DCOMP.COMP.GenExpr(_323_on, selfIdent, @params, false, out _out108, out _out109, out _out110, out _out111);
          _333_enclosingString = _out108;
          _334___v21 = _out109;
          _335___v22 = _out110;
          _336_enclosingIdents = _out111;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _336_enclosingIdents);
          DAST._IExpression _source19 = _323_on;
          if (_source19.is_Literal) {
            DAST._ILiteral _337___mcc_h22 = _source19.dtor_Literal_a0;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _338___mcc_h24 = _source19.dtor_Ident_a0;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _339___mcc_h26 = _source19.dtor_Companion_a0;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_333_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source19.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _340___mcc_h28 = _source19.dtor_Tuple_a0;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _341___mcc_h30 = _source19.dtor_path;
            Dafny.ISequence<DAST._IExpression> _342___mcc_h31 = _source19.dtor_args;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _343___mcc_h34 = _source19.dtor_dims;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _344___mcc_h36 = _source19.dtor_path;
            Dafny.ISequence<Dafny.Rune> _345___mcc_h37 = _source19.dtor_variant;
            bool _346___mcc_h38 = _source19.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _347___mcc_h39 = _source19.dtor_contents;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Convert) {
            DAST._IExpression _348___mcc_h44 = _source19.dtor_value;
            DAST._IType _349___mcc_h45 = _source19.dtor_from;
            DAST._IType _350___mcc_h46 = _source19.dtor_typ;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _351___mcc_h50 = _source19.dtor_elements;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _352___mcc_h52 = _source19.dtor_elements;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_This) {
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Ite) {
            DAST._IExpression _353___mcc_h54 = _source19.dtor_cond;
            DAST._IExpression _354___mcc_h55 = _source19.dtor_thn;
            DAST._IExpression _355___mcc_h56 = _source19.dtor_els;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_UnOp) {
            DAST._IUnaryOp _356___mcc_h60 = _source19.dtor_unOp;
            DAST._IExpression _357___mcc_h61 = _source19.dtor_expr;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _358___mcc_h64 = _source19.dtor_op;
            DAST._IExpression _359___mcc_h65 = _source19.dtor_left;
            DAST._IExpression _360___mcc_h66 = _source19.dtor_right;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_ArrayLen) {
            DAST._IExpression _361___mcc_h70 = _source19.dtor_expr;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Select) {
            DAST._IExpression _362___mcc_h72 = _source19.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _363___mcc_h73 = _source19.dtor_field;
            bool _364___mcc_h74 = _source19.dtor_isConstant;
            bool _365___mcc_h75 = _source19.dtor_onDatatype;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_SelectFn) {
            DAST._IExpression _366___mcc_h80 = _source19.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _367___mcc_h81 = _source19.dtor_field;
            bool _368___mcc_h82 = _source19.dtor_onDatatype;
            bool _369___mcc_h83 = _source19.dtor_isStatic;
            BigInteger _370___mcc_h84 = _source19.dtor_arity;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Index) {
            DAST._IExpression _371___mcc_h90 = _source19.dtor_expr;
            bool _372___mcc_h91 = _source19.dtor_isArray;
            Dafny.ISequence<DAST._IExpression> _373___mcc_h92 = _source19.dtor_indices;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_IndexRange) {
            DAST._IExpression _374___mcc_h96 = _source19.dtor_expr;
            bool _375___mcc_h97 = _source19.dtor_isArray;
            DAST._IOptional<DAST._IExpression> _376___mcc_h98 = _source19.dtor_low;
            DAST._IOptional<DAST._IExpression> _377___mcc_h99 = _source19.dtor_high;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_TupleSelect) {
            DAST._IExpression _378___mcc_h104 = _source19.dtor_expr;
            BigInteger _379___mcc_h105 = _source19.dtor_index;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Call) {
            DAST._IExpression _380___mcc_h108 = _source19.dtor_on;
            Dafny.ISequence<Dafny.Rune> _381___mcc_h109 = _source19.dtor_name;
            Dafny.ISequence<DAST._IType> _382___mcc_h110 = _source19.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _383___mcc_h111 = _source19.dtor_args;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _384___mcc_h116 = _source19.dtor_params;
            DAST._IType _385___mcc_h117 = _source19.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _386___mcc_h118 = _source19.dtor_body;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _387___mcc_h122 = _source19.dtor_values;
            DAST._IType _388___mcc_h123 = _source19.dtor_retType;
            DAST._IExpression _389___mcc_h124 = _source19.dtor_expr;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _390___mcc_h128 = _source19.dtor_name;
            DAST._IType _391___mcc_h129 = _source19.dtor_typ;
            DAST._IExpression _392___mcc_h130 = _source19.dtor_value;
            DAST._IExpression _393___mcc_h131 = _source19.dtor_iifeBody;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Apply) {
            DAST._IExpression _394___mcc_h136 = _source19.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _395___mcc_h137 = _source19.dtor_args;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_TypeTest) {
            DAST._IExpression _396___mcc_h140 = _source19.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _397___mcc_h141 = _source19.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _398___mcc_h142 = _source19.dtor_variant;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _399___mcc_h146 = _source19.dtor_typ;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _400_receiver;
          _400_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source20 = _319_maybeOutVars;
          if (_source20.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _401___mcc_h148 = _source20.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _402_outVars = _401___mcc_h148;
            {
              if ((new BigInteger((_402_outVars).Count)) > (BigInteger.One)) {
                _400_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _403_outI;
              _403_outI = BigInteger.Zero;
              while ((_403_outI) < (new BigInteger((_402_outVars).Count))) {
                if ((_403_outI).Sign == 1) {
                  _400_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_400_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _404_outVar;
                _404_outVar = (_402_outVars).Select(_403_outI);
                _400_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_400_receiver, (_404_outVar));
                _403_outI = (_403_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_402_outVars).Count)) > (BigInteger.One)) {
                _400_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_400_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_400_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_400_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _322_name), _324_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _327_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source16.is_Return) {
        DAST._IExpression _405___mcc_h17 = _source16.dtor_expr;
        DAST._IExpression _406_expr = _405___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _407_exprString;
          bool _408___v25;
          bool _409_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _410_recIdents;
          Dafny.ISequence<Dafny.Rune> _out112;
          bool _out113;
          bool _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          DCOMP.COMP.GenExpr(_406_expr, selfIdent, @params, true, out _out112, out _out113, out _out114, out _out115);
          _407_exprString = _out112;
          _408___v25 = _out113;
          _409_recErased = _out114;
          _410_recIdents = _out115;
          _407_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _407_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _410_recIdents;
          if (isLast) {
            generated = _407_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _407_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source16.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_Break) {
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _411___mcc_h18 = _source16.dtor_toLabel;
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _412_toLabel = _411___mcc_h18;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source21 = _412_toLabel;
          if (_source21.is_Some) {
            Dafny.ISequence<Dafny.Rune> _413___mcc_h149 = _source21.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _414_lbl = _413___mcc_h149;
            {
              generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break 'label_"), _414_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          } else {
            {
              generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _415___mcc_h19 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _416_body = _415___mcc_h19;
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if (!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#_this = self.clone();\n"));
          }
          BigInteger _417_paramI;
          _417_paramI = BigInteger.Zero;
          while ((_417_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _418_param;
            _418_param = (@params).Select(_417_paramI);
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#")), _418_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _418_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
            _417_paramI = (_417_paramI) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _419_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _420_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
          DCOMP.COMP.GenStmts(_416_body, ((!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out116, out _out117);
          _419_bodyString = _out116;
          _420_bodyIdents = _out117;
          readIdents = _420_bodyIdents;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'TAIL_CALL_START: loop {\n")), _419_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source16.is_JumpTailCallStart) {
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue 'TAIL_CALL_START;");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_Halt) {
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else {
        DAST._IExpression _421___mcc_h20 = _source16.dtor_Print_a0;
        DAST._IExpression _422_e = _421___mcc_h20;
        {
          Dafny.ISequence<Dafny.Rune> _423_printedExpr;
          bool _424_isOwned;
          bool _425___v26;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _426_recIdents;
          Dafny.ISequence<Dafny.Rune> _out118;
          bool _out119;
          bool _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          DCOMP.COMP.GenExpr(_422_e, selfIdent, @params, false, out _out118, out _out119, out _out120, out _out121);
          _423_printedExpr = _out118;
          _424_isOwned = _out119;
          _425___v26 = _out120;
          _426_recIdents = _out121;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_424_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _423_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _426_recIdents;
        }
      }
    }
    public static void GenExpr(DAST._IExpression e, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool mustOwn, out Dafny.ISequence<Dafny.Rune> s, out bool isOwned, out bool isErased, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      isOwned = false;
      isErased = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source22 = e;
      if (_source22.is_Literal) {
        DAST._ILiteral _427___mcc_h0 = _source22.dtor_Literal_a0;
        DAST._ILiteral _source23 = _427___mcc_h0;
        if (_source23.is_BoolLiteral) {
          bool _428___mcc_h1 = _source23.dtor_BoolLiteral_a0;
          if ((_428___mcc_h1) == (false)) {
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
        } else if (_source23.is_IntLiteral) {
          Dafny.ISequence<Dafny.Rune> _429___mcc_h2 = _source23.dtor_IntLiteral_a0;
          DAST._IType _430___mcc_h3 = _source23.dtor_IntLiteral_a1;
          DAST._IType _431_t = _430___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _432_i = _429___mcc_h2;
          {
            DAST._IType _source24 = _431_t;
            if (_source24.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _433___mcc_h197 = _source24.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _434___mcc_h198 = _source24.dtor_typeArgs;
              DAST._IResolvedType _435___mcc_h199 = _source24.dtor_resolved;
              {
                s = _432_i;
              }
            } else if (_source24.is_Nullable) {
              DAST._IType _436___mcc_h203 = _source24.dtor_Nullable_a0;
              {
                s = _432_i;
              }
            } else if (_source24.is_Tuple) {
              Dafny.ISequence<DAST._IType> _437___mcc_h205 = _source24.dtor_Tuple_a0;
              {
                s = _432_i;
              }
            } else if (_source24.is_Array) {
              DAST._IType _438___mcc_h207 = _source24.dtor_element;
              {
                s = _432_i;
              }
            } else if (_source24.is_Seq) {
              DAST._IType _439___mcc_h209 = _source24.dtor_element;
              {
                s = _432_i;
              }
            } else if (_source24.is_Set) {
              DAST._IType _440___mcc_h211 = _source24.dtor_element;
              {
                s = _432_i;
              }
            } else if (_source24.is_Multiset) {
              DAST._IType _441___mcc_h213 = _source24.dtor_element;
              {
                s = _432_i;
              }
            } else if (_source24.is_Map) {
              DAST._IType _442___mcc_h215 = _source24.dtor_key;
              DAST._IType _443___mcc_h216 = _source24.dtor_value;
              {
                s = _432_i;
              }
            } else if (_source24.is_Arrow) {
              Dafny.ISequence<DAST._IType> _444___mcc_h219 = _source24.dtor_args;
              DAST._IType _445___mcc_h220 = _source24.dtor_result;
              {
                s = _432_i;
              }
            } else if (_source24.is_Primitive) {
              DAST._IPrimitive _446___mcc_h223 = _source24.dtor_Primitive_a0;
              DAST._IPrimitive _source25 = _446___mcc_h223;
              if (_source25.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _432_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source25.is_Real) {
                {
                  s = _432_i;
                }
              } else if (_source25.is_String) {
                {
                  s = _432_i;
                }
              } else if (_source25.is_Bool) {
                {
                  s = _432_i;
                }
              } else {
                {
                  s = _432_i;
                }
              }
            } else if (_source24.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _447___mcc_h225 = _source24.dtor_Passthrough_a0;
              {
                s = _432_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _448___mcc_h227 = _source24.dtor_TypeArg_a0;
              {
                s = _432_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _449___mcc_h4 = _source23.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _450___mcc_h5 = _source23.dtor_DecLiteral_a1;
          DAST._IType _451___mcc_h6 = _source23.dtor_DecLiteral_a2;
          DAST._IType _452_t = _451___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _453_d = _450___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _454_n = _449___mcc_h4;
          {
            DAST._IType _source26 = _452_t;
            if (_source26.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _455___mcc_h229 = _source26.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _456___mcc_h230 = _source26.dtor_typeArgs;
              DAST._IResolvedType _457___mcc_h231 = _source26.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Nullable) {
              DAST._IType _458___mcc_h235 = _source26.dtor_Nullable_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Tuple) {
              Dafny.ISequence<DAST._IType> _459___mcc_h237 = _source26.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Array) {
              DAST._IType _460___mcc_h239 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Seq) {
              DAST._IType _461___mcc_h241 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Set) {
              DAST._IType _462___mcc_h243 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Multiset) {
              DAST._IType _463___mcc_h245 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Map) {
              DAST._IType _464___mcc_h247 = _source26.dtor_key;
              DAST._IType _465___mcc_h248 = _source26.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Arrow) {
              Dafny.ISequence<DAST._IType> _466___mcc_h251 = _source26.dtor_args;
              DAST._IType _467___mcc_h252 = _source26.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Primitive) {
              DAST._IPrimitive _468___mcc_h255 = _source26.dtor_Primitive_a0;
              DAST._IPrimitive _source27 = _468___mcc_h255;
              if (_source27.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source27.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _454_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source27.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source27.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source26.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _469___mcc_h257 = _source26.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _470___mcc_h259 = _source26.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_454_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _453_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _471___mcc_h7 = _source23.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _472_l = _471___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _472_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_CharLiteral) {
          Dafny.Rune _473___mcc_h8 = _source23.dtor_CharLiteral_a0;
          Dafny.Rune _474_c = _473___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_474_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
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
      } else if (_source22.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _475___mcc_h9 = _source22.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _476_name = _475___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _476_name);
          if (!((@params).Contains(_476_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_476_name);
        }
      } else if (_source22.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _477___mcc_h10 = _source22.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _478_path = _477___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out122;
          _out122 = DCOMP.COMP.GenPath(_478_path);
          s = _out122;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source22.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _479___mcc_h11 = _source22.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _480_values = _479___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _481_i;
          _481_i = BigInteger.Zero;
          bool _482_allErased;
          _482_allErased = true;
          while ((_481_i) < (new BigInteger((_480_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _483___v29;
            bool _484___v30;
            bool _485_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _486___v31;
            Dafny.ISequence<Dafny.Rune> _out123;
            bool _out124;
            bool _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            DCOMP.COMP.GenExpr((_480_values).Select(_481_i), selfIdent, @params, true, out _out123, out _out124, out _out125, out _out126);
            _483___v29 = _out123;
            _484___v30 = _out124;
            _485_isErased = _out125;
            _486___v31 = _out126;
            _482_allErased = (_482_allErased) && (_485_isErased);
            _481_i = (_481_i) + (BigInteger.One);
          }
          _481_i = BigInteger.Zero;
          while ((_481_i) < (new BigInteger((_480_values).Count))) {
            if ((_481_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _487_recursiveGen;
            bool _488___v32;
            bool _489_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _490_recIdents;
            Dafny.ISequence<Dafny.Rune> _out127;
            bool _out128;
            bool _out129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
            DCOMP.COMP.GenExpr((_480_values).Select(_481_i), selfIdent, @params, true, out _out127, out _out128, out _out129, out _out130);
            _487_recursiveGen = _out127;
            _488___v32 = _out128;
            _489_isErased = _out129;
            _490_recIdents = _out130;
            if ((_489_isErased) && (!(_482_allErased))) {
              _487_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _487_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _487_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _490_recIdents);
            _481_i = (_481_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _482_allErased;
        }
      } else if (_source22.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _491___mcc_h12 = _source22.dtor_path;
        Dafny.ISequence<DAST._IExpression> _492___mcc_h13 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _493_args = _492___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _494_path = _491___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _495_path;
          Dafny.ISequence<Dafny.Rune> _out131;
          _out131 = DCOMP.COMP.GenPath(_494_path);
          _495_path = _out131;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _495_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _496_i;
          _496_i = BigInteger.Zero;
          while ((_496_i) < (new BigInteger((_493_args).Count))) {
            if ((_496_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _497_recursiveGen;
            bool _498___v33;
            bool _499_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _500_recIdents;
            Dafny.ISequence<Dafny.Rune> _out132;
            bool _out133;
            bool _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            DCOMP.COMP.GenExpr((_493_args).Select(_496_i), selfIdent, @params, true, out _out132, out _out133, out _out134, out _out135);
            _497_recursiveGen = _out132;
            _498___v33 = _out133;
            _499_isErased = _out134;
            _500_recIdents = _out135;
            if (_499_isErased) {
              _497_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _497_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _497_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _500_recIdents);
            _496_i = (_496_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _501___mcc_h14 = _source22.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _502_dims = _501___mcc_h14;
        {
          BigInteger _503_i;
          _503_i = (new BigInteger((_502_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_503_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _504_recursiveGen;
            bool _505___v34;
            bool _506_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _507_recIdents;
            Dafny.ISequence<Dafny.Rune> _out136;
            bool _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP.COMP.GenExpr((_502_dims).Select(_503_i), selfIdent, @params, true, out _out136, out _out137, out _out138, out _out139);
            _504_recursiveGen = _out136;
            _505___v34 = _out137;
            _506_isErased = _out138;
            _507_recIdents = _out139;
            if (!(_506_isErased)) {
              _504_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _504_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _504_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _507_recIdents);
            _503_i = (_503_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _508___mcc_h15 = _source22.dtor_path;
        Dafny.ISequence<Dafny.Rune> _509___mcc_h16 = _source22.dtor_variant;
        bool _510___mcc_h17 = _source22.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _511___mcc_h18 = _source22.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _512_values = _511___mcc_h18;
        bool _513_isCo = _510___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _514_variant = _509___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _515_path = _508___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _516_path;
          Dafny.ISequence<Dafny.Rune> _out140;
          _out140 = DCOMP.COMP.GenPath(_515_path);
          _516_path = _out140;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _516_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _514_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _517_i;
          _517_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_517_i) < (new BigInteger((_512_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_512_values).Select(_517_i);
            Dafny.ISequence<Dafny.Rune> _518_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _519_value = _let_tmp_rhs0.dtor__1;
            if ((_517_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_513_isCo) {
              Dafny.ISequence<Dafny.Rune> _520_recursiveGen;
              bool _521___v35;
              bool _522_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _523_recIdents;
              Dafny.ISequence<Dafny.Rune> _out141;
              bool _out142;
              bool _out143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
              DCOMP.COMP.GenExpr(_519_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out141, out _out142, out _out143, out _out144);
              _520_recursiveGen = _out141;
              _521___v35 = _out142;
              _522_isErased = _out143;
              _523_recIdents = _out144;
              if (!(_522_isErased)) {
                _520_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _520_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _520_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _520_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _523_recIdents);
              Dafny.ISequence<Dafny.Rune> _524_allReadCloned;
              _524_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_523_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _525_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_523_recIdents).Elements) {
                  _525_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_523_recIdents).Contains(_525_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1182)");
              after__ASSIGN_SUCH_THAT_0:;
                _524_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_524_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _525_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _525_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _523_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_523_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_525_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _518_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _524_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _520_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _526_recursiveGen;
              bool _527___v36;
              bool _528_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _529_recIdents;
              Dafny.ISequence<Dafny.Rune> _out145;
              bool _out146;
              bool _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              DCOMP.COMP.GenExpr(_519_value, selfIdent, @params, true, out _out145, out _out146, out _out147, out _out148);
              _526_recursiveGen = _out145;
              _527___v36 = _out146;
              _528_isErased = _out147;
              _529_recIdents = _out148;
              if (!(_528_isErased)) {
                _526_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _526_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _526_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _526_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _518_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _526_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _529_recIdents);
            }
            _517_i = (_517_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_Convert) {
        DAST._IExpression _530___mcc_h19 = _source22.dtor_value;
        DAST._IType _531___mcc_h20 = _source22.dtor_from;
        DAST._IType _532___mcc_h21 = _source22.dtor_typ;
        DAST._IType _533_toTpe = _532___mcc_h21;
        DAST._IType _534_fromTpe = _531___mcc_h20;
        DAST._IExpression _535_expr = _530___mcc_h19;
        {
          if (object.Equals(_534_fromTpe, _533_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _536_recursiveGen;
            bool _537_recOwned;
            bool _538_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _539_recIdents;
            Dafny.ISequence<Dafny.Rune> _out149;
            bool _out150;
            bool _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out149, out _out150, out _out151, out _out152);
            _536_recursiveGen = _out149;
            _537_recOwned = _out150;
            _538_recErased = _out151;
            _539_recIdents = _out152;
            s = _536_recursiveGen;
            isOwned = _537_recOwned;
            isErased = _538_recErased;
            readIdents = _539_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source28 = _System.Tuple2<DAST._IType, DAST._IType>.create(_534_fromTpe, _533_toTpe);
            DAST._IType _540___mcc_h261 = _source28.dtor__0;
            DAST._IType _541___mcc_h262 = _source28.dtor__1;
            DAST._IType _source29 = _540___mcc_h261;
            if (_source29.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _542___mcc_h265 = _source29.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _543___mcc_h266 = _source29.dtor_typeArgs;
              DAST._IResolvedType _544___mcc_h267 = _source29.dtor_resolved;
              DAST._IResolvedType _source30 = _544___mcc_h267;
              if (_source30.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _545___mcc_h277 = _source30.dtor_path;
                DAST._IType _source31 = _541___mcc_h262;
                if (_source31.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _546___mcc_h281 = _source31.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _547___mcc_h282 = _source31.dtor_typeArgs;
                  DAST._IResolvedType _548___mcc_h283 = _source31.dtor_resolved;
                  DAST._IResolvedType _source32 = _548___mcc_h283;
                  if (_source32.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _549___mcc_h287 = _source32.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _550_recursiveGen;
                      bool _551_recOwned;
                      bool _552_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _553_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out153;
                      bool _out154;
                      bool _out155;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out153, out _out154, out _out155, out _out156);
                      _550_recursiveGen = _out153;
                      _551_recOwned = _out154;
                      _552_recErased = _out155;
                      _553_recIdents = _out156;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _550_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _551_recOwned;
                      isErased = _552_recErased;
                      readIdents = _553_recIdents;
                    }
                  } else if (_source32.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _554___mcc_h289 = _source32.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _555_recursiveGen;
                      bool _556_recOwned;
                      bool _557_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _558_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out157;
                      bool _out158;
                      bool _out159;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out157, out _out158, out _out159, out _out160);
                      _555_recursiveGen = _out157;
                      _556_recOwned = _out158;
                      _557_recErased = _out159;
                      _558_recIdents = _out160;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _555_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _556_recOwned;
                      isErased = _557_recErased;
                      readIdents = _558_recIdents;
                    }
                  } else {
                    DAST._IType _559___mcc_h291 = _source32.dtor_Newtype_a0;
                    DAST._IType _560_b = _559___mcc_h291;
                    {
                      if (object.Equals(_534_fromTpe, _560_b)) {
                        Dafny.ISequence<Dafny.Rune> _561_recursiveGen;
                        bool _562_recOwned;
                        bool _563_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _564_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out161;
                        bool _out162;
                        bool _out163;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out161, out _out162, out _out163, out _out164);
                        _561_recursiveGen = _out161;
                        _562_recOwned = _out162;
                        _563_recErased = _out163;
                        _564_recIdents = _out164;
                        Dafny.ISequence<Dafny.Rune> _565_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out165;
                        _out165 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _565_rhsType = _out165;
                        Dafny.ISequence<Dafny.Rune> _566_uneraseFn;
                        _566_uneraseFn = ((_562_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _565_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _566_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _561_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _562_recOwned;
                        isErased = false;
                        readIdents = _564_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out166;
                        bool _out167;
                        bool _out168;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _560_b), _560_b, _533_toTpe), selfIdent, @params, mustOwn, out _out166, out _out167, out _out168, out _out169);
                        s = _out166;
                        isOwned = _out167;
                        isErased = _out168;
                        readIdents = _out169;
                      }
                    }
                  }
                } else if (_source31.is_Nullable) {
                  DAST._IType _567___mcc_h293 = _source31.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _568_recursiveGen;
                    bool _569_recOwned;
                    bool _570_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _571_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out170;
                    bool _out171;
                    bool _out172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out170, out _out171, out _out172, out _out173);
                    _568_recursiveGen = _out170;
                    _569_recOwned = _out171;
                    _570_recErased = _out172;
                    _571_recIdents = _out173;
                    if (!(_569_recOwned)) {
                      _568_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_568_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _568_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _570_recErased;
                    readIdents = _571_recIdents;
                  }
                } else if (_source31.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _572___mcc_h295 = _source31.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _573_recursiveGen;
                    bool _574_recOwned;
                    bool _575_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _576_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out174;
                    bool _out175;
                    bool _out176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out174, out _out175, out _out176, out _out177);
                    _573_recursiveGen = _out174;
                    _574_recOwned = _out175;
                    _575_recErased = _out176;
                    _576_recIdents = _out177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _573_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _574_recOwned;
                    isErased = _575_recErased;
                    readIdents = _576_recIdents;
                  }
                } else if (_source31.is_Array) {
                  DAST._IType _577___mcc_h297 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _578_recursiveGen;
                    bool _579_recOwned;
                    bool _580_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _581_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out178;
                    bool _out179;
                    bool _out180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out178, out _out179, out _out180, out _out181);
                    _578_recursiveGen = _out178;
                    _579_recOwned = _out179;
                    _580_recErased = _out180;
                    _581_recIdents = _out181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _578_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _579_recOwned;
                    isErased = _580_recErased;
                    readIdents = _581_recIdents;
                  }
                } else if (_source31.is_Seq) {
                  DAST._IType _582___mcc_h299 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _583_recursiveGen;
                    bool _584_recOwned;
                    bool _585_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _586_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out182;
                    bool _out183;
                    bool _out184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out182, out _out183, out _out184, out _out185);
                    _583_recursiveGen = _out182;
                    _584_recOwned = _out183;
                    _585_recErased = _out184;
                    _586_recIdents = _out185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _583_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _584_recOwned;
                    isErased = _585_recErased;
                    readIdents = _586_recIdents;
                  }
                } else if (_source31.is_Set) {
                  DAST._IType _587___mcc_h301 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _588_recursiveGen;
                    bool _589_recOwned;
                    bool _590_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _591_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out186;
                    bool _out187;
                    bool _out188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out186, out _out187, out _out188, out _out189);
                    _588_recursiveGen = _out186;
                    _589_recOwned = _out187;
                    _590_recErased = _out188;
                    _591_recIdents = _out189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _588_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _589_recOwned;
                    isErased = _590_recErased;
                    readIdents = _591_recIdents;
                  }
                } else if (_source31.is_Multiset) {
                  DAST._IType _592___mcc_h303 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _593_recursiveGen;
                    bool _594_recOwned;
                    bool _595_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _596_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out190;
                    bool _out191;
                    bool _out192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out190, out _out191, out _out192, out _out193);
                    _593_recursiveGen = _out190;
                    _594_recOwned = _out191;
                    _595_recErased = _out192;
                    _596_recIdents = _out193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _593_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _594_recOwned;
                    isErased = _595_recErased;
                    readIdents = _596_recIdents;
                  }
                } else if (_source31.is_Map) {
                  DAST._IType _597___mcc_h305 = _source31.dtor_key;
                  DAST._IType _598___mcc_h306 = _source31.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _599_recursiveGen;
                    bool _600_recOwned;
                    bool _601_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _602_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out194;
                    bool _out195;
                    bool _out196;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out194, out _out195, out _out196, out _out197);
                    _599_recursiveGen = _out194;
                    _600_recOwned = _out195;
                    _601_recErased = _out196;
                    _602_recIdents = _out197;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _599_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _600_recOwned;
                    isErased = _601_recErased;
                    readIdents = _602_recIdents;
                  }
                } else if (_source31.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _603___mcc_h309 = _source31.dtor_args;
                  DAST._IType _604___mcc_h310 = _source31.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _605_recursiveGen;
                    bool _606_recOwned;
                    bool _607_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _608_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out198;
                    bool _out199;
                    bool _out200;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out198, out _out199, out _out200, out _out201);
                    _605_recursiveGen = _out198;
                    _606_recOwned = _out199;
                    _607_recErased = _out200;
                    _608_recIdents = _out201;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _605_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _606_recOwned;
                    isErased = _607_recErased;
                    readIdents = _608_recIdents;
                  }
                } else if (_source31.is_Primitive) {
                  DAST._IPrimitive _609___mcc_h313 = _source31.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _610_recursiveGen;
                    bool _611_recOwned;
                    bool _612_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _613_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out202;
                    bool _out203;
                    bool _out204;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out205;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out202, out _out203, out _out204, out _out205);
                    _610_recursiveGen = _out202;
                    _611_recOwned = _out203;
                    _612_recErased = _out204;
                    _613_recIdents = _out205;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _610_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _611_recOwned;
                    isErased = _612_recErased;
                    readIdents = _613_recIdents;
                  }
                } else if (_source31.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _614___mcc_h315 = _source31.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _615_recursiveGen;
                    bool _616_recOwned;
                    bool _617_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _618_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out206;
                    bool _out207;
                    bool _out208;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out206, out _out207, out _out208, out _out209);
                    _615_recursiveGen = _out206;
                    _616_recOwned = _out207;
                    _617_recErased = _out208;
                    _618_recIdents = _out209;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _615_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _616_recOwned;
                    isErased = _617_recErased;
                    readIdents = _618_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _619___mcc_h317 = _source31.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _620_recursiveGen;
                    bool _621_recOwned;
                    bool _622_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _623_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out210;
                    bool _out211;
                    bool _out212;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out210, out _out211, out _out212, out _out213);
                    _620_recursiveGen = _out210;
                    _621_recOwned = _out211;
                    _622_recErased = _out212;
                    _623_recIdents = _out213;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _620_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _621_recOwned;
                    isErased = _622_recErased;
                    readIdents = _623_recIdents;
                  }
                }
              } else if (_source30.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _624___mcc_h319 = _source30.dtor_path;
                DAST._IType _source33 = _541___mcc_h262;
                if (_source33.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _625___mcc_h323 = _source33.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _626___mcc_h324 = _source33.dtor_typeArgs;
                  DAST._IResolvedType _627___mcc_h325 = _source33.dtor_resolved;
                  DAST._IResolvedType _source34 = _627___mcc_h325;
                  if (_source34.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _628___mcc_h329 = _source34.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _629_recursiveGen;
                      bool _630_recOwned;
                      bool _631_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _632_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out214;
                      bool _out215;
                      bool _out216;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out214, out _out215, out _out216, out _out217);
                      _629_recursiveGen = _out214;
                      _630_recOwned = _out215;
                      _631_recErased = _out216;
                      _632_recIdents = _out217;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _629_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _630_recOwned;
                      isErased = _631_recErased;
                      readIdents = _632_recIdents;
                    }
                  } else if (_source34.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _633___mcc_h331 = _source34.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _634_recursiveGen;
                      bool _635_recOwned;
                      bool _636_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _637_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out218;
                      bool _out219;
                      bool _out220;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out221;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out218, out _out219, out _out220, out _out221);
                      _634_recursiveGen = _out218;
                      _635_recOwned = _out219;
                      _636_recErased = _out220;
                      _637_recIdents = _out221;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _634_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _635_recOwned;
                      isErased = _636_recErased;
                      readIdents = _637_recIdents;
                    }
                  } else {
                    DAST._IType _638___mcc_h333 = _source34.dtor_Newtype_a0;
                    DAST._IType _639_b = _638___mcc_h333;
                    {
                      if (object.Equals(_534_fromTpe, _639_b)) {
                        Dafny.ISequence<Dafny.Rune> _640_recursiveGen;
                        bool _641_recOwned;
                        bool _642_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _643_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out222;
                        bool _out223;
                        bool _out224;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out222, out _out223, out _out224, out _out225);
                        _640_recursiveGen = _out222;
                        _641_recOwned = _out223;
                        _642_recErased = _out224;
                        _643_recIdents = _out225;
                        Dafny.ISequence<Dafny.Rune> _644_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out226;
                        _out226 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _644_rhsType = _out226;
                        Dafny.ISequence<Dafny.Rune> _645_uneraseFn;
                        _645_uneraseFn = ((_641_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _644_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _645_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _640_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _641_recOwned;
                        isErased = false;
                        readIdents = _643_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out227;
                        bool _out228;
                        bool _out229;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _639_b), _639_b, _533_toTpe), selfIdent, @params, mustOwn, out _out227, out _out228, out _out229, out _out230);
                        s = _out227;
                        isOwned = _out228;
                        isErased = _out229;
                        readIdents = _out230;
                      }
                    }
                  }
                } else if (_source33.is_Nullable) {
                  DAST._IType _646___mcc_h335 = _source33.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _647_recursiveGen;
                    bool _648_recOwned;
                    bool _649_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _650_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out231;
                    bool _out232;
                    bool _out233;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out231, out _out232, out _out233, out _out234);
                    _647_recursiveGen = _out231;
                    _648_recOwned = _out232;
                    _649_recErased = _out233;
                    _650_recIdents = _out234;
                    if (!(_648_recOwned)) {
                      _647_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_647_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _647_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _649_recErased;
                    readIdents = _650_recIdents;
                  }
                } else if (_source33.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _651___mcc_h337 = _source33.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _652_recursiveGen;
                    bool _653_recOwned;
                    bool _654_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _655_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out235;
                    bool _out236;
                    bool _out237;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out235, out _out236, out _out237, out _out238);
                    _652_recursiveGen = _out235;
                    _653_recOwned = _out236;
                    _654_recErased = _out237;
                    _655_recIdents = _out238;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _652_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _653_recOwned;
                    isErased = _654_recErased;
                    readIdents = _655_recIdents;
                  }
                } else if (_source33.is_Array) {
                  DAST._IType _656___mcc_h339 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _657_recursiveGen;
                    bool _658_recOwned;
                    bool _659_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _660_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out239;
                    bool _out240;
                    bool _out241;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out242;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out239, out _out240, out _out241, out _out242);
                    _657_recursiveGen = _out239;
                    _658_recOwned = _out240;
                    _659_recErased = _out241;
                    _660_recIdents = _out242;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _657_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _658_recOwned;
                    isErased = _659_recErased;
                    readIdents = _660_recIdents;
                  }
                } else if (_source33.is_Seq) {
                  DAST._IType _661___mcc_h341 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _662_recursiveGen;
                    bool _663_recOwned;
                    bool _664_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _665_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out243;
                    bool _out244;
                    bool _out245;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out243, out _out244, out _out245, out _out246);
                    _662_recursiveGen = _out243;
                    _663_recOwned = _out244;
                    _664_recErased = _out245;
                    _665_recIdents = _out246;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _662_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _663_recOwned;
                    isErased = _664_recErased;
                    readIdents = _665_recIdents;
                  }
                } else if (_source33.is_Set) {
                  DAST._IType _666___mcc_h343 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _667_recursiveGen;
                    bool _668_recOwned;
                    bool _669_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _670_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out247;
                    bool _out248;
                    bool _out249;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out247, out _out248, out _out249, out _out250);
                    _667_recursiveGen = _out247;
                    _668_recOwned = _out248;
                    _669_recErased = _out249;
                    _670_recIdents = _out250;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _667_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _668_recOwned;
                    isErased = _669_recErased;
                    readIdents = _670_recIdents;
                  }
                } else if (_source33.is_Multiset) {
                  DAST._IType _671___mcc_h345 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _672_recursiveGen;
                    bool _673_recOwned;
                    bool _674_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _675_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out251;
                    bool _out252;
                    bool _out253;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out251, out _out252, out _out253, out _out254);
                    _672_recursiveGen = _out251;
                    _673_recOwned = _out252;
                    _674_recErased = _out253;
                    _675_recIdents = _out254;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _672_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _673_recOwned;
                    isErased = _674_recErased;
                    readIdents = _675_recIdents;
                  }
                } else if (_source33.is_Map) {
                  DAST._IType _676___mcc_h347 = _source33.dtor_key;
                  DAST._IType _677___mcc_h348 = _source33.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _678_recursiveGen;
                    bool _679_recOwned;
                    bool _680_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _681_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out255;
                    bool _out256;
                    bool _out257;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out255, out _out256, out _out257, out _out258);
                    _678_recursiveGen = _out255;
                    _679_recOwned = _out256;
                    _680_recErased = _out257;
                    _681_recIdents = _out258;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _678_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _679_recOwned;
                    isErased = _680_recErased;
                    readIdents = _681_recIdents;
                  }
                } else if (_source33.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _682___mcc_h351 = _source33.dtor_args;
                  DAST._IType _683___mcc_h352 = _source33.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _684_recursiveGen;
                    bool _685_recOwned;
                    bool _686_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _687_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out259;
                    bool _out260;
                    bool _out261;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out259, out _out260, out _out261, out _out262);
                    _684_recursiveGen = _out259;
                    _685_recOwned = _out260;
                    _686_recErased = _out261;
                    _687_recIdents = _out262;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _684_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _685_recOwned;
                    isErased = _686_recErased;
                    readIdents = _687_recIdents;
                  }
                } else if (_source33.is_Primitive) {
                  DAST._IPrimitive _688___mcc_h355 = _source33.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _689_recursiveGen;
                    bool _690_recOwned;
                    bool _691_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _692_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out263;
                    bool _out264;
                    bool _out265;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out263, out _out264, out _out265, out _out266);
                    _689_recursiveGen = _out263;
                    _690_recOwned = _out264;
                    _691_recErased = _out265;
                    _692_recIdents = _out266;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _689_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _690_recOwned;
                    isErased = _691_recErased;
                    readIdents = _692_recIdents;
                  }
                } else if (_source33.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _693___mcc_h357 = _source33.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _694_recursiveGen;
                    bool _695_recOwned;
                    bool _696_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _697_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out267;
                    bool _out268;
                    bool _out269;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out267, out _out268, out _out269, out _out270);
                    _694_recursiveGen = _out267;
                    _695_recOwned = _out268;
                    _696_recErased = _out269;
                    _697_recIdents = _out270;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _694_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _695_recOwned;
                    isErased = _696_recErased;
                    readIdents = _697_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _698___mcc_h359 = _source33.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _699_recursiveGen;
                    bool _700_recOwned;
                    bool _701_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _702_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out271;
                    bool _out272;
                    bool _out273;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out271, out _out272, out _out273, out _out274);
                    _699_recursiveGen = _out271;
                    _700_recOwned = _out272;
                    _701_recErased = _out273;
                    _702_recIdents = _out274;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _699_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _700_recOwned;
                    isErased = _701_recErased;
                    readIdents = _702_recIdents;
                  }
                }
              } else {
                DAST._IType _703___mcc_h361 = _source30.dtor_Newtype_a0;
                DAST._IType _source35 = _541___mcc_h262;
                if (_source35.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _704___mcc_h365 = _source35.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _705___mcc_h366 = _source35.dtor_typeArgs;
                  DAST._IResolvedType _706___mcc_h367 = _source35.dtor_resolved;
                  DAST._IResolvedType _source36 = _706___mcc_h367;
                  if (_source36.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _707___mcc_h374 = _source36.dtor_path;
                    DAST._IType _708_b = _703___mcc_h361;
                    {
                      if (object.Equals(_708_b, _533_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _709_recursiveGen;
                        bool _710_recOwned;
                        bool _711_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _712_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out275;
                        bool _out276;
                        bool _out277;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out275, out _out276, out _out277, out _out278);
                        _709_recursiveGen = _out275;
                        _710_recOwned = _out276;
                        _711_recErased = _out277;
                        _712_recIdents = _out278;
                        Dafny.ISequence<Dafny.Rune> _713_uneraseFn;
                        _713_uneraseFn = ((_710_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _713_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _709_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _710_recOwned;
                        isErased = true;
                        readIdents = _712_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out279;
                        bool _out280;
                        bool _out281;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _708_b), _708_b, _533_toTpe), selfIdent, @params, mustOwn, out _out279, out _out280, out _out281, out _out282);
                        s = _out279;
                        isOwned = _out280;
                        isErased = _out281;
                        readIdents = _out282;
                      }
                    }
                  } else if (_source36.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _714___mcc_h377 = _source36.dtor_path;
                    DAST._IType _715_b = _703___mcc_h361;
                    {
                      if (object.Equals(_715_b, _533_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _716_recursiveGen;
                        bool _717_recOwned;
                        bool _718_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _719_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out283;
                        bool _out284;
                        bool _out285;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out283, out _out284, out _out285, out _out286);
                        _716_recursiveGen = _out283;
                        _717_recOwned = _out284;
                        _718_recErased = _out285;
                        _719_recIdents = _out286;
                        Dafny.ISequence<Dafny.Rune> _720_uneraseFn;
                        _720_uneraseFn = ((_717_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _720_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _716_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _717_recOwned;
                        isErased = true;
                        readIdents = _719_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out287;
                        bool _out288;
                        bool _out289;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _715_b), _715_b, _533_toTpe), selfIdent, @params, mustOwn, out _out287, out _out288, out _out289, out _out290);
                        s = _out287;
                        isOwned = _out288;
                        isErased = _out289;
                        readIdents = _out290;
                      }
                    }
                  } else {
                    DAST._IType _721___mcc_h380 = _source36.dtor_Newtype_a0;
                    DAST._IType _722_b = _721___mcc_h380;
                    {
                      if (object.Equals(_534_fromTpe, _722_b)) {
                        Dafny.ISequence<Dafny.Rune> _723_recursiveGen;
                        bool _724_recOwned;
                        bool _725_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _726_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out291;
                        bool _out292;
                        bool _out293;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out291, out _out292, out _out293, out _out294);
                        _723_recursiveGen = _out291;
                        _724_recOwned = _out292;
                        _725_recErased = _out293;
                        _726_recIdents = _out294;
                        Dafny.ISequence<Dafny.Rune> _727_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out295;
                        _out295 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _727_rhsType = _out295;
                        Dafny.ISequence<Dafny.Rune> _728_uneraseFn;
                        _728_uneraseFn = ((_724_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _727_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _728_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _723_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _724_recOwned;
                        isErased = false;
                        readIdents = _726_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out296;
                        bool _out297;
                        bool _out298;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _722_b), _722_b, _533_toTpe), selfIdent, @params, mustOwn, out _out296, out _out297, out _out298, out _out299);
                        s = _out296;
                        isOwned = _out297;
                        isErased = _out298;
                        readIdents = _out299;
                      }
                    }
                  }
                } else if (_source35.is_Nullable) {
                  DAST._IType _729___mcc_h383 = _source35.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _730_recursiveGen;
                    bool _731_recOwned;
                    bool _732_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _733_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out300;
                    bool _out301;
                    bool _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out300, out _out301, out _out302, out _out303);
                    _730_recursiveGen = _out300;
                    _731_recOwned = _out301;
                    _732_recErased = _out302;
                    _733_recIdents = _out303;
                    if (!(_731_recOwned)) {
                      _730_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_730_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _730_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _732_recErased;
                    readIdents = _733_recIdents;
                  }
                } else if (_source35.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _734___mcc_h386 = _source35.dtor_Tuple_a0;
                  DAST._IType _735_b = _703___mcc_h361;
                  {
                    if (object.Equals(_735_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _736_recursiveGen;
                      bool _737_recOwned;
                      bool _738_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _739_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out304;
                      bool _out305;
                      bool _out306;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out304, out _out305, out _out306, out _out307);
                      _736_recursiveGen = _out304;
                      _737_recOwned = _out305;
                      _738_recErased = _out306;
                      _739_recIdents = _out307;
                      Dafny.ISequence<Dafny.Rune> _740_uneraseFn;
                      _740_uneraseFn = ((_737_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _740_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _736_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _737_recOwned;
                      isErased = true;
                      readIdents = _739_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out308;
                      bool _out309;
                      bool _out310;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _735_b), _735_b, _533_toTpe), selfIdent, @params, mustOwn, out _out308, out _out309, out _out310, out _out311);
                      s = _out308;
                      isOwned = _out309;
                      isErased = _out310;
                      readIdents = _out311;
                    }
                  }
                } else if (_source35.is_Array) {
                  DAST._IType _741___mcc_h389 = _source35.dtor_element;
                  DAST._IType _742_b = _703___mcc_h361;
                  {
                    if (object.Equals(_742_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _743_recursiveGen;
                      bool _744_recOwned;
                      bool _745_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _746_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out312;
                      bool _out313;
                      bool _out314;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out312, out _out313, out _out314, out _out315);
                      _743_recursiveGen = _out312;
                      _744_recOwned = _out313;
                      _745_recErased = _out314;
                      _746_recIdents = _out315;
                      Dafny.ISequence<Dafny.Rune> _747_uneraseFn;
                      _747_uneraseFn = ((_744_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _747_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _743_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _744_recOwned;
                      isErased = true;
                      readIdents = _746_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out316;
                      bool _out317;
                      bool _out318;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _742_b), _742_b, _533_toTpe), selfIdent, @params, mustOwn, out _out316, out _out317, out _out318, out _out319);
                      s = _out316;
                      isOwned = _out317;
                      isErased = _out318;
                      readIdents = _out319;
                    }
                  }
                } else if (_source35.is_Seq) {
                  DAST._IType _748___mcc_h392 = _source35.dtor_element;
                  DAST._IType _749_b = _703___mcc_h361;
                  {
                    if (object.Equals(_749_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _750_recursiveGen;
                      bool _751_recOwned;
                      bool _752_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _753_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out320;
                      bool _out321;
                      bool _out322;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out320, out _out321, out _out322, out _out323);
                      _750_recursiveGen = _out320;
                      _751_recOwned = _out321;
                      _752_recErased = _out322;
                      _753_recIdents = _out323;
                      Dafny.ISequence<Dafny.Rune> _754_uneraseFn;
                      _754_uneraseFn = ((_751_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _754_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _750_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _751_recOwned;
                      isErased = true;
                      readIdents = _753_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out324;
                      bool _out325;
                      bool _out326;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _749_b), _749_b, _533_toTpe), selfIdent, @params, mustOwn, out _out324, out _out325, out _out326, out _out327);
                      s = _out324;
                      isOwned = _out325;
                      isErased = _out326;
                      readIdents = _out327;
                    }
                  }
                } else if (_source35.is_Set) {
                  DAST._IType _755___mcc_h395 = _source35.dtor_element;
                  DAST._IType _756_b = _703___mcc_h361;
                  {
                    if (object.Equals(_756_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _757_recursiveGen;
                      bool _758_recOwned;
                      bool _759_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _760_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out328;
                      bool _out329;
                      bool _out330;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out328, out _out329, out _out330, out _out331);
                      _757_recursiveGen = _out328;
                      _758_recOwned = _out329;
                      _759_recErased = _out330;
                      _760_recIdents = _out331;
                      Dafny.ISequence<Dafny.Rune> _761_uneraseFn;
                      _761_uneraseFn = ((_758_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _761_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _757_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _758_recOwned;
                      isErased = true;
                      readIdents = _760_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out332;
                      bool _out333;
                      bool _out334;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _756_b), _756_b, _533_toTpe), selfIdent, @params, mustOwn, out _out332, out _out333, out _out334, out _out335);
                      s = _out332;
                      isOwned = _out333;
                      isErased = _out334;
                      readIdents = _out335;
                    }
                  }
                } else if (_source35.is_Multiset) {
                  DAST._IType _762___mcc_h398 = _source35.dtor_element;
                  DAST._IType _763_b = _703___mcc_h361;
                  {
                    if (object.Equals(_763_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _764_recursiveGen;
                      bool _765_recOwned;
                      bool _766_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _767_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out336;
                      bool _out337;
                      bool _out338;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out336, out _out337, out _out338, out _out339);
                      _764_recursiveGen = _out336;
                      _765_recOwned = _out337;
                      _766_recErased = _out338;
                      _767_recIdents = _out339;
                      Dafny.ISequence<Dafny.Rune> _768_uneraseFn;
                      _768_uneraseFn = ((_765_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _768_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _764_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _765_recOwned;
                      isErased = true;
                      readIdents = _767_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out340;
                      bool _out341;
                      bool _out342;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _763_b), _763_b, _533_toTpe), selfIdent, @params, mustOwn, out _out340, out _out341, out _out342, out _out343);
                      s = _out340;
                      isOwned = _out341;
                      isErased = _out342;
                      readIdents = _out343;
                    }
                  }
                } else if (_source35.is_Map) {
                  DAST._IType _769___mcc_h401 = _source35.dtor_key;
                  DAST._IType _770___mcc_h402 = _source35.dtor_value;
                  DAST._IType _771_b = _703___mcc_h361;
                  {
                    if (object.Equals(_771_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _772_recursiveGen;
                      bool _773_recOwned;
                      bool _774_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _775_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out344;
                      bool _out345;
                      bool _out346;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out347;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out344, out _out345, out _out346, out _out347);
                      _772_recursiveGen = _out344;
                      _773_recOwned = _out345;
                      _774_recErased = _out346;
                      _775_recIdents = _out347;
                      Dafny.ISequence<Dafny.Rune> _776_uneraseFn;
                      _776_uneraseFn = ((_773_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _776_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _772_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _773_recOwned;
                      isErased = true;
                      readIdents = _775_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out348;
                      bool _out349;
                      bool _out350;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _771_b), _771_b, _533_toTpe), selfIdent, @params, mustOwn, out _out348, out _out349, out _out350, out _out351);
                      s = _out348;
                      isOwned = _out349;
                      isErased = _out350;
                      readIdents = _out351;
                    }
                  }
                } else if (_source35.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _777___mcc_h407 = _source35.dtor_args;
                  DAST._IType _778___mcc_h408 = _source35.dtor_result;
                  DAST._IType _779_b = _703___mcc_h361;
                  {
                    if (object.Equals(_779_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _780_recursiveGen;
                      bool _781_recOwned;
                      bool _782_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _783_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out352;
                      bool _out353;
                      bool _out354;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out352, out _out353, out _out354, out _out355);
                      _780_recursiveGen = _out352;
                      _781_recOwned = _out353;
                      _782_recErased = _out354;
                      _783_recIdents = _out355;
                      Dafny.ISequence<Dafny.Rune> _784_uneraseFn;
                      _784_uneraseFn = ((_781_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _784_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _780_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _781_recOwned;
                      isErased = true;
                      readIdents = _783_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out356;
                      bool _out357;
                      bool _out358;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out359;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _779_b), _779_b, _533_toTpe), selfIdent, @params, mustOwn, out _out356, out _out357, out _out358, out _out359);
                      s = _out356;
                      isOwned = _out357;
                      isErased = _out358;
                      readIdents = _out359;
                    }
                  }
                } else if (_source35.is_Primitive) {
                  DAST._IPrimitive _785___mcc_h413 = _source35.dtor_Primitive_a0;
                  DAST._IType _786_b = _703___mcc_h361;
                  {
                    if (object.Equals(_786_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _787_recursiveGen;
                      bool _788_recOwned;
                      bool _789_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _790_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out360;
                      bool _out361;
                      bool _out362;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out360, out _out361, out _out362, out _out363);
                      _787_recursiveGen = _out360;
                      _788_recOwned = _out361;
                      _789_recErased = _out362;
                      _790_recIdents = _out363;
                      Dafny.ISequence<Dafny.Rune> _791_uneraseFn;
                      _791_uneraseFn = ((_788_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _791_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _787_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _788_recOwned;
                      isErased = true;
                      readIdents = _790_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out364;
                      bool _out365;
                      bool _out366;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _786_b), _786_b, _533_toTpe), selfIdent, @params, mustOwn, out _out364, out _out365, out _out366, out _out367);
                      s = _out364;
                      isOwned = _out365;
                      isErased = _out366;
                      readIdents = _out367;
                    }
                  }
                } else if (_source35.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _792___mcc_h416 = _source35.dtor_Passthrough_a0;
                  DAST._IType _793_b = _703___mcc_h361;
                  {
                    if (object.Equals(_793_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _794_recursiveGen;
                      bool _795_recOwned;
                      bool _796_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _797_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out368;
                      bool _out369;
                      bool _out370;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out368, out _out369, out _out370, out _out371);
                      _794_recursiveGen = _out368;
                      _795_recOwned = _out369;
                      _796_recErased = _out370;
                      _797_recIdents = _out371;
                      Dafny.ISequence<Dafny.Rune> _798_uneraseFn;
                      _798_uneraseFn = ((_795_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _798_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _794_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _795_recOwned;
                      isErased = true;
                      readIdents = _797_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out372;
                      bool _out373;
                      bool _out374;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _793_b), _793_b, _533_toTpe), selfIdent, @params, mustOwn, out _out372, out _out373, out _out374, out _out375);
                      s = _out372;
                      isOwned = _out373;
                      isErased = _out374;
                      readIdents = _out375;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _799___mcc_h419 = _source35.dtor_TypeArg_a0;
                  DAST._IType _800_b = _703___mcc_h361;
                  {
                    if (object.Equals(_800_b, _533_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _801_recursiveGen;
                      bool _802_recOwned;
                      bool _803_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _804_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out376;
                      bool _out377;
                      bool _out378;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out376, out _out377, out _out378, out _out379);
                      _801_recursiveGen = _out376;
                      _802_recOwned = _out377;
                      _803_recErased = _out378;
                      _804_recIdents = _out379;
                      Dafny.ISequence<Dafny.Rune> _805_uneraseFn;
                      _805_uneraseFn = ((_802_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _805_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _801_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _802_recOwned;
                      isErased = true;
                      readIdents = _804_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out380;
                      bool _out381;
                      bool _out382;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _800_b), _800_b, _533_toTpe), selfIdent, @params, mustOwn, out _out380, out _out381, out _out382, out _out383);
                      s = _out380;
                      isOwned = _out381;
                      isErased = _out382;
                      readIdents = _out383;
                    }
                  }
                }
              }
            } else if (_source29.is_Nullable) {
              DAST._IType _806___mcc_h422 = _source29.dtor_Nullable_a0;
              DAST._IType _source37 = _541___mcc_h262;
              if (_source37.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _807___mcc_h426 = _source37.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _808___mcc_h427 = _source37.dtor_typeArgs;
                DAST._IResolvedType _809___mcc_h428 = _source37.dtor_resolved;
                DAST._IResolvedType _source38 = _809___mcc_h428;
                if (_source38.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _810___mcc_h435 = _source38.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _811_recursiveGen;
                    bool _812_recOwned;
                    bool _813_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _814_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out384;
                    bool _out385;
                    bool _out386;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out384, out _out385, out _out386, out _out387);
                    _811_recursiveGen = _out384;
                    _812_recOwned = _out385;
                    _813_recErased = _out386;
                    _814_recIdents = _out387;
                    if (!(_812_recOwned)) {
                      _811_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_811_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_811_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _812_recOwned;
                    isErased = _813_recErased;
                    readIdents = _814_recIdents;
                  }
                } else if (_source38.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _815___mcc_h438 = _source38.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _816_recursiveGen;
                    bool _817_recOwned;
                    bool _818_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _819_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out388;
                    bool _out389;
                    bool _out390;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out388, out _out389, out _out390, out _out391);
                    _816_recursiveGen = _out388;
                    _817_recOwned = _out389;
                    _818_recErased = _out390;
                    _819_recIdents = _out391;
                    if (!(_817_recOwned)) {
                      _816_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_816_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_816_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _817_recOwned;
                    isErased = _818_recErased;
                    readIdents = _819_recIdents;
                  }
                } else {
                  DAST._IType _820___mcc_h441 = _source38.dtor_Newtype_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _821_recursiveGen;
                    bool _822_recOwned;
                    bool _823_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _824_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out392;
                    bool _out393;
                    bool _out394;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out392, out _out393, out _out394, out _out395);
                    _821_recursiveGen = _out392;
                    _822_recOwned = _out393;
                    _823_recErased = _out394;
                    _824_recIdents = _out395;
                    if (!(_822_recOwned)) {
                      _821_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_821_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_821_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _822_recOwned;
                    isErased = _823_recErased;
                    readIdents = _824_recIdents;
                  }
                }
              } else if (_source37.is_Nullable) {
                DAST._IType _825___mcc_h444 = _source37.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _826_recursiveGen;
                  bool _827_recOwned;
                  bool _828_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _829_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out396;
                  bool _out397;
                  bool _out398;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out396, out _out397, out _out398, out _out399);
                  _826_recursiveGen = _out396;
                  _827_recOwned = _out397;
                  _828_recErased = _out398;
                  _829_recIdents = _out399;
                  if (!(_827_recOwned)) {
                    _826_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_826_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_826_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _827_recOwned;
                  isErased = _828_recErased;
                  readIdents = _829_recIdents;
                }
              } else if (_source37.is_Tuple) {
                Dafny.ISequence<DAST._IType> _830___mcc_h447 = _source37.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _831_recursiveGen;
                  bool _832_recOwned;
                  bool _833_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _834_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out400;
                  bool _out401;
                  bool _out402;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out400, out _out401, out _out402, out _out403);
                  _831_recursiveGen = _out400;
                  _832_recOwned = _out401;
                  _833_recErased = _out402;
                  _834_recIdents = _out403;
                  if (!(_832_recOwned)) {
                    _831_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_831_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_831_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _832_recOwned;
                  isErased = _833_recErased;
                  readIdents = _834_recIdents;
                }
              } else if (_source37.is_Array) {
                DAST._IType _835___mcc_h450 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _836_recursiveGen;
                  bool _837_recOwned;
                  bool _838_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _839_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out404;
                  bool _out405;
                  bool _out406;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out404, out _out405, out _out406, out _out407);
                  _836_recursiveGen = _out404;
                  _837_recOwned = _out405;
                  _838_recErased = _out406;
                  _839_recIdents = _out407;
                  if (!(_837_recOwned)) {
                    _836_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_836_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_836_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _837_recOwned;
                  isErased = _838_recErased;
                  readIdents = _839_recIdents;
                }
              } else if (_source37.is_Seq) {
                DAST._IType _840___mcc_h453 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _841_recursiveGen;
                  bool _842_recOwned;
                  bool _843_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _844_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out408;
                  bool _out409;
                  bool _out410;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out408, out _out409, out _out410, out _out411);
                  _841_recursiveGen = _out408;
                  _842_recOwned = _out409;
                  _843_recErased = _out410;
                  _844_recIdents = _out411;
                  if (!(_842_recOwned)) {
                    _841_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_841_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_841_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _842_recOwned;
                  isErased = _843_recErased;
                  readIdents = _844_recIdents;
                }
              } else if (_source37.is_Set) {
                DAST._IType _845___mcc_h456 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _846_recursiveGen;
                  bool _847_recOwned;
                  bool _848_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _849_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out412;
                  bool _out413;
                  bool _out414;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out412, out _out413, out _out414, out _out415);
                  _846_recursiveGen = _out412;
                  _847_recOwned = _out413;
                  _848_recErased = _out414;
                  _849_recIdents = _out415;
                  if (!(_847_recOwned)) {
                    _846_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_846_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_846_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _847_recOwned;
                  isErased = _848_recErased;
                  readIdents = _849_recIdents;
                }
              } else if (_source37.is_Multiset) {
                DAST._IType _850___mcc_h459 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _851_recursiveGen;
                  bool _852_recOwned;
                  bool _853_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _854_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out416;
                  bool _out417;
                  bool _out418;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out416, out _out417, out _out418, out _out419);
                  _851_recursiveGen = _out416;
                  _852_recOwned = _out417;
                  _853_recErased = _out418;
                  _854_recIdents = _out419;
                  if (!(_852_recOwned)) {
                    _851_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_851_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_851_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _852_recOwned;
                  isErased = _853_recErased;
                  readIdents = _854_recIdents;
                }
              } else if (_source37.is_Map) {
                DAST._IType _855___mcc_h462 = _source37.dtor_key;
                DAST._IType _856___mcc_h463 = _source37.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _857_recursiveGen;
                  bool _858_recOwned;
                  bool _859_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _860_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out420;
                  bool _out421;
                  bool _out422;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out420, out _out421, out _out422, out _out423);
                  _857_recursiveGen = _out420;
                  _858_recOwned = _out421;
                  _859_recErased = _out422;
                  _860_recIdents = _out423;
                  if (!(_858_recOwned)) {
                    _857_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_857_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_857_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _858_recOwned;
                  isErased = _859_recErased;
                  readIdents = _860_recIdents;
                }
              } else if (_source37.is_Arrow) {
                Dafny.ISequence<DAST._IType> _861___mcc_h468 = _source37.dtor_args;
                DAST._IType _862___mcc_h469 = _source37.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _863_recursiveGen;
                  bool _864_recOwned;
                  bool _865_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _866_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out424;
                  bool _out425;
                  bool _out426;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out424, out _out425, out _out426, out _out427);
                  _863_recursiveGen = _out424;
                  _864_recOwned = _out425;
                  _865_recErased = _out426;
                  _866_recIdents = _out427;
                  if (!(_864_recOwned)) {
                    _863_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_863_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_863_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _864_recOwned;
                  isErased = _865_recErased;
                  readIdents = _866_recIdents;
                }
              } else if (_source37.is_Primitive) {
                DAST._IPrimitive _867___mcc_h474 = _source37.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _868_recursiveGen;
                  bool _869_recOwned;
                  bool _870_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _871_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out428;
                  bool _out429;
                  bool _out430;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out428, out _out429, out _out430, out _out431);
                  _868_recursiveGen = _out428;
                  _869_recOwned = _out429;
                  _870_recErased = _out430;
                  _871_recIdents = _out431;
                  if (!(_869_recOwned)) {
                    _868_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_868_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_868_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _869_recOwned;
                  isErased = _870_recErased;
                  readIdents = _871_recIdents;
                }
              } else if (_source37.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _872___mcc_h477 = _source37.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _873_recursiveGen;
                  bool _874_recOwned;
                  bool _875_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _876_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out432;
                  bool _out433;
                  bool _out434;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out432, out _out433, out _out434, out _out435);
                  _873_recursiveGen = _out432;
                  _874_recOwned = _out433;
                  _875_recErased = _out434;
                  _876_recIdents = _out435;
                  if (!(_874_recOwned)) {
                    _873_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_873_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_873_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _874_recOwned;
                  isErased = _875_recErased;
                  readIdents = _876_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _877___mcc_h480 = _source37.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _878_recursiveGen;
                  bool _879_recOwned;
                  bool _880_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _881_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out436;
                  bool _out437;
                  bool _out438;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out436, out _out437, out _out438, out _out439);
                  _878_recursiveGen = _out436;
                  _879_recOwned = _out437;
                  _880_recErased = _out438;
                  _881_recIdents = _out439;
                  if (!(_879_recOwned)) {
                    _878_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_878_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_878_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _879_recOwned;
                  isErased = _880_recErased;
                  readIdents = _881_recIdents;
                }
              }
            } else if (_source29.is_Tuple) {
              Dafny.ISequence<DAST._IType> _882___mcc_h483 = _source29.dtor_Tuple_a0;
              DAST._IType _source39 = _541___mcc_h262;
              if (_source39.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _883___mcc_h487 = _source39.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _884___mcc_h488 = _source39.dtor_typeArgs;
                DAST._IResolvedType _885___mcc_h489 = _source39.dtor_resolved;
                DAST._IResolvedType _source40 = _885___mcc_h489;
                if (_source40.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _886___mcc_h493 = _source40.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _887_recursiveGen;
                    bool _888_recOwned;
                    bool _889_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _890_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out440;
                    bool _out441;
                    bool _out442;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out440, out _out441, out _out442, out _out443);
                    _887_recursiveGen = _out440;
                    _888_recOwned = _out441;
                    _889_recErased = _out442;
                    _890_recIdents = _out443;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _887_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _888_recOwned;
                    isErased = _889_recErased;
                    readIdents = _890_recIdents;
                  }
                } else if (_source40.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _891___mcc_h495 = _source40.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _892_recursiveGen;
                    bool _893_recOwned;
                    bool _894_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _895_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out444;
                    bool _out445;
                    bool _out446;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out444, out _out445, out _out446, out _out447);
                    _892_recursiveGen = _out444;
                    _893_recOwned = _out445;
                    _894_recErased = _out446;
                    _895_recIdents = _out447;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _892_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _893_recOwned;
                    isErased = _894_recErased;
                    readIdents = _895_recIdents;
                  }
                } else {
                  DAST._IType _896___mcc_h497 = _source40.dtor_Newtype_a0;
                  DAST._IType _897_b = _896___mcc_h497;
                  {
                    if (object.Equals(_534_fromTpe, _897_b)) {
                      Dafny.ISequence<Dafny.Rune> _898_recursiveGen;
                      bool _899_recOwned;
                      bool _900_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _901_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out448;
                      bool _out449;
                      bool _out450;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out448, out _out449, out _out450, out _out451);
                      _898_recursiveGen = _out448;
                      _899_recOwned = _out449;
                      _900_recErased = _out450;
                      _901_recIdents = _out451;
                      Dafny.ISequence<Dafny.Rune> _902_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out452;
                      _out452 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _902_rhsType = _out452;
                      Dafny.ISequence<Dafny.Rune> _903_uneraseFn;
                      _903_uneraseFn = ((_899_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _902_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _903_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _898_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _899_recOwned;
                      isErased = false;
                      readIdents = _901_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out453;
                      bool _out454;
                      bool _out455;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _897_b), _897_b, _533_toTpe), selfIdent, @params, mustOwn, out _out453, out _out454, out _out455, out _out456);
                      s = _out453;
                      isOwned = _out454;
                      isErased = _out455;
                      readIdents = _out456;
                    }
                  }
                }
              } else if (_source39.is_Nullable) {
                DAST._IType _904___mcc_h499 = _source39.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _905_recursiveGen;
                  bool _906_recOwned;
                  bool _907_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _908_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out457;
                  bool _out458;
                  bool _out459;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out457, out _out458, out _out459, out _out460);
                  _905_recursiveGen = _out457;
                  _906_recOwned = _out458;
                  _907_recErased = _out459;
                  _908_recIdents = _out460;
                  if (!(_906_recOwned)) {
                    _905_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_905_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _905_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _907_recErased;
                  readIdents = _908_recIdents;
                }
              } else if (_source39.is_Tuple) {
                Dafny.ISequence<DAST._IType> _909___mcc_h501 = _source39.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _910_recursiveGen;
                  bool _911_recOwned;
                  bool _912_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _913_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out461;
                  bool _out462;
                  bool _out463;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out461, out _out462, out _out463, out _out464);
                  _910_recursiveGen = _out461;
                  _911_recOwned = _out462;
                  _912_recErased = _out463;
                  _913_recIdents = _out464;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _910_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _911_recOwned;
                  isErased = _912_recErased;
                  readIdents = _913_recIdents;
                }
              } else if (_source39.is_Array) {
                DAST._IType _914___mcc_h503 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _915_recursiveGen;
                  bool _916_recOwned;
                  bool _917_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _918_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out465;
                  bool _out466;
                  bool _out467;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out465, out _out466, out _out467, out _out468);
                  _915_recursiveGen = _out465;
                  _916_recOwned = _out466;
                  _917_recErased = _out467;
                  _918_recIdents = _out468;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _915_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _916_recOwned;
                  isErased = _917_recErased;
                  readIdents = _918_recIdents;
                }
              } else if (_source39.is_Seq) {
                DAST._IType _919___mcc_h505 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _920_recursiveGen;
                  bool _921_recOwned;
                  bool _922_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _923_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out469;
                  bool _out470;
                  bool _out471;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out469, out _out470, out _out471, out _out472);
                  _920_recursiveGen = _out469;
                  _921_recOwned = _out470;
                  _922_recErased = _out471;
                  _923_recIdents = _out472;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _920_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _921_recOwned;
                  isErased = _922_recErased;
                  readIdents = _923_recIdents;
                }
              } else if (_source39.is_Set) {
                DAST._IType _924___mcc_h507 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _925_recursiveGen;
                  bool _926_recOwned;
                  bool _927_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _928_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out473;
                  bool _out474;
                  bool _out475;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out473, out _out474, out _out475, out _out476);
                  _925_recursiveGen = _out473;
                  _926_recOwned = _out474;
                  _927_recErased = _out475;
                  _928_recIdents = _out476;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _925_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _926_recOwned;
                  isErased = _927_recErased;
                  readIdents = _928_recIdents;
                }
              } else if (_source39.is_Multiset) {
                DAST._IType _929___mcc_h509 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _930_recursiveGen;
                  bool _931_recOwned;
                  bool _932_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _933_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out477;
                  bool _out478;
                  bool _out479;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out477, out _out478, out _out479, out _out480);
                  _930_recursiveGen = _out477;
                  _931_recOwned = _out478;
                  _932_recErased = _out479;
                  _933_recIdents = _out480;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _930_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _931_recOwned;
                  isErased = _932_recErased;
                  readIdents = _933_recIdents;
                }
              } else if (_source39.is_Map) {
                DAST._IType _934___mcc_h511 = _source39.dtor_key;
                DAST._IType _935___mcc_h512 = _source39.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _936_recursiveGen;
                  bool _937_recOwned;
                  bool _938_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _939_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out481;
                  bool _out482;
                  bool _out483;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out481, out _out482, out _out483, out _out484);
                  _936_recursiveGen = _out481;
                  _937_recOwned = _out482;
                  _938_recErased = _out483;
                  _939_recIdents = _out484;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _936_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _937_recOwned;
                  isErased = _938_recErased;
                  readIdents = _939_recIdents;
                }
              } else if (_source39.is_Arrow) {
                Dafny.ISequence<DAST._IType> _940___mcc_h515 = _source39.dtor_args;
                DAST._IType _941___mcc_h516 = _source39.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _942_recursiveGen;
                  bool _943_recOwned;
                  bool _944_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _945_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out485;
                  bool _out486;
                  bool _out487;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out488;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out485, out _out486, out _out487, out _out488);
                  _942_recursiveGen = _out485;
                  _943_recOwned = _out486;
                  _944_recErased = _out487;
                  _945_recIdents = _out488;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _942_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _943_recOwned;
                  isErased = _944_recErased;
                  readIdents = _945_recIdents;
                }
              } else if (_source39.is_Primitive) {
                DAST._IPrimitive _946___mcc_h519 = _source39.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _947_recursiveGen;
                  bool _948_recOwned;
                  bool _949_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _950_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out489;
                  bool _out490;
                  bool _out491;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out489, out _out490, out _out491, out _out492);
                  _947_recursiveGen = _out489;
                  _948_recOwned = _out490;
                  _949_recErased = _out491;
                  _950_recIdents = _out492;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _947_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _948_recOwned;
                  isErased = _949_recErased;
                  readIdents = _950_recIdents;
                }
              } else if (_source39.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _951___mcc_h521 = _source39.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _952_recursiveGen;
                  bool _953_recOwned;
                  bool _954_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _955_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out493;
                  bool _out494;
                  bool _out495;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out493, out _out494, out _out495, out _out496);
                  _952_recursiveGen = _out493;
                  _953_recOwned = _out494;
                  _954_recErased = _out495;
                  _955_recIdents = _out496;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _952_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _953_recOwned;
                  isErased = _954_recErased;
                  readIdents = _955_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _956___mcc_h523 = _source39.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _957_recursiveGen;
                  bool _958_recOwned;
                  bool _959_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _960_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out497;
                  bool _out498;
                  bool _out499;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out497, out _out498, out _out499, out _out500);
                  _957_recursiveGen = _out497;
                  _958_recOwned = _out498;
                  _959_recErased = _out499;
                  _960_recIdents = _out500;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _957_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _958_recOwned;
                  isErased = _959_recErased;
                  readIdents = _960_recIdents;
                }
              }
            } else if (_source29.is_Array) {
              DAST._IType _961___mcc_h525 = _source29.dtor_element;
              DAST._IType _source41 = _541___mcc_h262;
              if (_source41.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _962___mcc_h529 = _source41.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _963___mcc_h530 = _source41.dtor_typeArgs;
                DAST._IResolvedType _964___mcc_h531 = _source41.dtor_resolved;
                DAST._IResolvedType _source42 = _964___mcc_h531;
                if (_source42.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _965___mcc_h535 = _source42.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _966_recursiveGen;
                    bool _967_recOwned;
                    bool _968_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _969_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out501;
                    bool _out502;
                    bool _out503;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out501, out _out502, out _out503, out _out504);
                    _966_recursiveGen = _out501;
                    _967_recOwned = _out502;
                    _968_recErased = _out503;
                    _969_recIdents = _out504;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _966_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _967_recOwned;
                    isErased = _968_recErased;
                    readIdents = _969_recIdents;
                  }
                } else if (_source42.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _970___mcc_h537 = _source42.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _971_recursiveGen;
                    bool _972_recOwned;
                    bool _973_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _974_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out505;
                    bool _out506;
                    bool _out507;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out505, out _out506, out _out507, out _out508);
                    _971_recursiveGen = _out505;
                    _972_recOwned = _out506;
                    _973_recErased = _out507;
                    _974_recIdents = _out508;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _971_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _972_recOwned;
                    isErased = _973_recErased;
                    readIdents = _974_recIdents;
                  }
                } else {
                  DAST._IType _975___mcc_h539 = _source42.dtor_Newtype_a0;
                  DAST._IType _976_b = _975___mcc_h539;
                  {
                    if (object.Equals(_534_fromTpe, _976_b)) {
                      Dafny.ISequence<Dafny.Rune> _977_recursiveGen;
                      bool _978_recOwned;
                      bool _979_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _980_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out509;
                      bool _out510;
                      bool _out511;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out509, out _out510, out _out511, out _out512);
                      _977_recursiveGen = _out509;
                      _978_recOwned = _out510;
                      _979_recErased = _out511;
                      _980_recIdents = _out512;
                      Dafny.ISequence<Dafny.Rune> _981_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out513;
                      _out513 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _981_rhsType = _out513;
                      Dafny.ISequence<Dafny.Rune> _982_uneraseFn;
                      _982_uneraseFn = ((_978_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _981_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _982_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _977_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _978_recOwned;
                      isErased = false;
                      readIdents = _980_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out514;
                      bool _out515;
                      bool _out516;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _976_b), _976_b, _533_toTpe), selfIdent, @params, mustOwn, out _out514, out _out515, out _out516, out _out517);
                      s = _out514;
                      isOwned = _out515;
                      isErased = _out516;
                      readIdents = _out517;
                    }
                  }
                }
              } else if (_source41.is_Nullable) {
                DAST._IType _983___mcc_h541 = _source41.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _984_recursiveGen;
                  bool _985_recOwned;
                  bool _986_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _987_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out518;
                  bool _out519;
                  bool _out520;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out518, out _out519, out _out520, out _out521);
                  _984_recursiveGen = _out518;
                  _985_recOwned = _out519;
                  _986_recErased = _out520;
                  _987_recIdents = _out521;
                  if (!(_985_recOwned)) {
                    _984_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_984_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _984_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _986_recErased;
                  readIdents = _987_recIdents;
                }
              } else if (_source41.is_Tuple) {
                Dafny.ISequence<DAST._IType> _988___mcc_h543 = _source41.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _989_recursiveGen;
                  bool _990_recOwned;
                  bool _991_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _992_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out522;
                  bool _out523;
                  bool _out524;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out522, out _out523, out _out524, out _out525);
                  _989_recursiveGen = _out522;
                  _990_recOwned = _out523;
                  _991_recErased = _out524;
                  _992_recIdents = _out525;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _989_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _990_recOwned;
                  isErased = _991_recErased;
                  readIdents = _992_recIdents;
                }
              } else if (_source41.is_Array) {
                DAST._IType _993___mcc_h545 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _994_recursiveGen;
                  bool _995_recOwned;
                  bool _996_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _997_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out526;
                  bool _out527;
                  bool _out528;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out526, out _out527, out _out528, out _out529);
                  _994_recursiveGen = _out526;
                  _995_recOwned = _out527;
                  _996_recErased = _out528;
                  _997_recIdents = _out529;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _994_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _995_recOwned;
                  isErased = _996_recErased;
                  readIdents = _997_recIdents;
                }
              } else if (_source41.is_Seq) {
                DAST._IType _998___mcc_h547 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _999_recursiveGen;
                  bool _1000_recOwned;
                  bool _1001_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1002_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out530;
                  bool _out531;
                  bool _out532;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out530, out _out531, out _out532, out _out533);
                  _999_recursiveGen = _out530;
                  _1000_recOwned = _out531;
                  _1001_recErased = _out532;
                  _1002_recIdents = _out533;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _999_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1000_recOwned;
                  isErased = _1001_recErased;
                  readIdents = _1002_recIdents;
                }
              } else if (_source41.is_Set) {
                DAST._IType _1003___mcc_h549 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1004_recursiveGen;
                  bool _1005_recOwned;
                  bool _1006_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1007_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out534;
                  bool _out535;
                  bool _out536;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out537;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out534, out _out535, out _out536, out _out537);
                  _1004_recursiveGen = _out534;
                  _1005_recOwned = _out535;
                  _1006_recErased = _out536;
                  _1007_recIdents = _out537;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1004_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1005_recOwned;
                  isErased = _1006_recErased;
                  readIdents = _1007_recIdents;
                }
              } else if (_source41.is_Multiset) {
                DAST._IType _1008___mcc_h551 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1009_recursiveGen;
                  bool _1010_recOwned;
                  bool _1011_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1012_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out538;
                  bool _out539;
                  bool _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out538, out _out539, out _out540, out _out541);
                  _1009_recursiveGen = _out538;
                  _1010_recOwned = _out539;
                  _1011_recErased = _out540;
                  _1012_recIdents = _out541;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1009_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1010_recOwned;
                  isErased = _1011_recErased;
                  readIdents = _1012_recIdents;
                }
              } else if (_source41.is_Map) {
                DAST._IType _1013___mcc_h553 = _source41.dtor_key;
                DAST._IType _1014___mcc_h554 = _source41.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1015_recursiveGen;
                  bool _1016_recOwned;
                  bool _1017_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1018_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out542;
                  bool _out543;
                  bool _out544;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out542, out _out543, out _out544, out _out545);
                  _1015_recursiveGen = _out542;
                  _1016_recOwned = _out543;
                  _1017_recErased = _out544;
                  _1018_recIdents = _out545;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1015_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1016_recOwned;
                  isErased = _1017_recErased;
                  readIdents = _1018_recIdents;
                }
              } else if (_source41.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1019___mcc_h557 = _source41.dtor_args;
                DAST._IType _1020___mcc_h558 = _source41.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1021_recursiveGen;
                  bool _1022_recOwned;
                  bool _1023_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1024_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out546;
                  bool _out547;
                  bool _out548;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out546, out _out547, out _out548, out _out549);
                  _1021_recursiveGen = _out546;
                  _1022_recOwned = _out547;
                  _1023_recErased = _out548;
                  _1024_recIdents = _out549;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1021_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1022_recOwned;
                  isErased = _1023_recErased;
                  readIdents = _1024_recIdents;
                }
              } else if (_source41.is_Primitive) {
                DAST._IPrimitive _1025___mcc_h561 = _source41.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1026_recursiveGen;
                  bool _1027_recOwned;
                  bool _1028_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1029_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out550;
                  bool _out551;
                  bool _out552;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out550, out _out551, out _out552, out _out553);
                  _1026_recursiveGen = _out550;
                  _1027_recOwned = _out551;
                  _1028_recErased = _out552;
                  _1029_recIdents = _out553;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1026_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1027_recOwned;
                  isErased = _1028_recErased;
                  readIdents = _1029_recIdents;
                }
              } else if (_source41.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1030___mcc_h563 = _source41.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1031_recursiveGen;
                  bool _1032_recOwned;
                  bool _1033_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1034_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out554;
                  bool _out555;
                  bool _out556;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out554, out _out555, out _out556, out _out557);
                  _1031_recursiveGen = _out554;
                  _1032_recOwned = _out555;
                  _1033_recErased = _out556;
                  _1034_recIdents = _out557;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1031_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1032_recOwned;
                  isErased = _1033_recErased;
                  readIdents = _1034_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1035___mcc_h565 = _source41.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1036_recursiveGen;
                  bool _1037_recOwned;
                  bool _1038_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1039_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out558;
                  bool _out559;
                  bool _out560;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out561;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out558, out _out559, out _out560, out _out561);
                  _1036_recursiveGen = _out558;
                  _1037_recOwned = _out559;
                  _1038_recErased = _out560;
                  _1039_recIdents = _out561;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1036_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1037_recOwned;
                  isErased = _1038_recErased;
                  readIdents = _1039_recIdents;
                }
              }
            } else if (_source29.is_Seq) {
              DAST._IType _1040___mcc_h567 = _source29.dtor_element;
              DAST._IType _source43 = _541___mcc_h262;
              if (_source43.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1041___mcc_h571 = _source43.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1042___mcc_h572 = _source43.dtor_typeArgs;
                DAST._IResolvedType _1043___mcc_h573 = _source43.dtor_resolved;
                DAST._IResolvedType _source44 = _1043___mcc_h573;
                if (_source44.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1044___mcc_h577 = _source44.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1045_recursiveGen;
                    bool _1046_recOwned;
                    bool _1047_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1048_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out562;
                    bool _out563;
                    bool _out564;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out562, out _out563, out _out564, out _out565);
                    _1045_recursiveGen = _out562;
                    _1046_recOwned = _out563;
                    _1047_recErased = _out564;
                    _1048_recIdents = _out565;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1045_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1046_recOwned;
                    isErased = _1047_recErased;
                    readIdents = _1048_recIdents;
                  }
                } else if (_source44.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1049___mcc_h579 = _source44.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1050_recursiveGen;
                    bool _1051_recOwned;
                    bool _1052_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1053_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out566;
                    bool _out567;
                    bool _out568;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out566, out _out567, out _out568, out _out569);
                    _1050_recursiveGen = _out566;
                    _1051_recOwned = _out567;
                    _1052_recErased = _out568;
                    _1053_recIdents = _out569;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1050_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1051_recOwned;
                    isErased = _1052_recErased;
                    readIdents = _1053_recIdents;
                  }
                } else {
                  DAST._IType _1054___mcc_h581 = _source44.dtor_Newtype_a0;
                  DAST._IType _1055_b = _1054___mcc_h581;
                  {
                    if (object.Equals(_534_fromTpe, _1055_b)) {
                      Dafny.ISequence<Dafny.Rune> _1056_recursiveGen;
                      bool _1057_recOwned;
                      bool _1058_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1059_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out570;
                      bool _out571;
                      bool _out572;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out573;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out570, out _out571, out _out572, out _out573);
                      _1056_recursiveGen = _out570;
                      _1057_recOwned = _out571;
                      _1058_recErased = _out572;
                      _1059_recIdents = _out573;
                      Dafny.ISequence<Dafny.Rune> _1060_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out574;
                      _out574 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1060_rhsType = _out574;
                      Dafny.ISequence<Dafny.Rune> _1061_uneraseFn;
                      _1061_uneraseFn = ((_1057_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1060_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1061_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1056_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1057_recOwned;
                      isErased = false;
                      readIdents = _1059_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out575;
                      bool _out576;
                      bool _out577;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1055_b), _1055_b, _533_toTpe), selfIdent, @params, mustOwn, out _out575, out _out576, out _out577, out _out578);
                      s = _out575;
                      isOwned = _out576;
                      isErased = _out577;
                      readIdents = _out578;
                    }
                  }
                }
              } else if (_source43.is_Nullable) {
                DAST._IType _1062___mcc_h583 = _source43.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1063_recursiveGen;
                  bool _1064_recOwned;
                  bool _1065_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1066_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out579;
                  bool _out580;
                  bool _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out579, out _out580, out _out581, out _out582);
                  _1063_recursiveGen = _out579;
                  _1064_recOwned = _out580;
                  _1065_recErased = _out581;
                  _1066_recIdents = _out582;
                  if (!(_1064_recOwned)) {
                    _1063_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1063_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1063_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1065_recErased;
                  readIdents = _1066_recIdents;
                }
              } else if (_source43.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1067___mcc_h585 = _source43.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1068_recursiveGen;
                  bool _1069_recOwned;
                  bool _1070_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1071_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out583;
                  bool _out584;
                  bool _out585;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out583, out _out584, out _out585, out _out586);
                  _1068_recursiveGen = _out583;
                  _1069_recOwned = _out584;
                  _1070_recErased = _out585;
                  _1071_recIdents = _out586;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1068_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1069_recOwned;
                  isErased = _1070_recErased;
                  readIdents = _1071_recIdents;
                }
              } else if (_source43.is_Array) {
                DAST._IType _1072___mcc_h587 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1073_recursiveGen;
                  bool _1074_recOwned;
                  bool _1075_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1076_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out587;
                  bool _out588;
                  bool _out589;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out587, out _out588, out _out589, out _out590);
                  _1073_recursiveGen = _out587;
                  _1074_recOwned = _out588;
                  _1075_recErased = _out589;
                  _1076_recIdents = _out590;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1073_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1074_recOwned;
                  isErased = _1075_recErased;
                  readIdents = _1076_recIdents;
                }
              } else if (_source43.is_Seq) {
                DAST._IType _1077___mcc_h589 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1078_recursiveGen;
                  bool _1079_recOwned;
                  bool _1080_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1081_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out591;
                  bool _out592;
                  bool _out593;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out591, out _out592, out _out593, out _out594);
                  _1078_recursiveGen = _out591;
                  _1079_recOwned = _out592;
                  _1080_recErased = _out593;
                  _1081_recIdents = _out594;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1078_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1079_recOwned;
                  isErased = _1080_recErased;
                  readIdents = _1081_recIdents;
                }
              } else if (_source43.is_Set) {
                DAST._IType _1082___mcc_h591 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1083_recursiveGen;
                  bool _1084_recOwned;
                  bool _1085_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1086_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out595;
                  bool _out596;
                  bool _out597;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out595, out _out596, out _out597, out _out598);
                  _1083_recursiveGen = _out595;
                  _1084_recOwned = _out596;
                  _1085_recErased = _out597;
                  _1086_recIdents = _out598;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1083_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1084_recOwned;
                  isErased = _1085_recErased;
                  readIdents = _1086_recIdents;
                }
              } else if (_source43.is_Multiset) {
                DAST._IType _1087___mcc_h593 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1088_recursiveGen;
                  bool _1089_recOwned;
                  bool _1090_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1091_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out599;
                  bool _out600;
                  bool _out601;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out599, out _out600, out _out601, out _out602);
                  _1088_recursiveGen = _out599;
                  _1089_recOwned = _out600;
                  _1090_recErased = _out601;
                  _1091_recIdents = _out602;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1088_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1089_recOwned;
                  isErased = _1090_recErased;
                  readIdents = _1091_recIdents;
                }
              } else if (_source43.is_Map) {
                DAST._IType _1092___mcc_h595 = _source43.dtor_key;
                DAST._IType _1093___mcc_h596 = _source43.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1094_recursiveGen;
                  bool _1095_recOwned;
                  bool _1096_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1097_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out603;
                  bool _out604;
                  bool _out605;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out603, out _out604, out _out605, out _out606);
                  _1094_recursiveGen = _out603;
                  _1095_recOwned = _out604;
                  _1096_recErased = _out605;
                  _1097_recIdents = _out606;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1094_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1095_recOwned;
                  isErased = _1096_recErased;
                  readIdents = _1097_recIdents;
                }
              } else if (_source43.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1098___mcc_h599 = _source43.dtor_args;
                DAST._IType _1099___mcc_h600 = _source43.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1100_recursiveGen;
                  bool _1101_recOwned;
                  bool _1102_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1103_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out607;
                  bool _out608;
                  bool _out609;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out607, out _out608, out _out609, out _out610);
                  _1100_recursiveGen = _out607;
                  _1101_recOwned = _out608;
                  _1102_recErased = _out609;
                  _1103_recIdents = _out610;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1100_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1101_recOwned;
                  isErased = _1102_recErased;
                  readIdents = _1103_recIdents;
                }
              } else if (_source43.is_Primitive) {
                DAST._IPrimitive _1104___mcc_h603 = _source43.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1105_recursiveGen;
                  bool _1106_recOwned;
                  bool _1107_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1108_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out611;
                  bool _out612;
                  bool _out613;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out611, out _out612, out _out613, out _out614);
                  _1105_recursiveGen = _out611;
                  _1106_recOwned = _out612;
                  _1107_recErased = _out613;
                  _1108_recIdents = _out614;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1105_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1106_recOwned;
                  isErased = _1107_recErased;
                  readIdents = _1108_recIdents;
                }
              } else if (_source43.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1109___mcc_h605 = _source43.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1110_recursiveGen;
                  bool _1111_recOwned;
                  bool _1112_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1113_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out615;
                  bool _out616;
                  bool _out617;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out618;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out615, out _out616, out _out617, out _out618);
                  _1110_recursiveGen = _out615;
                  _1111_recOwned = _out616;
                  _1112_recErased = _out617;
                  _1113_recIdents = _out618;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1110_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1111_recOwned;
                  isErased = _1112_recErased;
                  readIdents = _1113_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1114___mcc_h607 = _source43.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1115_recursiveGen;
                  bool _1116_recOwned;
                  bool _1117_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1118_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out619;
                  bool _out620;
                  bool _out621;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out619, out _out620, out _out621, out _out622);
                  _1115_recursiveGen = _out619;
                  _1116_recOwned = _out620;
                  _1117_recErased = _out621;
                  _1118_recIdents = _out622;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1115_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1116_recOwned;
                  isErased = _1117_recErased;
                  readIdents = _1118_recIdents;
                }
              }
            } else if (_source29.is_Set) {
              DAST._IType _1119___mcc_h609 = _source29.dtor_element;
              DAST._IType _source45 = _541___mcc_h262;
              if (_source45.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1120___mcc_h613 = _source45.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1121___mcc_h614 = _source45.dtor_typeArgs;
                DAST._IResolvedType _1122___mcc_h615 = _source45.dtor_resolved;
                DAST._IResolvedType _source46 = _1122___mcc_h615;
                if (_source46.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1123___mcc_h619 = _source46.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1124_recursiveGen;
                    bool _1125_recOwned;
                    bool _1126_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1127_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out623;
                    bool _out624;
                    bool _out625;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out626;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out623, out _out624, out _out625, out _out626);
                    _1124_recursiveGen = _out623;
                    _1125_recOwned = _out624;
                    _1126_recErased = _out625;
                    _1127_recIdents = _out626;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1124_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1125_recOwned;
                    isErased = _1126_recErased;
                    readIdents = _1127_recIdents;
                  }
                } else if (_source46.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1128___mcc_h621 = _source46.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1129_recursiveGen;
                    bool _1130_recOwned;
                    bool _1131_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1132_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out627;
                    bool _out628;
                    bool _out629;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out627, out _out628, out _out629, out _out630);
                    _1129_recursiveGen = _out627;
                    _1130_recOwned = _out628;
                    _1131_recErased = _out629;
                    _1132_recIdents = _out630;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1129_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1130_recOwned;
                    isErased = _1131_recErased;
                    readIdents = _1132_recIdents;
                  }
                } else {
                  DAST._IType _1133___mcc_h623 = _source46.dtor_Newtype_a0;
                  DAST._IType _1134_b = _1133___mcc_h623;
                  {
                    if (object.Equals(_534_fromTpe, _1134_b)) {
                      Dafny.ISequence<Dafny.Rune> _1135_recursiveGen;
                      bool _1136_recOwned;
                      bool _1137_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1138_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out631;
                      bool _out632;
                      bool _out633;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out631, out _out632, out _out633, out _out634);
                      _1135_recursiveGen = _out631;
                      _1136_recOwned = _out632;
                      _1137_recErased = _out633;
                      _1138_recIdents = _out634;
                      Dafny.ISequence<Dafny.Rune> _1139_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out635;
                      _out635 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1139_rhsType = _out635;
                      Dafny.ISequence<Dafny.Rune> _1140_uneraseFn;
                      _1140_uneraseFn = ((_1136_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1139_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1140_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1135_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1136_recOwned;
                      isErased = false;
                      readIdents = _1138_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out636;
                      bool _out637;
                      bool _out638;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1134_b), _1134_b, _533_toTpe), selfIdent, @params, mustOwn, out _out636, out _out637, out _out638, out _out639);
                      s = _out636;
                      isOwned = _out637;
                      isErased = _out638;
                      readIdents = _out639;
                    }
                  }
                }
              } else if (_source45.is_Nullable) {
                DAST._IType _1141___mcc_h625 = _source45.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1142_recursiveGen;
                  bool _1143_recOwned;
                  bool _1144_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1145_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out640;
                  bool _out641;
                  bool _out642;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out640, out _out641, out _out642, out _out643);
                  _1142_recursiveGen = _out640;
                  _1143_recOwned = _out641;
                  _1144_recErased = _out642;
                  _1145_recIdents = _out643;
                  if (!(_1143_recOwned)) {
                    _1142_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1142_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1142_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1144_recErased;
                  readIdents = _1145_recIdents;
                }
              } else if (_source45.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1146___mcc_h627 = _source45.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1147_recursiveGen;
                  bool _1148_recOwned;
                  bool _1149_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1150_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out644;
                  bool _out645;
                  bool _out646;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out644, out _out645, out _out646, out _out647);
                  _1147_recursiveGen = _out644;
                  _1148_recOwned = _out645;
                  _1149_recErased = _out646;
                  _1150_recIdents = _out647;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1147_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1148_recOwned;
                  isErased = _1149_recErased;
                  readIdents = _1150_recIdents;
                }
              } else if (_source45.is_Array) {
                DAST._IType _1151___mcc_h629 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1152_recursiveGen;
                  bool _1153_recOwned;
                  bool _1154_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1155_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out648;
                  bool _out649;
                  bool _out650;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out651;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out648, out _out649, out _out650, out _out651);
                  _1152_recursiveGen = _out648;
                  _1153_recOwned = _out649;
                  _1154_recErased = _out650;
                  _1155_recIdents = _out651;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1152_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1153_recOwned;
                  isErased = _1154_recErased;
                  readIdents = _1155_recIdents;
                }
              } else if (_source45.is_Seq) {
                DAST._IType _1156___mcc_h631 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1157_recursiveGen;
                  bool _1158_recOwned;
                  bool _1159_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1160_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out652;
                  bool _out653;
                  bool _out654;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out652, out _out653, out _out654, out _out655);
                  _1157_recursiveGen = _out652;
                  _1158_recOwned = _out653;
                  _1159_recErased = _out654;
                  _1160_recIdents = _out655;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1157_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1158_recOwned;
                  isErased = _1159_recErased;
                  readIdents = _1160_recIdents;
                }
              } else if (_source45.is_Set) {
                DAST._IType _1161___mcc_h633 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1162_recursiveGen;
                  bool _1163_recOwned;
                  bool _1164_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1165_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out656;
                  bool _out657;
                  bool _out658;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out659;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out656, out _out657, out _out658, out _out659);
                  _1162_recursiveGen = _out656;
                  _1163_recOwned = _out657;
                  _1164_recErased = _out658;
                  _1165_recIdents = _out659;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1162_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1163_recOwned;
                  isErased = _1164_recErased;
                  readIdents = _1165_recIdents;
                }
              } else if (_source45.is_Multiset) {
                DAST._IType _1166___mcc_h635 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1167_recursiveGen;
                  bool _1168_recOwned;
                  bool _1169_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1170_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out660;
                  bool _out661;
                  bool _out662;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out660, out _out661, out _out662, out _out663);
                  _1167_recursiveGen = _out660;
                  _1168_recOwned = _out661;
                  _1169_recErased = _out662;
                  _1170_recIdents = _out663;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1167_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1168_recOwned;
                  isErased = _1169_recErased;
                  readIdents = _1170_recIdents;
                }
              } else if (_source45.is_Map) {
                DAST._IType _1171___mcc_h637 = _source45.dtor_key;
                DAST._IType _1172___mcc_h638 = _source45.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1173_recursiveGen;
                  bool _1174_recOwned;
                  bool _1175_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1176_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out664;
                  bool _out665;
                  bool _out666;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out664, out _out665, out _out666, out _out667);
                  _1173_recursiveGen = _out664;
                  _1174_recOwned = _out665;
                  _1175_recErased = _out666;
                  _1176_recIdents = _out667;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1173_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1174_recOwned;
                  isErased = _1175_recErased;
                  readIdents = _1176_recIdents;
                }
              } else if (_source45.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1177___mcc_h641 = _source45.dtor_args;
                DAST._IType _1178___mcc_h642 = _source45.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1179_recursiveGen;
                  bool _1180_recOwned;
                  bool _1181_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1182_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out668;
                  bool _out669;
                  bool _out670;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out671;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out668, out _out669, out _out670, out _out671);
                  _1179_recursiveGen = _out668;
                  _1180_recOwned = _out669;
                  _1181_recErased = _out670;
                  _1182_recIdents = _out671;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1179_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1180_recOwned;
                  isErased = _1181_recErased;
                  readIdents = _1182_recIdents;
                }
              } else if (_source45.is_Primitive) {
                DAST._IPrimitive _1183___mcc_h645 = _source45.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1184_recursiveGen;
                  bool _1185_recOwned;
                  bool _1186_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1187_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out672;
                  bool _out673;
                  bool _out674;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out675;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out672, out _out673, out _out674, out _out675);
                  _1184_recursiveGen = _out672;
                  _1185_recOwned = _out673;
                  _1186_recErased = _out674;
                  _1187_recIdents = _out675;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1184_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1185_recOwned;
                  isErased = _1186_recErased;
                  readIdents = _1187_recIdents;
                }
              } else if (_source45.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1188___mcc_h647 = _source45.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1189_recursiveGen;
                  bool _1190_recOwned;
                  bool _1191_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1192_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out676;
                  bool _out677;
                  bool _out678;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out676, out _out677, out _out678, out _out679);
                  _1189_recursiveGen = _out676;
                  _1190_recOwned = _out677;
                  _1191_recErased = _out678;
                  _1192_recIdents = _out679;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1189_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1190_recOwned;
                  isErased = _1191_recErased;
                  readIdents = _1192_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1193___mcc_h649 = _source45.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1194_recursiveGen;
                  bool _1195_recOwned;
                  bool _1196_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1197_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out680;
                  bool _out681;
                  bool _out682;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out683;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out680, out _out681, out _out682, out _out683);
                  _1194_recursiveGen = _out680;
                  _1195_recOwned = _out681;
                  _1196_recErased = _out682;
                  _1197_recIdents = _out683;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1194_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1195_recOwned;
                  isErased = _1196_recErased;
                  readIdents = _1197_recIdents;
                }
              }
            } else if (_source29.is_Multiset) {
              DAST._IType _1198___mcc_h651 = _source29.dtor_element;
              DAST._IType _source47 = _541___mcc_h262;
              if (_source47.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1199___mcc_h655 = _source47.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1200___mcc_h656 = _source47.dtor_typeArgs;
                DAST._IResolvedType _1201___mcc_h657 = _source47.dtor_resolved;
                DAST._IResolvedType _source48 = _1201___mcc_h657;
                if (_source48.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1202___mcc_h661 = _source48.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1203_recursiveGen;
                    bool _1204_recOwned;
                    bool _1205_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1206_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out684;
                    bool _out685;
                    bool _out686;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out687;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out684, out _out685, out _out686, out _out687);
                    _1203_recursiveGen = _out684;
                    _1204_recOwned = _out685;
                    _1205_recErased = _out686;
                    _1206_recIdents = _out687;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1203_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1204_recOwned;
                    isErased = _1205_recErased;
                    readIdents = _1206_recIdents;
                  }
                } else if (_source48.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1207___mcc_h663 = _source48.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1208_recursiveGen;
                    bool _1209_recOwned;
                    bool _1210_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1211_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out688;
                    bool _out689;
                    bool _out690;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out688, out _out689, out _out690, out _out691);
                    _1208_recursiveGen = _out688;
                    _1209_recOwned = _out689;
                    _1210_recErased = _out690;
                    _1211_recIdents = _out691;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1208_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1209_recOwned;
                    isErased = _1210_recErased;
                    readIdents = _1211_recIdents;
                  }
                } else {
                  DAST._IType _1212___mcc_h665 = _source48.dtor_Newtype_a0;
                  DAST._IType _1213_b = _1212___mcc_h665;
                  {
                    if (object.Equals(_534_fromTpe, _1213_b)) {
                      Dafny.ISequence<Dafny.Rune> _1214_recursiveGen;
                      bool _1215_recOwned;
                      bool _1216_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1217_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out692;
                      bool _out693;
                      bool _out694;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out695;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out692, out _out693, out _out694, out _out695);
                      _1214_recursiveGen = _out692;
                      _1215_recOwned = _out693;
                      _1216_recErased = _out694;
                      _1217_recIdents = _out695;
                      Dafny.ISequence<Dafny.Rune> _1218_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out696;
                      _out696 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1218_rhsType = _out696;
                      Dafny.ISequence<Dafny.Rune> _1219_uneraseFn;
                      _1219_uneraseFn = ((_1215_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1218_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1219_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1214_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1215_recOwned;
                      isErased = false;
                      readIdents = _1217_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out697;
                      bool _out698;
                      bool _out699;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1213_b), _1213_b, _533_toTpe), selfIdent, @params, mustOwn, out _out697, out _out698, out _out699, out _out700);
                      s = _out697;
                      isOwned = _out698;
                      isErased = _out699;
                      readIdents = _out700;
                    }
                  }
                }
              } else if (_source47.is_Nullable) {
                DAST._IType _1220___mcc_h667 = _source47.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1221_recursiveGen;
                  bool _1222_recOwned;
                  bool _1223_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1224_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out701;
                  bool _out702;
                  bool _out703;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out704;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out701, out _out702, out _out703, out _out704);
                  _1221_recursiveGen = _out701;
                  _1222_recOwned = _out702;
                  _1223_recErased = _out703;
                  _1224_recIdents = _out704;
                  if (!(_1222_recOwned)) {
                    _1221_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1221_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1221_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1223_recErased;
                  readIdents = _1224_recIdents;
                }
              } else if (_source47.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1225___mcc_h669 = _source47.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1226_recursiveGen;
                  bool _1227_recOwned;
                  bool _1228_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1229_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out705;
                  bool _out706;
                  bool _out707;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out708;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out705, out _out706, out _out707, out _out708);
                  _1226_recursiveGen = _out705;
                  _1227_recOwned = _out706;
                  _1228_recErased = _out707;
                  _1229_recIdents = _out708;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1226_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1227_recOwned;
                  isErased = _1228_recErased;
                  readIdents = _1229_recIdents;
                }
              } else if (_source47.is_Array) {
                DAST._IType _1230___mcc_h671 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1231_recursiveGen;
                  bool _1232_recOwned;
                  bool _1233_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1234_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out709;
                  bool _out710;
                  bool _out711;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out709, out _out710, out _out711, out _out712);
                  _1231_recursiveGen = _out709;
                  _1232_recOwned = _out710;
                  _1233_recErased = _out711;
                  _1234_recIdents = _out712;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1231_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1232_recOwned;
                  isErased = _1233_recErased;
                  readIdents = _1234_recIdents;
                }
              } else if (_source47.is_Seq) {
                DAST._IType _1235___mcc_h673 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1236_recursiveGen;
                  bool _1237_recOwned;
                  bool _1238_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1239_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out713;
                  bool _out714;
                  bool _out715;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out716;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out713, out _out714, out _out715, out _out716);
                  _1236_recursiveGen = _out713;
                  _1237_recOwned = _out714;
                  _1238_recErased = _out715;
                  _1239_recIdents = _out716;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1236_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1237_recOwned;
                  isErased = _1238_recErased;
                  readIdents = _1239_recIdents;
                }
              } else if (_source47.is_Set) {
                DAST._IType _1240___mcc_h675 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1241_recursiveGen;
                  bool _1242_recOwned;
                  bool _1243_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1244_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out717;
                  bool _out718;
                  bool _out719;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out720;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out717, out _out718, out _out719, out _out720);
                  _1241_recursiveGen = _out717;
                  _1242_recOwned = _out718;
                  _1243_recErased = _out719;
                  _1244_recIdents = _out720;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1241_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1242_recOwned;
                  isErased = _1243_recErased;
                  readIdents = _1244_recIdents;
                }
              } else if (_source47.is_Multiset) {
                DAST._IType _1245___mcc_h677 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1246_recursiveGen;
                  bool _1247_recOwned;
                  bool _1248_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1249_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out721;
                  bool _out722;
                  bool _out723;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out721, out _out722, out _out723, out _out724);
                  _1246_recursiveGen = _out721;
                  _1247_recOwned = _out722;
                  _1248_recErased = _out723;
                  _1249_recIdents = _out724;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1246_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1247_recOwned;
                  isErased = _1248_recErased;
                  readIdents = _1249_recIdents;
                }
              } else if (_source47.is_Map) {
                DAST._IType _1250___mcc_h679 = _source47.dtor_key;
                DAST._IType _1251___mcc_h680 = _source47.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1252_recursiveGen;
                  bool _1253_recOwned;
                  bool _1254_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1255_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out725;
                  bool _out726;
                  bool _out727;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out728;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out725, out _out726, out _out727, out _out728);
                  _1252_recursiveGen = _out725;
                  _1253_recOwned = _out726;
                  _1254_recErased = _out727;
                  _1255_recIdents = _out728;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1252_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1253_recOwned;
                  isErased = _1254_recErased;
                  readIdents = _1255_recIdents;
                }
              } else if (_source47.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1256___mcc_h683 = _source47.dtor_args;
                DAST._IType _1257___mcc_h684 = _source47.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1258_recursiveGen;
                  bool _1259_recOwned;
                  bool _1260_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1261_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out729;
                  bool _out730;
                  bool _out731;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out732;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out729, out _out730, out _out731, out _out732);
                  _1258_recursiveGen = _out729;
                  _1259_recOwned = _out730;
                  _1260_recErased = _out731;
                  _1261_recIdents = _out732;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1258_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1259_recOwned;
                  isErased = _1260_recErased;
                  readIdents = _1261_recIdents;
                }
              } else if (_source47.is_Primitive) {
                DAST._IPrimitive _1262___mcc_h687 = _source47.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1263_recursiveGen;
                  bool _1264_recOwned;
                  bool _1265_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1266_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out733;
                  bool _out734;
                  bool _out735;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out733, out _out734, out _out735, out _out736);
                  _1263_recursiveGen = _out733;
                  _1264_recOwned = _out734;
                  _1265_recErased = _out735;
                  _1266_recIdents = _out736;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1263_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1264_recOwned;
                  isErased = _1265_recErased;
                  readIdents = _1266_recIdents;
                }
              } else if (_source47.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1267___mcc_h689 = _source47.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1268_recursiveGen;
                  bool _1269_recOwned;
                  bool _1270_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1271_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out737;
                  bool _out738;
                  bool _out739;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out740;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out737, out _out738, out _out739, out _out740);
                  _1268_recursiveGen = _out737;
                  _1269_recOwned = _out738;
                  _1270_recErased = _out739;
                  _1271_recIdents = _out740;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1268_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1269_recOwned;
                  isErased = _1270_recErased;
                  readIdents = _1271_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1272___mcc_h691 = _source47.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1273_recursiveGen;
                  bool _1274_recOwned;
                  bool _1275_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1276_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out741;
                  bool _out742;
                  bool _out743;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out744;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out741, out _out742, out _out743, out _out744);
                  _1273_recursiveGen = _out741;
                  _1274_recOwned = _out742;
                  _1275_recErased = _out743;
                  _1276_recIdents = _out744;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1273_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1274_recOwned;
                  isErased = _1275_recErased;
                  readIdents = _1276_recIdents;
                }
              }
            } else if (_source29.is_Map) {
              DAST._IType _1277___mcc_h693 = _source29.dtor_key;
              DAST._IType _1278___mcc_h694 = _source29.dtor_value;
              DAST._IType _source49 = _541___mcc_h262;
              if (_source49.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1279___mcc_h701 = _source49.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1280___mcc_h702 = _source49.dtor_typeArgs;
                DAST._IResolvedType _1281___mcc_h703 = _source49.dtor_resolved;
                DAST._IResolvedType _source50 = _1281___mcc_h703;
                if (_source50.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1282___mcc_h707 = _source50.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1283_recursiveGen;
                    bool _1284_recOwned;
                    bool _1285_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1286_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out745;
                    bool _out746;
                    bool _out747;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out745, out _out746, out _out747, out _out748);
                    _1283_recursiveGen = _out745;
                    _1284_recOwned = _out746;
                    _1285_recErased = _out747;
                    _1286_recIdents = _out748;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1283_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1284_recOwned;
                    isErased = _1285_recErased;
                    readIdents = _1286_recIdents;
                  }
                } else if (_source50.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1287___mcc_h709 = _source50.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1288_recursiveGen;
                    bool _1289_recOwned;
                    bool _1290_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1291_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out749;
                    bool _out750;
                    bool _out751;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out752;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out749, out _out750, out _out751, out _out752);
                    _1288_recursiveGen = _out749;
                    _1289_recOwned = _out750;
                    _1290_recErased = _out751;
                    _1291_recIdents = _out752;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1288_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1289_recOwned;
                    isErased = _1290_recErased;
                    readIdents = _1291_recIdents;
                  }
                } else {
                  DAST._IType _1292___mcc_h711 = _source50.dtor_Newtype_a0;
                  DAST._IType _1293_b = _1292___mcc_h711;
                  {
                    if (object.Equals(_534_fromTpe, _1293_b)) {
                      Dafny.ISequence<Dafny.Rune> _1294_recursiveGen;
                      bool _1295_recOwned;
                      bool _1296_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1297_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out753;
                      bool _out754;
                      bool _out755;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out756;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out753, out _out754, out _out755, out _out756);
                      _1294_recursiveGen = _out753;
                      _1295_recOwned = _out754;
                      _1296_recErased = _out755;
                      _1297_recIdents = _out756;
                      Dafny.ISequence<Dafny.Rune> _1298_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out757;
                      _out757 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1298_rhsType = _out757;
                      Dafny.ISequence<Dafny.Rune> _1299_uneraseFn;
                      _1299_uneraseFn = ((_1295_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1298_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1299_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1294_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1295_recOwned;
                      isErased = false;
                      readIdents = _1297_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out758;
                      bool _out759;
                      bool _out760;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out761;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1293_b), _1293_b, _533_toTpe), selfIdent, @params, mustOwn, out _out758, out _out759, out _out760, out _out761);
                      s = _out758;
                      isOwned = _out759;
                      isErased = _out760;
                      readIdents = _out761;
                    }
                  }
                }
              } else if (_source49.is_Nullable) {
                DAST._IType _1300___mcc_h713 = _source49.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1301_recursiveGen;
                  bool _1302_recOwned;
                  bool _1303_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1304_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out762;
                  bool _out763;
                  bool _out764;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out762, out _out763, out _out764, out _out765);
                  _1301_recursiveGen = _out762;
                  _1302_recOwned = _out763;
                  _1303_recErased = _out764;
                  _1304_recIdents = _out765;
                  if (!(_1302_recOwned)) {
                    _1301_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1301_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1301_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1303_recErased;
                  readIdents = _1304_recIdents;
                }
              } else if (_source49.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1305___mcc_h715 = _source49.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1306_recursiveGen;
                  bool _1307_recOwned;
                  bool _1308_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1309_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out766;
                  bool _out767;
                  bool _out768;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out766, out _out767, out _out768, out _out769);
                  _1306_recursiveGen = _out766;
                  _1307_recOwned = _out767;
                  _1308_recErased = _out768;
                  _1309_recIdents = _out769;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1306_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1307_recOwned;
                  isErased = _1308_recErased;
                  readIdents = _1309_recIdents;
                }
              } else if (_source49.is_Array) {
                DAST._IType _1310___mcc_h717 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1311_recursiveGen;
                  bool _1312_recOwned;
                  bool _1313_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1314_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out770;
                  bool _out771;
                  bool _out772;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out773;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out770, out _out771, out _out772, out _out773);
                  _1311_recursiveGen = _out770;
                  _1312_recOwned = _out771;
                  _1313_recErased = _out772;
                  _1314_recIdents = _out773;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1311_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1312_recOwned;
                  isErased = _1313_recErased;
                  readIdents = _1314_recIdents;
                }
              } else if (_source49.is_Seq) {
                DAST._IType _1315___mcc_h719 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1316_recursiveGen;
                  bool _1317_recOwned;
                  bool _1318_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1319_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out774;
                  bool _out775;
                  bool _out776;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out777;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out774, out _out775, out _out776, out _out777);
                  _1316_recursiveGen = _out774;
                  _1317_recOwned = _out775;
                  _1318_recErased = _out776;
                  _1319_recIdents = _out777;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1316_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1317_recOwned;
                  isErased = _1318_recErased;
                  readIdents = _1319_recIdents;
                }
              } else if (_source49.is_Set) {
                DAST._IType _1320___mcc_h721 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1321_recursiveGen;
                  bool _1322_recOwned;
                  bool _1323_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1324_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out778;
                  bool _out779;
                  bool _out780;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out778, out _out779, out _out780, out _out781);
                  _1321_recursiveGen = _out778;
                  _1322_recOwned = _out779;
                  _1323_recErased = _out780;
                  _1324_recIdents = _out781;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1321_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1322_recOwned;
                  isErased = _1323_recErased;
                  readIdents = _1324_recIdents;
                }
              } else if (_source49.is_Multiset) {
                DAST._IType _1325___mcc_h723 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1326_recursiveGen;
                  bool _1327_recOwned;
                  bool _1328_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1329_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out782;
                  bool _out783;
                  bool _out784;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out785;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out782, out _out783, out _out784, out _out785);
                  _1326_recursiveGen = _out782;
                  _1327_recOwned = _out783;
                  _1328_recErased = _out784;
                  _1329_recIdents = _out785;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1326_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1327_recOwned;
                  isErased = _1328_recErased;
                  readIdents = _1329_recIdents;
                }
              } else if (_source49.is_Map) {
                DAST._IType _1330___mcc_h725 = _source49.dtor_key;
                DAST._IType _1331___mcc_h726 = _source49.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1332_recursiveGen;
                  bool _1333_recOwned;
                  bool _1334_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1335_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out786;
                  bool _out787;
                  bool _out788;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out789;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out786, out _out787, out _out788, out _out789);
                  _1332_recursiveGen = _out786;
                  _1333_recOwned = _out787;
                  _1334_recErased = _out788;
                  _1335_recIdents = _out789;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1332_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1333_recOwned;
                  isErased = _1334_recErased;
                  readIdents = _1335_recIdents;
                }
              } else if (_source49.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1336___mcc_h729 = _source49.dtor_args;
                DAST._IType _1337___mcc_h730 = _source49.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1338_recursiveGen;
                  bool _1339_recOwned;
                  bool _1340_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1341_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out790;
                  bool _out791;
                  bool _out792;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out790, out _out791, out _out792, out _out793);
                  _1338_recursiveGen = _out790;
                  _1339_recOwned = _out791;
                  _1340_recErased = _out792;
                  _1341_recIdents = _out793;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1338_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1339_recOwned;
                  isErased = _1340_recErased;
                  readIdents = _1341_recIdents;
                }
              } else if (_source49.is_Primitive) {
                DAST._IPrimitive _1342___mcc_h733 = _source49.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1343_recursiveGen;
                  bool _1344_recOwned;
                  bool _1345_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1346_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out794;
                  bool _out795;
                  bool _out796;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out797;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out794, out _out795, out _out796, out _out797);
                  _1343_recursiveGen = _out794;
                  _1344_recOwned = _out795;
                  _1345_recErased = _out796;
                  _1346_recIdents = _out797;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1343_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1344_recOwned;
                  isErased = _1345_recErased;
                  readIdents = _1346_recIdents;
                }
              } else if (_source49.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1347___mcc_h735 = _source49.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1348_recursiveGen;
                  bool _1349_recOwned;
                  bool _1350_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1351_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out798;
                  bool _out799;
                  bool _out800;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out801;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out798, out _out799, out _out800, out _out801);
                  _1348_recursiveGen = _out798;
                  _1349_recOwned = _out799;
                  _1350_recErased = _out800;
                  _1351_recIdents = _out801;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1348_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1349_recOwned;
                  isErased = _1350_recErased;
                  readIdents = _1351_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1352___mcc_h737 = _source49.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1353_recursiveGen;
                  bool _1354_recOwned;
                  bool _1355_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1356_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out802;
                  bool _out803;
                  bool _out804;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out802, out _out803, out _out804, out _out805);
                  _1353_recursiveGen = _out802;
                  _1354_recOwned = _out803;
                  _1355_recErased = _out804;
                  _1356_recIdents = _out805;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1353_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1354_recOwned;
                  isErased = _1355_recErased;
                  readIdents = _1356_recIdents;
                }
              }
            } else if (_source29.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1357___mcc_h739 = _source29.dtor_args;
              DAST._IType _1358___mcc_h740 = _source29.dtor_result;
              DAST._IType _source51 = _541___mcc_h262;
              if (_source51.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1359___mcc_h747 = _source51.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1360___mcc_h748 = _source51.dtor_typeArgs;
                DAST._IResolvedType _1361___mcc_h749 = _source51.dtor_resolved;
                DAST._IResolvedType _source52 = _1361___mcc_h749;
                if (_source52.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1362___mcc_h753 = _source52.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1363_recursiveGen;
                    bool _1364_recOwned;
                    bool _1365_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1366_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out806;
                    bool _out807;
                    bool _out808;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out809;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out806, out _out807, out _out808, out _out809);
                    _1363_recursiveGen = _out806;
                    _1364_recOwned = _out807;
                    _1365_recErased = _out808;
                    _1366_recIdents = _out809;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1363_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1364_recOwned;
                    isErased = _1365_recErased;
                    readIdents = _1366_recIdents;
                  }
                } else if (_source52.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1367___mcc_h755 = _source52.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1368_recursiveGen;
                    bool _1369_recOwned;
                    bool _1370_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1371_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out810;
                    bool _out811;
                    bool _out812;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out813;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out810, out _out811, out _out812, out _out813);
                    _1368_recursiveGen = _out810;
                    _1369_recOwned = _out811;
                    _1370_recErased = _out812;
                    _1371_recIdents = _out813;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1368_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1369_recOwned;
                    isErased = _1370_recErased;
                    readIdents = _1371_recIdents;
                  }
                } else {
                  DAST._IType _1372___mcc_h757 = _source52.dtor_Newtype_a0;
                  DAST._IType _1373_b = _1372___mcc_h757;
                  {
                    if (object.Equals(_534_fromTpe, _1373_b)) {
                      Dafny.ISequence<Dafny.Rune> _1374_recursiveGen;
                      bool _1375_recOwned;
                      bool _1376_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1377_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out814;
                      bool _out815;
                      bool _out816;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out814, out _out815, out _out816, out _out817);
                      _1374_recursiveGen = _out814;
                      _1375_recOwned = _out815;
                      _1376_recErased = _out816;
                      _1377_recIdents = _out817;
                      Dafny.ISequence<Dafny.Rune> _1378_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out818;
                      _out818 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1378_rhsType = _out818;
                      Dafny.ISequence<Dafny.Rune> _1379_uneraseFn;
                      _1379_uneraseFn = ((_1375_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1378_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1379_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1374_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1375_recOwned;
                      isErased = false;
                      readIdents = _1377_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out819;
                      bool _out820;
                      bool _out821;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out822;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1373_b), _1373_b, _533_toTpe), selfIdent, @params, mustOwn, out _out819, out _out820, out _out821, out _out822);
                      s = _out819;
                      isOwned = _out820;
                      isErased = _out821;
                      readIdents = _out822;
                    }
                  }
                }
              } else if (_source51.is_Nullable) {
                DAST._IType _1380___mcc_h759 = _source51.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1381_recursiveGen;
                  bool _1382_recOwned;
                  bool _1383_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1384_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out823;
                  bool _out824;
                  bool _out825;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out823, out _out824, out _out825, out _out826);
                  _1381_recursiveGen = _out823;
                  _1382_recOwned = _out824;
                  _1383_recErased = _out825;
                  _1384_recIdents = _out826;
                  if (!(_1382_recOwned)) {
                    _1381_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1381_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1381_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1383_recErased;
                  readIdents = _1384_recIdents;
                }
              } else if (_source51.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1385___mcc_h761 = _source51.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1386_recursiveGen;
                  bool _1387_recOwned;
                  bool _1388_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1389_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out827;
                  bool _out828;
                  bool _out829;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out830;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out827, out _out828, out _out829, out _out830);
                  _1386_recursiveGen = _out827;
                  _1387_recOwned = _out828;
                  _1388_recErased = _out829;
                  _1389_recIdents = _out830;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1386_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1387_recOwned;
                  isErased = _1388_recErased;
                  readIdents = _1389_recIdents;
                }
              } else if (_source51.is_Array) {
                DAST._IType _1390___mcc_h763 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1391_recursiveGen;
                  bool _1392_recOwned;
                  bool _1393_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1394_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out831;
                  bool _out832;
                  bool _out833;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out834;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out831, out _out832, out _out833, out _out834);
                  _1391_recursiveGen = _out831;
                  _1392_recOwned = _out832;
                  _1393_recErased = _out833;
                  _1394_recIdents = _out834;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1391_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1392_recOwned;
                  isErased = _1393_recErased;
                  readIdents = _1394_recIdents;
                }
              } else if (_source51.is_Seq) {
                DAST._IType _1395___mcc_h765 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1396_recursiveGen;
                  bool _1397_recOwned;
                  bool _1398_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1399_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out835;
                  bool _out836;
                  bool _out837;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out835, out _out836, out _out837, out _out838);
                  _1396_recursiveGen = _out835;
                  _1397_recOwned = _out836;
                  _1398_recErased = _out837;
                  _1399_recIdents = _out838;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1396_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1397_recOwned;
                  isErased = _1398_recErased;
                  readIdents = _1399_recIdents;
                }
              } else if (_source51.is_Set) {
                DAST._IType _1400___mcc_h767 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1401_recursiveGen;
                  bool _1402_recOwned;
                  bool _1403_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1404_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out839;
                  bool _out840;
                  bool _out841;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out842;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out839, out _out840, out _out841, out _out842);
                  _1401_recursiveGen = _out839;
                  _1402_recOwned = _out840;
                  _1403_recErased = _out841;
                  _1404_recIdents = _out842;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1401_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1402_recOwned;
                  isErased = _1403_recErased;
                  readIdents = _1404_recIdents;
                }
              } else if (_source51.is_Multiset) {
                DAST._IType _1405___mcc_h769 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1406_recursiveGen;
                  bool _1407_recOwned;
                  bool _1408_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1409_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out843;
                  bool _out844;
                  bool _out845;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out846;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out843, out _out844, out _out845, out _out846);
                  _1406_recursiveGen = _out843;
                  _1407_recOwned = _out844;
                  _1408_recErased = _out845;
                  _1409_recIdents = _out846;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1406_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1407_recOwned;
                  isErased = _1408_recErased;
                  readIdents = _1409_recIdents;
                }
              } else if (_source51.is_Map) {
                DAST._IType _1410___mcc_h771 = _source51.dtor_key;
                DAST._IType _1411___mcc_h772 = _source51.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1412_recursiveGen;
                  bool _1413_recOwned;
                  bool _1414_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1415_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out847;
                  bool _out848;
                  bool _out849;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out847, out _out848, out _out849, out _out850);
                  _1412_recursiveGen = _out847;
                  _1413_recOwned = _out848;
                  _1414_recErased = _out849;
                  _1415_recIdents = _out850;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1412_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1413_recOwned;
                  isErased = _1414_recErased;
                  readIdents = _1415_recIdents;
                }
              } else if (_source51.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1416___mcc_h775 = _source51.dtor_args;
                DAST._IType _1417___mcc_h776 = _source51.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1418_recursiveGen;
                  bool _1419_recOwned;
                  bool _1420_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1421_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out851;
                  bool _out852;
                  bool _out853;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out854;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out851, out _out852, out _out853, out _out854);
                  _1418_recursiveGen = _out851;
                  _1419_recOwned = _out852;
                  _1420_recErased = _out853;
                  _1421_recIdents = _out854;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1418_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1419_recOwned;
                  isErased = _1420_recErased;
                  readIdents = _1421_recIdents;
                }
              } else if (_source51.is_Primitive) {
                DAST._IPrimitive _1422___mcc_h779 = _source51.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1423_recursiveGen;
                  bool _1424_recOwned;
                  bool _1425_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1426_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out855;
                  bool _out856;
                  bool _out857;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out858;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out855, out _out856, out _out857, out _out858);
                  _1423_recursiveGen = _out855;
                  _1424_recOwned = _out856;
                  _1425_recErased = _out857;
                  _1426_recIdents = _out858;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1423_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1424_recOwned;
                  isErased = _1425_recErased;
                  readIdents = _1426_recIdents;
                }
              } else if (_source51.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1427___mcc_h781 = _source51.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1428_recursiveGen;
                  bool _1429_recOwned;
                  bool _1430_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1431_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out859;
                  bool _out860;
                  bool _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out859, out _out860, out _out861, out _out862);
                  _1428_recursiveGen = _out859;
                  _1429_recOwned = _out860;
                  _1430_recErased = _out861;
                  _1431_recIdents = _out862;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1428_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1429_recOwned;
                  isErased = _1430_recErased;
                  readIdents = _1431_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1432___mcc_h783 = _source51.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1433_recursiveGen;
                  bool _1434_recOwned;
                  bool _1435_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1436_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out863;
                  bool _out864;
                  bool _out865;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out866;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out863, out _out864, out _out865, out _out866);
                  _1433_recursiveGen = _out863;
                  _1434_recOwned = _out864;
                  _1435_recErased = _out865;
                  _1436_recIdents = _out866;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1433_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1434_recOwned;
                  isErased = _1435_recErased;
                  readIdents = _1436_recIdents;
                }
              }
            } else if (_source29.is_Primitive) {
              DAST._IPrimitive _1437___mcc_h785 = _source29.dtor_Primitive_a0;
              DAST._IPrimitive _source53 = _1437___mcc_h785;
              if (_source53.is_Int) {
                DAST._IType _source54 = _541___mcc_h262;
                if (_source54.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1438___mcc_h789 = _source54.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1439___mcc_h790 = _source54.dtor_typeArgs;
                  DAST._IResolvedType _1440___mcc_h791 = _source54.dtor_resolved;
                  DAST._IResolvedType _source55 = _1440___mcc_h791;
                  if (_source55.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1441___mcc_h795 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1442_recursiveGen;
                      bool _1443_recOwned;
                      bool _1444_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1445_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out867;
                      bool _out868;
                      bool _out869;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out870;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out867, out _out868, out _out869, out _out870);
                      _1442_recursiveGen = _out867;
                      _1443_recOwned = _out868;
                      _1444_recErased = _out869;
                      _1445_recIdents = _out870;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1442_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1443_recOwned;
                      isErased = _1444_recErased;
                      readIdents = _1445_recIdents;
                    }
                  } else if (_source55.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1446___mcc_h797 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1447_recursiveGen;
                      bool _1448_recOwned;
                      bool _1449_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1450_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out871;
                      bool _out872;
                      bool _out873;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out871, out _out872, out _out873, out _out874);
                      _1447_recursiveGen = _out871;
                      _1448_recOwned = _out872;
                      _1449_recErased = _out873;
                      _1450_recIdents = _out874;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1447_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1448_recOwned;
                      isErased = _1449_recErased;
                      readIdents = _1450_recIdents;
                    }
                  } else {
                    DAST._IType _1451___mcc_h799 = _source55.dtor_Newtype_a0;
                    DAST._IType _1452_b = _1451___mcc_h799;
                    {
                      if (object.Equals(_534_fromTpe, _1452_b)) {
                        Dafny.ISequence<Dafny.Rune> _1453_recursiveGen;
                        bool _1454_recOwned;
                        bool _1455_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1456_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out875;
                        bool _out876;
                        bool _out877;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out878;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out875, out _out876, out _out877, out _out878);
                        _1453_recursiveGen = _out875;
                        _1454_recOwned = _out876;
                        _1455_recErased = _out877;
                        _1456_recIdents = _out878;
                        Dafny.ISequence<Dafny.Rune> _1457_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out879;
                        _out879 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _1457_rhsType = _out879;
                        Dafny.ISequence<Dafny.Rune> _1458_uneraseFn;
                        _1458_uneraseFn = ((_1454_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1457_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1458_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1453_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1454_recOwned;
                        isErased = false;
                        readIdents = _1456_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out880;
                        bool _out881;
                        bool _out882;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1452_b), _1452_b, _533_toTpe), selfIdent, @params, mustOwn, out _out880, out _out881, out _out882, out _out883);
                        s = _out880;
                        isOwned = _out881;
                        isErased = _out882;
                        readIdents = _out883;
                      }
                    }
                  }
                } else if (_source54.is_Nullable) {
                  DAST._IType _1459___mcc_h801 = _source54.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1460_recursiveGen;
                    bool _1461_recOwned;
                    bool _1462_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1463_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out884;
                    bool _out885;
                    bool _out886;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out887;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out884, out _out885, out _out886, out _out887);
                    _1460_recursiveGen = _out884;
                    _1461_recOwned = _out885;
                    _1462_recErased = _out886;
                    _1463_recIdents = _out887;
                    if (!(_1461_recOwned)) {
                      _1460_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1460_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1460_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1462_recErased;
                    readIdents = _1463_recIdents;
                  }
                } else if (_source54.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1464___mcc_h803 = _source54.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1465_recursiveGen;
                    bool _1466_recOwned;
                    bool _1467_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1468_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out888;
                    bool _out889;
                    bool _out890;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out891;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out888, out _out889, out _out890, out _out891);
                    _1465_recursiveGen = _out888;
                    _1466_recOwned = _out889;
                    _1467_recErased = _out890;
                    _1468_recIdents = _out891;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1465_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1466_recOwned;
                    isErased = _1467_recErased;
                    readIdents = _1468_recIdents;
                  }
                } else if (_source54.is_Array) {
                  DAST._IType _1469___mcc_h805 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1470_recursiveGen;
                    bool _1471_recOwned;
                    bool _1472_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1473_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out892;
                    bool _out893;
                    bool _out894;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out892, out _out893, out _out894, out _out895);
                    _1470_recursiveGen = _out892;
                    _1471_recOwned = _out893;
                    _1472_recErased = _out894;
                    _1473_recIdents = _out895;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1470_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1471_recOwned;
                    isErased = _1472_recErased;
                    readIdents = _1473_recIdents;
                  }
                } else if (_source54.is_Seq) {
                  DAST._IType _1474___mcc_h807 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1475_recursiveGen;
                    bool _1476_recOwned;
                    bool _1477_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1478_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out896;
                    bool _out897;
                    bool _out898;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out899;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out896, out _out897, out _out898, out _out899);
                    _1475_recursiveGen = _out896;
                    _1476_recOwned = _out897;
                    _1477_recErased = _out898;
                    _1478_recIdents = _out899;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1475_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1476_recOwned;
                    isErased = _1477_recErased;
                    readIdents = _1478_recIdents;
                  }
                } else if (_source54.is_Set) {
                  DAST._IType _1479___mcc_h809 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1480_recursiveGen;
                    bool _1481_recOwned;
                    bool _1482_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1483_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out900;
                    bool _out901;
                    bool _out902;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out903;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out900, out _out901, out _out902, out _out903);
                    _1480_recursiveGen = _out900;
                    _1481_recOwned = _out901;
                    _1482_recErased = _out902;
                    _1483_recIdents = _out903;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1480_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1481_recOwned;
                    isErased = _1482_recErased;
                    readIdents = _1483_recIdents;
                  }
                } else if (_source54.is_Multiset) {
                  DAST._IType _1484___mcc_h811 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1485_recursiveGen;
                    bool _1486_recOwned;
                    bool _1487_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1488_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out904;
                    bool _out905;
                    bool _out906;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out904, out _out905, out _out906, out _out907);
                    _1485_recursiveGen = _out904;
                    _1486_recOwned = _out905;
                    _1487_recErased = _out906;
                    _1488_recIdents = _out907;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1485_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1486_recOwned;
                    isErased = _1487_recErased;
                    readIdents = _1488_recIdents;
                  }
                } else if (_source54.is_Map) {
                  DAST._IType _1489___mcc_h813 = _source54.dtor_key;
                  DAST._IType _1490___mcc_h814 = _source54.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1491_recursiveGen;
                    bool _1492_recOwned;
                    bool _1493_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1494_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out908;
                    bool _out909;
                    bool _out910;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out911;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out908, out _out909, out _out910, out _out911);
                    _1491_recursiveGen = _out908;
                    _1492_recOwned = _out909;
                    _1493_recErased = _out910;
                    _1494_recIdents = _out911;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1491_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1492_recOwned;
                    isErased = _1493_recErased;
                    readIdents = _1494_recIdents;
                  }
                } else if (_source54.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1495___mcc_h817 = _source54.dtor_args;
                  DAST._IType _1496___mcc_h818 = _source54.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1497_recursiveGen;
                    bool _1498_recOwned;
                    bool _1499_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1500_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out912;
                    bool _out913;
                    bool _out914;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out915;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out912, out _out913, out _out914, out _out915);
                    _1497_recursiveGen = _out912;
                    _1498_recOwned = _out913;
                    _1499_recErased = _out914;
                    _1500_recIdents = _out915;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1497_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1498_recOwned;
                    isErased = _1499_recErased;
                    readIdents = _1500_recIdents;
                  }
                } else if (_source54.is_Primitive) {
                  DAST._IPrimitive _1501___mcc_h821 = _source54.dtor_Primitive_a0;
                  DAST._IPrimitive _source56 = _1501___mcc_h821;
                  if (_source56.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1502_recursiveGen;
                      bool _1503_recOwned;
                      bool _1504_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1505_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out916;
                      bool _out917;
                      bool _out918;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out916, out _out917, out _out918, out _out919);
                      _1502_recursiveGen = _out916;
                      _1503_recOwned = _out917;
                      _1504_recErased = _out918;
                      _1505_recIdents = _out919;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1502_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1503_recOwned;
                      isErased = _1504_recErased;
                      readIdents = _1505_recIdents;
                    }
                  } else if (_source56.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1506_recursiveGen;
                      bool _1507___v47;
                      bool _1508___v48;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1509_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out920;
                      bool _out921;
                      bool _out922;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out923;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, true, out _out920, out _out921, out _out922, out _out923);
                      _1506_recursiveGen = _out920;
                      _1507___v47 = _out921;
                      _1508___v48 = _out922;
                      _1509_recIdents = _out923;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1506_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1509_recIdents;
                    }
                  } else if (_source56.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1510_recursiveGen;
                      bool _1511_recOwned;
                      bool _1512_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1513_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out924;
                      bool _out925;
                      bool _out926;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out927;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out924, out _out925, out _out926, out _out927);
                      _1510_recursiveGen = _out924;
                      _1511_recOwned = _out925;
                      _1512_recErased = _out926;
                      _1513_recIdents = _out927;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1510_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1511_recOwned;
                      isErased = _1512_recErased;
                      readIdents = _1513_recIdents;
                    }
                  } else if (_source56.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1514_recursiveGen;
                      bool _1515_recOwned;
                      bool _1516_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1517_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out928;
                      bool _out929;
                      bool _out930;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out928, out _out929, out _out930, out _out931);
                      _1514_recursiveGen = _out928;
                      _1515_recOwned = _out929;
                      _1516_recErased = _out930;
                      _1517_recIdents = _out931;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1514_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1515_recOwned;
                      isErased = _1516_recErased;
                      readIdents = _1517_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1518_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out932;
                      _out932 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1518_rhsType = _out932;
                      Dafny.ISequence<Dafny.Rune> _1519_recursiveGen;
                      bool _1520___v57;
                      bool _1521___v58;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out933;
                      bool _out934;
                      bool _out935;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, true, out _out933, out _out934, out _out935, out _out936);
                      _1519_recursiveGen = _out933;
                      _1520___v57 = _out934;
                      _1521___v58 = _out935;
                      _1522_recIdents = _out936;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1519_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1522_recIdents;
                    }
                  }
                } else if (_source54.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1523___mcc_h823 = _source54.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1524_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out937;
                    _out937 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                    _1524_rhsType = _out937;
                    Dafny.ISequence<Dafny.Rune> _1525_recursiveGen;
                    bool _1526___v52;
                    bool _1527___v53;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1528_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out938;
                    bool _out939;
                    bool _out940;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out941;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, true, out _out938, out _out939, out _out940, out _out941);
                    _1525_recursiveGen = _out938;
                    _1526___v52 = _out939;
                    _1527___v53 = _out940;
                    _1528_recIdents = _out941;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1524_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1525_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1528_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1529___mcc_h825 = _source54.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1530_recursiveGen;
                    bool _1531_recOwned;
                    bool _1532_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1533_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out942;
                    bool _out943;
                    bool _out944;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out942, out _out943, out _out944, out _out945);
                    _1530_recursiveGen = _out942;
                    _1531_recOwned = _out943;
                    _1532_recErased = _out944;
                    _1533_recIdents = _out945;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1530_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1531_recOwned;
                    isErased = _1532_recErased;
                    readIdents = _1533_recIdents;
                  }
                }
              } else if (_source53.is_Real) {
                DAST._IType _source57 = _541___mcc_h262;
                if (_source57.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1534___mcc_h827 = _source57.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1535___mcc_h828 = _source57.dtor_typeArgs;
                  DAST._IResolvedType _1536___mcc_h829 = _source57.dtor_resolved;
                  DAST._IResolvedType _source58 = _1536___mcc_h829;
                  if (_source58.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1537___mcc_h833 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1538_recursiveGen;
                      bool _1539_recOwned;
                      bool _1540_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1541_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out946;
                      bool _out947;
                      bool _out948;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out946, out _out947, out _out948, out _out949);
                      _1538_recursiveGen = _out946;
                      _1539_recOwned = _out947;
                      _1540_recErased = _out948;
                      _1541_recIdents = _out949;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1538_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1539_recOwned;
                      isErased = _1540_recErased;
                      readIdents = _1541_recIdents;
                    }
                  } else if (_source58.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1542___mcc_h835 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1543_recursiveGen;
                      bool _1544_recOwned;
                      bool _1545_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1546_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out950;
                      bool _out951;
                      bool _out952;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out953;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out950, out _out951, out _out952, out _out953);
                      _1543_recursiveGen = _out950;
                      _1544_recOwned = _out951;
                      _1545_recErased = _out952;
                      _1546_recIdents = _out953;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1543_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1544_recOwned;
                      isErased = _1545_recErased;
                      readIdents = _1546_recIdents;
                    }
                  } else {
                    DAST._IType _1547___mcc_h837 = _source58.dtor_Newtype_a0;
                    DAST._IType _1548_b = _1547___mcc_h837;
                    {
                      if (object.Equals(_534_fromTpe, _1548_b)) {
                        Dafny.ISequence<Dafny.Rune> _1549_recursiveGen;
                        bool _1550_recOwned;
                        bool _1551_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1552_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out954;
                        bool _out955;
                        bool _out956;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out954, out _out955, out _out956, out _out957);
                        _1549_recursiveGen = _out954;
                        _1550_recOwned = _out955;
                        _1551_recErased = _out956;
                        _1552_recIdents = _out957;
                        Dafny.ISequence<Dafny.Rune> _1553_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out958;
                        _out958 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _1553_rhsType = _out958;
                        Dafny.ISequence<Dafny.Rune> _1554_uneraseFn;
                        _1554_uneraseFn = ((_1550_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1553_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1554_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1549_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1550_recOwned;
                        isErased = false;
                        readIdents = _1552_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out959;
                        bool _out960;
                        bool _out961;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out962;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1548_b), _1548_b, _533_toTpe), selfIdent, @params, mustOwn, out _out959, out _out960, out _out961, out _out962);
                        s = _out959;
                        isOwned = _out960;
                        isErased = _out961;
                        readIdents = _out962;
                      }
                    }
                  }
                } else if (_source57.is_Nullable) {
                  DAST._IType _1555___mcc_h839 = _source57.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1556_recursiveGen;
                    bool _1557_recOwned;
                    bool _1558_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out963;
                    bool _out964;
                    bool _out965;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out963, out _out964, out _out965, out _out966);
                    _1556_recursiveGen = _out963;
                    _1557_recOwned = _out964;
                    _1558_recErased = _out965;
                    _1559_recIdents = _out966;
                    if (!(_1557_recOwned)) {
                      _1556_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1556_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1556_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1558_recErased;
                    readIdents = _1559_recIdents;
                  }
                } else if (_source57.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1560___mcc_h841 = _source57.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1561_recursiveGen;
                    bool _1562_recOwned;
                    bool _1563_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1564_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out967;
                    bool _out968;
                    bool _out969;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out970;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out967, out _out968, out _out969, out _out970);
                    _1561_recursiveGen = _out967;
                    _1562_recOwned = _out968;
                    _1563_recErased = _out969;
                    _1564_recIdents = _out970;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1561_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1562_recOwned;
                    isErased = _1563_recErased;
                    readIdents = _1564_recIdents;
                  }
                } else if (_source57.is_Array) {
                  DAST._IType _1565___mcc_h843 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1566_recursiveGen;
                    bool _1567_recOwned;
                    bool _1568_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out971;
                    bool _out972;
                    bool _out973;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out971, out _out972, out _out973, out _out974);
                    _1566_recursiveGen = _out971;
                    _1567_recOwned = _out972;
                    _1568_recErased = _out973;
                    _1569_recIdents = _out974;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1566_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1567_recOwned;
                    isErased = _1568_recErased;
                    readIdents = _1569_recIdents;
                  }
                } else if (_source57.is_Seq) {
                  DAST._IType _1570___mcc_h845 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1571_recursiveGen;
                    bool _1572_recOwned;
                    bool _1573_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1574_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out975;
                    bool _out976;
                    bool _out977;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out978;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out975, out _out976, out _out977, out _out978);
                    _1571_recursiveGen = _out975;
                    _1572_recOwned = _out976;
                    _1573_recErased = _out977;
                    _1574_recIdents = _out978;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1571_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1572_recOwned;
                    isErased = _1573_recErased;
                    readIdents = _1574_recIdents;
                  }
                } else if (_source57.is_Set) {
                  DAST._IType _1575___mcc_h847 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1576_recursiveGen;
                    bool _1577_recOwned;
                    bool _1578_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1579_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out979;
                    bool _out980;
                    bool _out981;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out979, out _out980, out _out981, out _out982);
                    _1576_recursiveGen = _out979;
                    _1577_recOwned = _out980;
                    _1578_recErased = _out981;
                    _1579_recIdents = _out982;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1576_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1577_recOwned;
                    isErased = _1578_recErased;
                    readIdents = _1579_recIdents;
                  }
                } else if (_source57.is_Multiset) {
                  DAST._IType _1580___mcc_h849 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1581_recursiveGen;
                    bool _1582_recOwned;
                    bool _1583_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1584_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out983;
                    bool _out984;
                    bool _out985;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out986;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out983, out _out984, out _out985, out _out986);
                    _1581_recursiveGen = _out983;
                    _1582_recOwned = _out984;
                    _1583_recErased = _out985;
                    _1584_recIdents = _out986;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1581_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1582_recOwned;
                    isErased = _1583_recErased;
                    readIdents = _1584_recIdents;
                  }
                } else if (_source57.is_Map) {
                  DAST._IType _1585___mcc_h851 = _source57.dtor_key;
                  DAST._IType _1586___mcc_h852 = _source57.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1587_recursiveGen;
                    bool _1588_recOwned;
                    bool _1589_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out987;
                    bool _out988;
                    bool _out989;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out987, out _out988, out _out989, out _out990);
                    _1587_recursiveGen = _out987;
                    _1588_recOwned = _out988;
                    _1589_recErased = _out989;
                    _1590_recIdents = _out990;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1587_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1588_recOwned;
                    isErased = _1589_recErased;
                    readIdents = _1590_recIdents;
                  }
                } else if (_source57.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1591___mcc_h855 = _source57.dtor_args;
                  DAST._IType _1592___mcc_h856 = _source57.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1593_recursiveGen;
                    bool _1594_recOwned;
                    bool _1595_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1596_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out991;
                    bool _out992;
                    bool _out993;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out994;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out991, out _out992, out _out993, out _out994);
                    _1593_recursiveGen = _out991;
                    _1594_recOwned = _out992;
                    _1595_recErased = _out993;
                    _1596_recIdents = _out994;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1593_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1594_recOwned;
                    isErased = _1595_recErased;
                    readIdents = _1596_recIdents;
                  }
                } else if (_source57.is_Primitive) {
                  DAST._IPrimitive _1597___mcc_h859 = _source57.dtor_Primitive_a0;
                  DAST._IPrimitive _source59 = _1597___mcc_h859;
                  if (_source59.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1598_recursiveGen;
                      bool _1599___v49;
                      bool _1600___v50;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1601_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out995;
                      bool _out996;
                      bool _out997;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out998;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, false, out _out995, out _out996, out _out997, out _out998);
                      _1598_recursiveGen = _out995;
                      _1599___v49 = _out996;
                      _1600___v50 = _out997;
                      _1601_recIdents = _out998;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1598_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1601_recIdents;
                    }
                  } else if (_source59.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1602_recursiveGen;
                      bool _1603_recOwned;
                      bool _1604_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1605_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out999;
                      bool _out1000;
                      bool _out1001;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out999, out _out1000, out _out1001, out _out1002);
                      _1602_recursiveGen = _out999;
                      _1603_recOwned = _out1000;
                      _1604_recErased = _out1001;
                      _1605_recIdents = _out1002;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1602_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1603_recOwned;
                      isErased = _1604_recErased;
                      readIdents = _1605_recIdents;
                    }
                  } else if (_source59.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1606_recursiveGen;
                      bool _1607_recOwned;
                      bool _1608_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1609_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1003;
                      bool _out1004;
                      bool _out1005;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1006;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1003, out _out1004, out _out1005, out _out1006);
                      _1606_recursiveGen = _out1003;
                      _1607_recOwned = _out1004;
                      _1608_recErased = _out1005;
                      _1609_recIdents = _out1006;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1606_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1607_recOwned;
                      isErased = _1608_recErased;
                      readIdents = _1609_recIdents;
                    }
                  } else if (_source59.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1610_recursiveGen;
                      bool _1611_recOwned;
                      bool _1612_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1007;
                      bool _out1008;
                      bool _out1009;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1007, out _out1008, out _out1009, out _out1010);
                      _1610_recursiveGen = _out1007;
                      _1611_recOwned = _out1008;
                      _1612_recErased = _out1009;
                      _1613_recIdents = _out1010;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1610_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1611_recOwned;
                      isErased = _1612_recErased;
                      readIdents = _1613_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1614_recursiveGen;
                      bool _1615_recOwned;
                      bool _1616_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1617_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1011;
                      bool _out1012;
                      bool _out1013;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1011, out _out1012, out _out1013, out _out1014);
                      _1614_recursiveGen = _out1011;
                      _1615_recOwned = _out1012;
                      _1616_recErased = _out1013;
                      _1617_recIdents = _out1014;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1614_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1615_recOwned;
                      isErased = _1616_recErased;
                      readIdents = _1617_recIdents;
                    }
                  }
                } else if (_source57.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1618___mcc_h861 = _source57.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1619_recursiveGen;
                    bool _1620_recOwned;
                    bool _1621_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1622_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1015;
                    bool _out1016;
                    bool _out1017;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1018;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1015, out _out1016, out _out1017, out _out1018);
                    _1619_recursiveGen = _out1015;
                    _1620_recOwned = _out1016;
                    _1621_recErased = _out1017;
                    _1622_recIdents = _out1018;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1619_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1620_recOwned;
                    isErased = _1621_recErased;
                    readIdents = _1622_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1623___mcc_h863 = _source57.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1624_recursiveGen;
                    bool _1625_recOwned;
                    bool _1626_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1627_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1019;
                    bool _out1020;
                    bool _out1021;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1019, out _out1020, out _out1021, out _out1022);
                    _1624_recursiveGen = _out1019;
                    _1625_recOwned = _out1020;
                    _1626_recErased = _out1021;
                    _1627_recIdents = _out1022;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1624_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1625_recOwned;
                    isErased = _1626_recErased;
                    readIdents = _1627_recIdents;
                  }
                }
              } else if (_source53.is_String) {
                DAST._IType _source60 = _541___mcc_h262;
                if (_source60.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1628___mcc_h865 = _source60.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1629___mcc_h866 = _source60.dtor_typeArgs;
                  DAST._IResolvedType _1630___mcc_h867 = _source60.dtor_resolved;
                  DAST._IResolvedType _source61 = _1630___mcc_h867;
                  if (_source61.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1631___mcc_h871 = _source61.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1632_recursiveGen;
                      bool _1633_recOwned;
                      bool _1634_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1635_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1023;
                      bool _out1024;
                      bool _out1025;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1023, out _out1024, out _out1025, out _out1026);
                      _1632_recursiveGen = _out1023;
                      _1633_recOwned = _out1024;
                      _1634_recErased = _out1025;
                      _1635_recIdents = _out1026;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1632_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1633_recOwned;
                      isErased = _1634_recErased;
                      readIdents = _1635_recIdents;
                    }
                  } else if (_source61.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1636___mcc_h873 = _source61.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1637_recursiveGen;
                      bool _1638_recOwned;
                      bool _1639_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1640_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1027;
                      bool _out1028;
                      bool _out1029;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1030;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1027, out _out1028, out _out1029, out _out1030);
                      _1637_recursiveGen = _out1027;
                      _1638_recOwned = _out1028;
                      _1639_recErased = _out1029;
                      _1640_recIdents = _out1030;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1637_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1638_recOwned;
                      isErased = _1639_recErased;
                      readIdents = _1640_recIdents;
                    }
                  } else {
                    DAST._IType _1641___mcc_h875 = _source61.dtor_Newtype_a0;
                    DAST._IType _1642_b = _1641___mcc_h875;
                    {
                      if (object.Equals(_534_fromTpe, _1642_b)) {
                        Dafny.ISequence<Dafny.Rune> _1643_recursiveGen;
                        bool _1644_recOwned;
                        bool _1645_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1646_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1031;
                        bool _out1032;
                        bool _out1033;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1031, out _out1032, out _out1033, out _out1034);
                        _1643_recursiveGen = _out1031;
                        _1644_recOwned = _out1032;
                        _1645_recErased = _out1033;
                        _1646_recIdents = _out1034;
                        Dafny.ISequence<Dafny.Rune> _1647_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1035;
                        _out1035 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _1647_rhsType = _out1035;
                        Dafny.ISequence<Dafny.Rune> _1648_uneraseFn;
                        _1648_uneraseFn = ((_1644_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1647_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1648_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1643_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1644_recOwned;
                        isErased = false;
                        readIdents = _1646_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1036;
                        bool _out1037;
                        bool _out1038;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1039;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1642_b), _1642_b, _533_toTpe), selfIdent, @params, mustOwn, out _out1036, out _out1037, out _out1038, out _out1039);
                        s = _out1036;
                        isOwned = _out1037;
                        isErased = _out1038;
                        readIdents = _out1039;
                      }
                    }
                  }
                } else if (_source60.is_Nullable) {
                  DAST._IType _1649___mcc_h877 = _source60.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1650_recursiveGen;
                    bool _1651_recOwned;
                    bool _1652_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1653_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1040;
                    bool _out1041;
                    bool _out1042;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1040, out _out1041, out _out1042, out _out1043);
                    _1650_recursiveGen = _out1040;
                    _1651_recOwned = _out1041;
                    _1652_recErased = _out1042;
                    _1653_recIdents = _out1043;
                    if (!(_1651_recOwned)) {
                      _1650_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1650_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1650_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1652_recErased;
                    readIdents = _1653_recIdents;
                  }
                } else if (_source60.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1654___mcc_h879 = _source60.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1655_recursiveGen;
                    bool _1656_recOwned;
                    bool _1657_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1658_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1044;
                    bool _out1045;
                    bool _out1046;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1047;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1044, out _out1045, out _out1046, out _out1047);
                    _1655_recursiveGen = _out1044;
                    _1656_recOwned = _out1045;
                    _1657_recErased = _out1046;
                    _1658_recIdents = _out1047;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1655_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1656_recOwned;
                    isErased = _1657_recErased;
                    readIdents = _1658_recIdents;
                  }
                } else if (_source60.is_Array) {
                  DAST._IType _1659___mcc_h881 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1660_recursiveGen;
                    bool _1661_recOwned;
                    bool _1662_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1663_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1048;
                    bool _out1049;
                    bool _out1050;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1051;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1048, out _out1049, out _out1050, out _out1051);
                    _1660_recursiveGen = _out1048;
                    _1661_recOwned = _out1049;
                    _1662_recErased = _out1050;
                    _1663_recIdents = _out1051;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1660_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1661_recOwned;
                    isErased = _1662_recErased;
                    readIdents = _1663_recIdents;
                  }
                } else if (_source60.is_Seq) {
                  DAST._IType _1664___mcc_h883 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1665_recursiveGen;
                    bool _1666_recOwned;
                    bool _1667_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1668_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1052;
                    bool _out1053;
                    bool _out1054;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1052, out _out1053, out _out1054, out _out1055);
                    _1665_recursiveGen = _out1052;
                    _1666_recOwned = _out1053;
                    _1667_recErased = _out1054;
                    _1668_recIdents = _out1055;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1665_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1666_recOwned;
                    isErased = _1667_recErased;
                    readIdents = _1668_recIdents;
                  }
                } else if (_source60.is_Set) {
                  DAST._IType _1669___mcc_h885 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1670_recursiveGen;
                    bool _1671_recOwned;
                    bool _1672_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1673_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1056;
                    bool _out1057;
                    bool _out1058;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1059;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1056, out _out1057, out _out1058, out _out1059);
                    _1670_recursiveGen = _out1056;
                    _1671_recOwned = _out1057;
                    _1672_recErased = _out1058;
                    _1673_recIdents = _out1059;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1670_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1671_recOwned;
                    isErased = _1672_recErased;
                    readIdents = _1673_recIdents;
                  }
                } else if (_source60.is_Multiset) {
                  DAST._IType _1674___mcc_h887 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1675_recursiveGen;
                    bool _1676_recOwned;
                    bool _1677_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1678_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1060;
                    bool _out1061;
                    bool _out1062;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1063;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1060, out _out1061, out _out1062, out _out1063);
                    _1675_recursiveGen = _out1060;
                    _1676_recOwned = _out1061;
                    _1677_recErased = _out1062;
                    _1678_recIdents = _out1063;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1675_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1676_recOwned;
                    isErased = _1677_recErased;
                    readIdents = _1678_recIdents;
                  }
                } else if (_source60.is_Map) {
                  DAST._IType _1679___mcc_h889 = _source60.dtor_key;
                  DAST._IType _1680___mcc_h890 = _source60.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1681_recursiveGen;
                    bool _1682_recOwned;
                    bool _1683_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1684_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1064;
                    bool _out1065;
                    bool _out1066;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1064, out _out1065, out _out1066, out _out1067);
                    _1681_recursiveGen = _out1064;
                    _1682_recOwned = _out1065;
                    _1683_recErased = _out1066;
                    _1684_recIdents = _out1067;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1681_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1682_recOwned;
                    isErased = _1683_recErased;
                    readIdents = _1684_recIdents;
                  }
                } else if (_source60.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1685___mcc_h893 = _source60.dtor_args;
                  DAST._IType _1686___mcc_h894 = _source60.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1687_recursiveGen;
                    bool _1688_recOwned;
                    bool _1689_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1690_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1068;
                    bool _out1069;
                    bool _out1070;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1071;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1068, out _out1069, out _out1070, out _out1071);
                    _1687_recursiveGen = _out1068;
                    _1688_recOwned = _out1069;
                    _1689_recErased = _out1070;
                    _1690_recIdents = _out1071;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1687_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1688_recOwned;
                    isErased = _1689_recErased;
                    readIdents = _1690_recIdents;
                  }
                } else if (_source60.is_Primitive) {
                  DAST._IPrimitive _1691___mcc_h897 = _source60.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1692_recursiveGen;
                    bool _1693_recOwned;
                    bool _1694_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1695_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1072;
                    bool _out1073;
                    bool _out1074;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1075;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1072, out _out1073, out _out1074, out _out1075);
                    _1692_recursiveGen = _out1072;
                    _1693_recOwned = _out1073;
                    _1694_recErased = _out1074;
                    _1695_recIdents = _out1075;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1692_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1693_recOwned;
                    isErased = _1694_recErased;
                    readIdents = _1695_recIdents;
                  }
                } else if (_source60.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1696___mcc_h899 = _source60.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1697_recursiveGen;
                    bool _1698_recOwned;
                    bool _1699_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1700_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1076;
                    bool _out1077;
                    bool _out1078;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1076, out _out1077, out _out1078, out _out1079);
                    _1697_recursiveGen = _out1076;
                    _1698_recOwned = _out1077;
                    _1699_recErased = _out1078;
                    _1700_recIdents = _out1079;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1697_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1698_recOwned;
                    isErased = _1699_recErased;
                    readIdents = _1700_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1701___mcc_h901 = _source60.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1702_recursiveGen;
                    bool _1703_recOwned;
                    bool _1704_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1705_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1080;
                    bool _out1081;
                    bool _out1082;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1083;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1080, out _out1081, out _out1082, out _out1083);
                    _1702_recursiveGen = _out1080;
                    _1703_recOwned = _out1081;
                    _1704_recErased = _out1082;
                    _1705_recIdents = _out1083;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1702_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1703_recOwned;
                    isErased = _1704_recErased;
                    readIdents = _1705_recIdents;
                  }
                }
              } else if (_source53.is_Bool) {
                DAST._IType _source62 = _541___mcc_h262;
                if (_source62.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1706___mcc_h903 = _source62.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1707___mcc_h904 = _source62.dtor_typeArgs;
                  DAST._IResolvedType _1708___mcc_h905 = _source62.dtor_resolved;
                  DAST._IResolvedType _source63 = _1708___mcc_h905;
                  if (_source63.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1709___mcc_h909 = _source63.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1710_recursiveGen;
                      bool _1711_recOwned;
                      bool _1712_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1713_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1084;
                      bool _out1085;
                      bool _out1086;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1087;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1084, out _out1085, out _out1086, out _out1087);
                      _1710_recursiveGen = _out1084;
                      _1711_recOwned = _out1085;
                      _1712_recErased = _out1086;
                      _1713_recIdents = _out1087;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1710_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1711_recOwned;
                      isErased = _1712_recErased;
                      readIdents = _1713_recIdents;
                    }
                  } else if (_source63.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1714___mcc_h911 = _source63.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1715_recursiveGen;
                      bool _1716_recOwned;
                      bool _1717_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1718_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1088;
                      bool _out1089;
                      bool _out1090;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1088, out _out1089, out _out1090, out _out1091);
                      _1715_recursiveGen = _out1088;
                      _1716_recOwned = _out1089;
                      _1717_recErased = _out1090;
                      _1718_recIdents = _out1091;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1715_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1716_recOwned;
                      isErased = _1717_recErased;
                      readIdents = _1718_recIdents;
                    }
                  } else {
                    DAST._IType _1719___mcc_h913 = _source63.dtor_Newtype_a0;
                    DAST._IType _1720_b = _1719___mcc_h913;
                    {
                      if (object.Equals(_534_fromTpe, _1720_b)) {
                        Dafny.ISequence<Dafny.Rune> _1721_recursiveGen;
                        bool _1722_recOwned;
                        bool _1723_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1092;
                        bool _out1093;
                        bool _out1094;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1095;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1092, out _out1093, out _out1094, out _out1095);
                        _1721_recursiveGen = _out1092;
                        _1722_recOwned = _out1093;
                        _1723_recErased = _out1094;
                        _1724_recIdents = _out1095;
                        Dafny.ISequence<Dafny.Rune> _1725_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1096;
                        _out1096 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _1725_rhsType = _out1096;
                        Dafny.ISequence<Dafny.Rune> _1726_uneraseFn;
                        _1726_uneraseFn = ((_1722_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1725_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1726_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1721_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1722_recOwned;
                        isErased = false;
                        readIdents = _1724_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1097;
                        bool _out1098;
                        bool _out1099;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1720_b), _1720_b, _533_toTpe), selfIdent, @params, mustOwn, out _out1097, out _out1098, out _out1099, out _out1100);
                        s = _out1097;
                        isOwned = _out1098;
                        isErased = _out1099;
                        readIdents = _out1100;
                      }
                    }
                  }
                } else if (_source62.is_Nullable) {
                  DAST._IType _1727___mcc_h915 = _source62.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1728_recursiveGen;
                    bool _1729_recOwned;
                    bool _1730_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1731_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1101;
                    bool _out1102;
                    bool _out1103;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1104;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1101, out _out1102, out _out1103, out _out1104);
                    _1728_recursiveGen = _out1101;
                    _1729_recOwned = _out1102;
                    _1730_recErased = _out1103;
                    _1731_recIdents = _out1104;
                    if (!(_1729_recOwned)) {
                      _1728_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1728_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1728_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1730_recErased;
                    readIdents = _1731_recIdents;
                  }
                } else if (_source62.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1732___mcc_h917 = _source62.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1733_recursiveGen;
                    bool _1734_recOwned;
                    bool _1735_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1105;
                    bool _out1106;
                    bool _out1107;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1108;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1105, out _out1106, out _out1107, out _out1108);
                    _1733_recursiveGen = _out1105;
                    _1734_recOwned = _out1106;
                    _1735_recErased = _out1107;
                    _1736_recIdents = _out1108;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1733_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1734_recOwned;
                    isErased = _1735_recErased;
                    readIdents = _1736_recIdents;
                  }
                } else if (_source62.is_Array) {
                  DAST._IType _1737___mcc_h919 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1738_recursiveGen;
                    bool _1739_recOwned;
                    bool _1740_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1741_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1109;
                    bool _out1110;
                    bool _out1111;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1109, out _out1110, out _out1111, out _out1112);
                    _1738_recursiveGen = _out1109;
                    _1739_recOwned = _out1110;
                    _1740_recErased = _out1111;
                    _1741_recIdents = _out1112;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1738_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1739_recOwned;
                    isErased = _1740_recErased;
                    readIdents = _1741_recIdents;
                  }
                } else if (_source62.is_Seq) {
                  DAST._IType _1742___mcc_h921 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1743_recursiveGen;
                    bool _1744_recOwned;
                    bool _1745_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1746_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1113;
                    bool _out1114;
                    bool _out1115;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1116;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1113, out _out1114, out _out1115, out _out1116);
                    _1743_recursiveGen = _out1113;
                    _1744_recOwned = _out1114;
                    _1745_recErased = _out1115;
                    _1746_recIdents = _out1116;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1743_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1744_recOwned;
                    isErased = _1745_recErased;
                    readIdents = _1746_recIdents;
                  }
                } else if (_source62.is_Set) {
                  DAST._IType _1747___mcc_h923 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1748_recursiveGen;
                    bool _1749_recOwned;
                    bool _1750_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1751_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1117;
                    bool _out1118;
                    bool _out1119;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1120;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1117, out _out1118, out _out1119, out _out1120);
                    _1748_recursiveGen = _out1117;
                    _1749_recOwned = _out1118;
                    _1750_recErased = _out1119;
                    _1751_recIdents = _out1120;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1748_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1749_recOwned;
                    isErased = _1750_recErased;
                    readIdents = _1751_recIdents;
                  }
                } else if (_source62.is_Multiset) {
                  DAST._IType _1752___mcc_h925 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1753_recursiveGen;
                    bool _1754_recOwned;
                    bool _1755_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1756_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1121;
                    bool _out1122;
                    bool _out1123;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1121, out _out1122, out _out1123, out _out1124);
                    _1753_recursiveGen = _out1121;
                    _1754_recOwned = _out1122;
                    _1755_recErased = _out1123;
                    _1756_recIdents = _out1124;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1753_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1754_recOwned;
                    isErased = _1755_recErased;
                    readIdents = _1756_recIdents;
                  }
                } else if (_source62.is_Map) {
                  DAST._IType _1757___mcc_h927 = _source62.dtor_key;
                  DAST._IType _1758___mcc_h928 = _source62.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1759_recursiveGen;
                    bool _1760_recOwned;
                    bool _1761_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1762_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1125;
                    bool _out1126;
                    bool _out1127;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1125, out _out1126, out _out1127, out _out1128);
                    _1759_recursiveGen = _out1125;
                    _1760_recOwned = _out1126;
                    _1761_recErased = _out1127;
                    _1762_recIdents = _out1128;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1759_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1760_recOwned;
                    isErased = _1761_recErased;
                    readIdents = _1762_recIdents;
                  }
                } else if (_source62.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1763___mcc_h931 = _source62.dtor_args;
                  DAST._IType _1764___mcc_h932 = _source62.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1765_recursiveGen;
                    bool _1766_recOwned;
                    bool _1767_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1768_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1129;
                    bool _out1130;
                    bool _out1131;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1132;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1129, out _out1130, out _out1131, out _out1132);
                    _1765_recursiveGen = _out1129;
                    _1766_recOwned = _out1130;
                    _1767_recErased = _out1131;
                    _1768_recIdents = _out1132;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1765_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1766_recOwned;
                    isErased = _1767_recErased;
                    readIdents = _1768_recIdents;
                  }
                } else if (_source62.is_Primitive) {
                  DAST._IPrimitive _1769___mcc_h935 = _source62.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1770_recursiveGen;
                    bool _1771_recOwned;
                    bool _1772_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1773_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1133;
                    bool _out1134;
                    bool _out1135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1133, out _out1134, out _out1135, out _out1136);
                    _1770_recursiveGen = _out1133;
                    _1771_recOwned = _out1134;
                    _1772_recErased = _out1135;
                    _1773_recIdents = _out1136;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1770_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1771_recOwned;
                    isErased = _1772_recErased;
                    readIdents = _1773_recIdents;
                  }
                } else if (_source62.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1774___mcc_h937 = _source62.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1775_recursiveGen;
                    bool _1776_recOwned;
                    bool _1777_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1137;
                    bool _out1138;
                    bool _out1139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1140;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1137, out _out1138, out _out1139, out _out1140);
                    _1775_recursiveGen = _out1137;
                    _1776_recOwned = _out1138;
                    _1777_recErased = _out1139;
                    _1778_recIdents = _out1140;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1775_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1776_recOwned;
                    isErased = _1777_recErased;
                    readIdents = _1778_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1779___mcc_h939 = _source62.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1780_recursiveGen;
                    bool _1781_recOwned;
                    bool _1782_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1783_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1141;
                    bool _out1142;
                    bool _out1143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1144;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1141, out _out1142, out _out1143, out _out1144);
                    _1780_recursiveGen = _out1141;
                    _1781_recOwned = _out1142;
                    _1782_recErased = _out1143;
                    _1783_recIdents = _out1144;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1780_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1781_recOwned;
                    isErased = _1782_recErased;
                    readIdents = _1783_recIdents;
                  }
                }
              } else {
                DAST._IType _source64 = _541___mcc_h262;
                if (_source64.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1784___mcc_h941 = _source64.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1785___mcc_h942 = _source64.dtor_typeArgs;
                  DAST._IResolvedType _1786___mcc_h943 = _source64.dtor_resolved;
                  DAST._IResolvedType _source65 = _1786___mcc_h943;
                  if (_source65.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1787___mcc_h947 = _source65.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1788_recursiveGen;
                      bool _1789_recOwned;
                      bool _1790_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1791_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1145;
                      bool _out1146;
                      bool _out1147;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1145, out _out1146, out _out1147, out _out1148);
                      _1788_recursiveGen = _out1145;
                      _1789_recOwned = _out1146;
                      _1790_recErased = _out1147;
                      _1791_recIdents = _out1148;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1788_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1789_recOwned;
                      isErased = _1790_recErased;
                      readIdents = _1791_recIdents;
                    }
                  } else if (_source65.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1792___mcc_h949 = _source65.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1793_recursiveGen;
                      bool _1794_recOwned;
                      bool _1795_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1796_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1149;
                      bool _out1150;
                      bool _out1151;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1152;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1149, out _out1150, out _out1151, out _out1152);
                      _1793_recursiveGen = _out1149;
                      _1794_recOwned = _out1150;
                      _1795_recErased = _out1151;
                      _1796_recIdents = _out1152;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1793_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1794_recOwned;
                      isErased = _1795_recErased;
                      readIdents = _1796_recIdents;
                    }
                  } else {
                    DAST._IType _1797___mcc_h951 = _source65.dtor_Newtype_a0;
                    DAST._IType _1798_b = _1797___mcc_h951;
                    {
                      if (object.Equals(_534_fromTpe, _1798_b)) {
                        Dafny.ISequence<Dafny.Rune> _1799_recursiveGen;
                        bool _1800_recOwned;
                        bool _1801_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1802_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1153;
                        bool _out1154;
                        bool _out1155;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1156;
                        DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1153, out _out1154, out _out1155, out _out1156);
                        _1799_recursiveGen = _out1153;
                        _1800_recOwned = _out1154;
                        _1801_recErased = _out1155;
                        _1802_recIdents = _out1156;
                        Dafny.ISequence<Dafny.Rune> _1803_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1157;
                        _out1157 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                        _1803_rhsType = _out1157;
                        Dafny.ISequence<Dafny.Rune> _1804_uneraseFn;
                        _1804_uneraseFn = ((_1800_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1803_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1804_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1799_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1800_recOwned;
                        isErased = false;
                        readIdents = _1802_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1158;
                        bool _out1159;
                        bool _out1160;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1161;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1798_b), _1798_b, _533_toTpe), selfIdent, @params, mustOwn, out _out1158, out _out1159, out _out1160, out _out1161);
                        s = _out1158;
                        isOwned = _out1159;
                        isErased = _out1160;
                        readIdents = _out1161;
                      }
                    }
                  }
                } else if (_source64.is_Nullable) {
                  DAST._IType _1805___mcc_h953 = _source64.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1806_recursiveGen;
                    bool _1807_recOwned;
                    bool _1808_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1162;
                    bool _out1163;
                    bool _out1164;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1165;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1162, out _out1163, out _out1164, out _out1165);
                    _1806_recursiveGen = _out1162;
                    _1807_recOwned = _out1163;
                    _1808_recErased = _out1164;
                    _1809_recIdents = _out1165;
                    if (!(_1807_recOwned)) {
                      _1806_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1806_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1806_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1808_recErased;
                    readIdents = _1809_recIdents;
                  }
                } else if (_source64.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1810___mcc_h955 = _source64.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1811_recursiveGen;
                    bool _1812_recOwned;
                    bool _1813_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1814_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1166;
                    bool _out1167;
                    bool _out1168;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1166, out _out1167, out _out1168, out _out1169);
                    _1811_recursiveGen = _out1166;
                    _1812_recOwned = _out1167;
                    _1813_recErased = _out1168;
                    _1814_recIdents = _out1169;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1811_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1812_recOwned;
                    isErased = _1813_recErased;
                    readIdents = _1814_recIdents;
                  }
                } else if (_source64.is_Array) {
                  DAST._IType _1815___mcc_h957 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1816_recursiveGen;
                    bool _1817_recOwned;
                    bool _1818_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1819_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1170;
                    bool _out1171;
                    bool _out1172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1173;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1170, out _out1171, out _out1172, out _out1173);
                    _1816_recursiveGen = _out1170;
                    _1817_recOwned = _out1171;
                    _1818_recErased = _out1172;
                    _1819_recIdents = _out1173;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1816_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1817_recOwned;
                    isErased = _1818_recErased;
                    readIdents = _1819_recIdents;
                  }
                } else if (_source64.is_Seq) {
                  DAST._IType _1820___mcc_h959 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1821_recursiveGen;
                    bool _1822_recOwned;
                    bool _1823_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1824_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1174;
                    bool _out1175;
                    bool _out1176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1177;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1174, out _out1175, out _out1176, out _out1177);
                    _1821_recursiveGen = _out1174;
                    _1822_recOwned = _out1175;
                    _1823_recErased = _out1176;
                    _1824_recIdents = _out1177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1821_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1822_recOwned;
                    isErased = _1823_recErased;
                    readIdents = _1824_recIdents;
                  }
                } else if (_source64.is_Set) {
                  DAST._IType _1825___mcc_h961 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1826_recursiveGen;
                    bool _1827_recOwned;
                    bool _1828_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1829_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1178;
                    bool _out1179;
                    bool _out1180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1178, out _out1179, out _out1180, out _out1181);
                    _1826_recursiveGen = _out1178;
                    _1827_recOwned = _out1179;
                    _1828_recErased = _out1180;
                    _1829_recIdents = _out1181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1826_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1827_recOwned;
                    isErased = _1828_recErased;
                    readIdents = _1829_recIdents;
                  }
                } else if (_source64.is_Multiset) {
                  DAST._IType _1830___mcc_h963 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1831_recursiveGen;
                    bool _1832_recOwned;
                    bool _1833_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1834_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1182;
                    bool _out1183;
                    bool _out1184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1185;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1182, out _out1183, out _out1184, out _out1185);
                    _1831_recursiveGen = _out1182;
                    _1832_recOwned = _out1183;
                    _1833_recErased = _out1184;
                    _1834_recIdents = _out1185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1831_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1832_recOwned;
                    isErased = _1833_recErased;
                    readIdents = _1834_recIdents;
                  }
                } else if (_source64.is_Map) {
                  DAST._IType _1835___mcc_h965 = _source64.dtor_key;
                  DAST._IType _1836___mcc_h966 = _source64.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1837_recursiveGen;
                    bool _1838_recOwned;
                    bool _1839_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1840_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1186;
                    bool _out1187;
                    bool _out1188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1189;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1186, out _out1187, out _out1188, out _out1189);
                    _1837_recursiveGen = _out1186;
                    _1838_recOwned = _out1187;
                    _1839_recErased = _out1188;
                    _1840_recIdents = _out1189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1837_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1838_recOwned;
                    isErased = _1839_recErased;
                    readIdents = _1840_recIdents;
                  }
                } else if (_source64.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1841___mcc_h969 = _source64.dtor_args;
                  DAST._IType _1842___mcc_h970 = _source64.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1843_recursiveGen;
                    bool _1844_recOwned;
                    bool _1845_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1846_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1190;
                    bool _out1191;
                    bool _out1192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1190, out _out1191, out _out1192, out _out1193);
                    _1843_recursiveGen = _out1190;
                    _1844_recOwned = _out1191;
                    _1845_recErased = _out1192;
                    _1846_recIdents = _out1193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1843_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1844_recOwned;
                    isErased = _1845_recErased;
                    readIdents = _1846_recIdents;
                  }
                } else if (_source64.is_Primitive) {
                  DAST._IPrimitive _1847___mcc_h973 = _source64.dtor_Primitive_a0;
                  DAST._IPrimitive _source66 = _1847___mcc_h973;
                  if (_source66.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1848_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1194;
                      _out1194 = DCOMP.COMP.GenType(_534_fromTpe, true, false);
                      _1848_rhsType = _out1194;
                      Dafny.ISequence<Dafny.Rune> _1849_recursiveGen;
                      bool _1850___v59;
                      bool _1851___v60;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1852_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1195;
                      bool _out1196;
                      bool _out1197;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1198;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, true, out _out1195, out _out1196, out _out1197, out _out1198);
                      _1849_recursiveGen = _out1195;
                      _1850___v59 = _out1196;
                      _1851___v60 = _out1197;
                      _1852_recIdents = _out1198;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1849_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1852_recIdents;
                    }
                  } else if (_source66.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1853_recursiveGen;
                      bool _1854_recOwned;
                      bool _1855_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1856_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1199;
                      bool _out1200;
                      bool _out1201;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1199, out _out1200, out _out1201, out _out1202);
                      _1853_recursiveGen = _out1199;
                      _1854_recOwned = _out1200;
                      _1855_recErased = _out1201;
                      _1856_recIdents = _out1202;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1853_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1854_recOwned;
                      isErased = _1855_recErased;
                      readIdents = _1856_recIdents;
                    }
                  } else if (_source66.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1857_recursiveGen;
                      bool _1858_recOwned;
                      bool _1859_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1860_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1203;
                      bool _out1204;
                      bool _out1205;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1206;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1203, out _out1204, out _out1205, out _out1206);
                      _1857_recursiveGen = _out1203;
                      _1858_recOwned = _out1204;
                      _1859_recErased = _out1205;
                      _1860_recIdents = _out1206;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1857_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1858_recOwned;
                      isErased = _1859_recErased;
                      readIdents = _1860_recIdents;
                    }
                  } else if (_source66.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1861_recursiveGen;
                      bool _1862_recOwned;
                      bool _1863_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1864_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1207;
                      bool _out1208;
                      bool _out1209;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1210;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1207, out _out1208, out _out1209, out _out1210);
                      _1861_recursiveGen = _out1207;
                      _1862_recOwned = _out1208;
                      _1863_recErased = _out1209;
                      _1864_recIdents = _out1210;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1861_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1862_recOwned;
                      isErased = _1863_recErased;
                      readIdents = _1864_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1865_recursiveGen;
                      bool _1866_recOwned;
                      bool _1867_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1868_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1211;
                      bool _out1212;
                      bool _out1213;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1211, out _out1212, out _out1213, out _out1214);
                      _1865_recursiveGen = _out1211;
                      _1866_recOwned = _out1212;
                      _1867_recErased = _out1213;
                      _1868_recIdents = _out1214;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1865_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1866_recOwned;
                      isErased = _1867_recErased;
                      readIdents = _1868_recIdents;
                    }
                  }
                } else if (_source64.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1869___mcc_h975 = _source64.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1870_recursiveGen;
                    bool _1871_recOwned;
                    bool _1872_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1873_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1215;
                    bool _out1216;
                    bool _out1217;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1218;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1215, out _out1216, out _out1217, out _out1218);
                    _1870_recursiveGen = _out1215;
                    _1871_recOwned = _out1216;
                    _1872_recErased = _out1217;
                    _1873_recIdents = _out1218;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1870_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1871_recOwned;
                    isErased = _1872_recErased;
                    readIdents = _1873_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1874___mcc_h977 = _source64.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1875_recursiveGen;
                    bool _1876_recOwned;
                    bool _1877_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1878_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1219;
                    bool _out1220;
                    bool _out1221;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1222;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1219, out _out1220, out _out1221, out _out1222);
                    _1875_recursiveGen = _out1219;
                    _1876_recOwned = _out1220;
                    _1877_recErased = _out1221;
                    _1878_recIdents = _out1222;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1875_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1876_recOwned;
                    isErased = _1877_recErased;
                    readIdents = _1878_recIdents;
                  }
                }
              }
            } else if (_source29.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1879___mcc_h979 = _source29.dtor_Passthrough_a0;
              DAST._IType _source67 = _541___mcc_h262;
              if (_source67.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1880___mcc_h983 = _source67.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1881___mcc_h984 = _source67.dtor_typeArgs;
                DAST._IResolvedType _1882___mcc_h985 = _source67.dtor_resolved;
                DAST._IResolvedType _source68 = _1882___mcc_h985;
                if (_source68.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1883___mcc_h989 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1884_recursiveGen;
                    bool _1885_recOwned;
                    bool _1886_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1887_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1223;
                    bool _out1224;
                    bool _out1225;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1223, out _out1224, out _out1225, out _out1226);
                    _1884_recursiveGen = _out1223;
                    _1885_recOwned = _out1224;
                    _1886_recErased = _out1225;
                    _1887_recIdents = _out1226;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1884_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1885_recOwned;
                    isErased = _1886_recErased;
                    readIdents = _1887_recIdents;
                  }
                } else if (_source68.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1888___mcc_h991 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1889_recursiveGen;
                    bool _1890_recOwned;
                    bool _1891_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1892_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1227;
                    bool _out1228;
                    bool _out1229;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1230;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1227, out _out1228, out _out1229, out _out1230);
                    _1889_recursiveGen = _out1227;
                    _1890_recOwned = _out1228;
                    _1891_recErased = _out1229;
                    _1892_recIdents = _out1230;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1889_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1890_recOwned;
                    isErased = _1891_recErased;
                    readIdents = _1892_recIdents;
                  }
                } else {
                  DAST._IType _1893___mcc_h993 = _source68.dtor_Newtype_a0;
                  DAST._IType _1894_b = _1893___mcc_h993;
                  {
                    if (object.Equals(_534_fromTpe, _1894_b)) {
                      Dafny.ISequence<Dafny.Rune> _1895_recursiveGen;
                      bool _1896_recOwned;
                      bool _1897_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1898_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1231;
                      bool _out1232;
                      bool _out1233;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1234;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1231, out _out1232, out _out1233, out _out1234);
                      _1895_recursiveGen = _out1231;
                      _1896_recOwned = _out1232;
                      _1897_recErased = _out1233;
                      _1898_recIdents = _out1234;
                      Dafny.ISequence<Dafny.Rune> _1899_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1235;
                      _out1235 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1899_rhsType = _out1235;
                      Dafny.ISequence<Dafny.Rune> _1900_uneraseFn;
                      _1900_uneraseFn = ((_1896_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1899_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1900_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1895_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1896_recOwned;
                      isErased = false;
                      readIdents = _1898_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1236;
                      bool _out1237;
                      bool _out1238;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1239;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1894_b), _1894_b, _533_toTpe), selfIdent, @params, mustOwn, out _out1236, out _out1237, out _out1238, out _out1239);
                      s = _out1236;
                      isOwned = _out1237;
                      isErased = _out1238;
                      readIdents = _out1239;
                    }
                  }
                }
              } else if (_source67.is_Nullable) {
                DAST._IType _1901___mcc_h995 = _source67.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1902_recursiveGen;
                  bool _1903_recOwned;
                  bool _1904_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1905_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1240;
                  bool _out1241;
                  bool _out1242;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1240, out _out1241, out _out1242, out _out1243);
                  _1902_recursiveGen = _out1240;
                  _1903_recOwned = _out1241;
                  _1904_recErased = _out1242;
                  _1905_recIdents = _out1243;
                  if (!(_1903_recOwned)) {
                    _1902_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1902_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1902_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1904_recErased;
                  readIdents = _1905_recIdents;
                }
              } else if (_source67.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1906___mcc_h997 = _source67.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1907_recursiveGen;
                  bool _1908_recOwned;
                  bool _1909_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1910_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1244;
                  bool _out1245;
                  bool _out1246;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1244, out _out1245, out _out1246, out _out1247);
                  _1907_recursiveGen = _out1244;
                  _1908_recOwned = _out1245;
                  _1909_recErased = _out1246;
                  _1910_recIdents = _out1247;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1907_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1908_recOwned;
                  isErased = _1909_recErased;
                  readIdents = _1910_recIdents;
                }
              } else if (_source67.is_Array) {
                DAST._IType _1911___mcc_h999 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1912_recursiveGen;
                  bool _1913_recOwned;
                  bool _1914_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1915_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1248;
                  bool _out1249;
                  bool _out1250;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1248, out _out1249, out _out1250, out _out1251);
                  _1912_recursiveGen = _out1248;
                  _1913_recOwned = _out1249;
                  _1914_recErased = _out1250;
                  _1915_recIdents = _out1251;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1912_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1913_recOwned;
                  isErased = _1914_recErased;
                  readIdents = _1915_recIdents;
                }
              } else if (_source67.is_Seq) {
                DAST._IType _1916___mcc_h1001 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1917_recursiveGen;
                  bool _1918_recOwned;
                  bool _1919_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1920_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1252;
                  bool _out1253;
                  bool _out1254;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1255;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1252, out _out1253, out _out1254, out _out1255);
                  _1917_recursiveGen = _out1252;
                  _1918_recOwned = _out1253;
                  _1919_recErased = _out1254;
                  _1920_recIdents = _out1255;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1917_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1918_recOwned;
                  isErased = _1919_recErased;
                  readIdents = _1920_recIdents;
                }
              } else if (_source67.is_Set) {
                DAST._IType _1921___mcc_h1003 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1922_recursiveGen;
                  bool _1923_recOwned;
                  bool _1924_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1925_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1256;
                  bool _out1257;
                  bool _out1258;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1256, out _out1257, out _out1258, out _out1259);
                  _1922_recursiveGen = _out1256;
                  _1923_recOwned = _out1257;
                  _1924_recErased = _out1258;
                  _1925_recIdents = _out1259;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1922_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1923_recOwned;
                  isErased = _1924_recErased;
                  readIdents = _1925_recIdents;
                }
              } else if (_source67.is_Multiset) {
                DAST._IType _1926___mcc_h1005 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1927_recursiveGen;
                  bool _1928_recOwned;
                  bool _1929_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1930_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1260;
                  bool _out1261;
                  bool _out1262;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1263;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1260, out _out1261, out _out1262, out _out1263);
                  _1927_recursiveGen = _out1260;
                  _1928_recOwned = _out1261;
                  _1929_recErased = _out1262;
                  _1930_recIdents = _out1263;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1927_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1928_recOwned;
                  isErased = _1929_recErased;
                  readIdents = _1930_recIdents;
                }
              } else if (_source67.is_Map) {
                DAST._IType _1931___mcc_h1007 = _source67.dtor_key;
                DAST._IType _1932___mcc_h1008 = _source67.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1933_recursiveGen;
                  bool _1934_recOwned;
                  bool _1935_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1936_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1264;
                  bool _out1265;
                  bool _out1266;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1267;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1264, out _out1265, out _out1266, out _out1267);
                  _1933_recursiveGen = _out1264;
                  _1934_recOwned = _out1265;
                  _1935_recErased = _out1266;
                  _1936_recIdents = _out1267;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1933_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1934_recOwned;
                  isErased = _1935_recErased;
                  readIdents = _1936_recIdents;
                }
              } else if (_source67.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1937___mcc_h1011 = _source67.dtor_args;
                DAST._IType _1938___mcc_h1012 = _source67.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1939_recursiveGen;
                  bool _1940_recOwned;
                  bool _1941_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1942_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1268;
                  bool _out1269;
                  bool _out1270;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1268, out _out1269, out _out1270, out _out1271);
                  _1939_recursiveGen = _out1268;
                  _1940_recOwned = _out1269;
                  _1941_recErased = _out1270;
                  _1942_recIdents = _out1271;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1939_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1940_recOwned;
                  isErased = _1941_recErased;
                  readIdents = _1942_recIdents;
                }
              } else if (_source67.is_Primitive) {
                DAST._IPrimitive _1943___mcc_h1015 = _source67.dtor_Primitive_a0;
                DAST._IPrimitive _source69 = _1943___mcc_h1015;
                if (_source69.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1944_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1272;
                    _out1272 = DCOMP.COMP.GenType(_534_fromTpe, true, false);
                    _1944_rhsType = _out1272;
                    Dafny.ISequence<Dafny.Rune> _1945_recursiveGen;
                    bool _1946___v55;
                    bool _1947___v56;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1948_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1273;
                    bool _out1274;
                    bool _out1275;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1276;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, true, out _out1273, out _out1274, out _out1275, out _out1276);
                    _1945_recursiveGen = _out1273;
                    _1946___v55 = _out1274;
                    _1947___v56 = _out1275;
                    _1948_recIdents = _out1276;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1945_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1948_recIdents;
                  }
                } else if (_source69.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1949_recursiveGen;
                    bool _1950_recOwned;
                    bool _1951_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1952_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1277;
                    bool _out1278;
                    bool _out1279;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1277, out _out1278, out _out1279, out _out1280);
                    _1949_recursiveGen = _out1277;
                    _1950_recOwned = _out1278;
                    _1951_recErased = _out1279;
                    _1952_recIdents = _out1280;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1949_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1950_recOwned;
                    isErased = _1951_recErased;
                    readIdents = _1952_recIdents;
                  }
                } else if (_source69.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1953_recursiveGen;
                    bool _1954_recOwned;
                    bool _1955_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1956_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1281;
                    bool _out1282;
                    bool _out1283;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1281, out _out1282, out _out1283, out _out1284);
                    _1953_recursiveGen = _out1281;
                    _1954_recOwned = _out1282;
                    _1955_recErased = _out1283;
                    _1956_recIdents = _out1284;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1953_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1954_recOwned;
                    isErased = _1955_recErased;
                    readIdents = _1956_recIdents;
                  }
                } else if (_source69.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1957_recursiveGen;
                    bool _1958_recOwned;
                    bool _1959_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1960_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1285;
                    bool _out1286;
                    bool _out1287;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1288;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1285, out _out1286, out _out1287, out _out1288);
                    _1957_recursiveGen = _out1285;
                    _1958_recOwned = _out1286;
                    _1959_recErased = _out1287;
                    _1960_recIdents = _out1288;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1957_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1958_recOwned;
                    isErased = _1959_recErased;
                    readIdents = _1960_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _1961_recursiveGen;
                    bool _1962_recOwned;
                    bool _1963_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1289;
                    bool _out1290;
                    bool _out1291;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1289, out _out1290, out _out1291, out _out1292);
                    _1961_recursiveGen = _out1289;
                    _1962_recOwned = _out1290;
                    _1963_recErased = _out1291;
                    _1964_recIdents = _out1292;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1961_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1962_recOwned;
                    isErased = _1963_recErased;
                    readIdents = _1964_recIdents;
                  }
                }
              } else if (_source67.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1965___mcc_h1017 = _source67.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1966_recursiveGen;
                  bool _1967___v63;
                  bool _1968___v64;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1969_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1293;
                  bool _out1294;
                  bool _out1295;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1296;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, true, out _out1293, out _out1294, out _out1295, out _out1296);
                  _1966_recursiveGen = _out1293;
                  _1967___v63 = _out1294;
                  _1968___v64 = _out1295;
                  _1969_recIdents = _out1296;
                  Dafny.ISequence<Dafny.Rune> _1970_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1297;
                  _out1297 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                  _1970_toTpeGen = _out1297;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _1966_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _1970_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _1969_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1971___mcc_h1019 = _source67.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1972_recursiveGen;
                  bool _1973_recOwned;
                  bool _1974_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1975_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1298;
                  bool _out1299;
                  bool _out1300;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1298, out _out1299, out _out1300, out _out1301);
                  _1972_recursiveGen = _out1298;
                  _1973_recOwned = _out1299;
                  _1974_recErased = _out1300;
                  _1975_recIdents = _out1301;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1972_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1973_recOwned;
                  isErased = _1974_recErased;
                  readIdents = _1975_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _1976___mcc_h1021 = _source29.dtor_TypeArg_a0;
              DAST._IType _source70 = _541___mcc_h262;
              if (_source70.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1977___mcc_h1025 = _source70.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1978___mcc_h1026 = _source70.dtor_typeArgs;
                DAST._IResolvedType _1979___mcc_h1027 = _source70.dtor_resolved;
                DAST._IResolvedType _source71 = _1979___mcc_h1027;
                if (_source71.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1980___mcc_h1031 = _source71.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1981_recursiveGen;
                    bool _1982_recOwned;
                    bool _1983_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1302;
                    bool _out1303;
                    bool _out1304;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1302, out _out1303, out _out1304, out _out1305);
                    _1981_recursiveGen = _out1302;
                    _1982_recOwned = _out1303;
                    _1983_recErased = _out1304;
                    _1984_recIdents = _out1305;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1981_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1982_recOwned;
                    isErased = _1983_recErased;
                    readIdents = _1984_recIdents;
                  }
                } else if (_source71.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1985___mcc_h1033 = _source71.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1986_recursiveGen;
                    bool _1987_recOwned;
                    bool _1988_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1989_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1306;
                    bool _out1307;
                    bool _out1308;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1309;
                    DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1306, out _out1307, out _out1308, out _out1309);
                    _1986_recursiveGen = _out1306;
                    _1987_recOwned = _out1307;
                    _1988_recErased = _out1308;
                    _1989_recIdents = _out1309;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1986_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1987_recOwned;
                    isErased = _1988_recErased;
                    readIdents = _1989_recIdents;
                  }
                } else {
                  DAST._IType _1990___mcc_h1035 = _source71.dtor_Newtype_a0;
                  DAST._IType _1991_b = _1990___mcc_h1035;
                  {
                    if (object.Equals(_534_fromTpe, _1991_b)) {
                      Dafny.ISequence<Dafny.Rune> _1992_recursiveGen;
                      bool _1993_recOwned;
                      bool _1994_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1995_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1310;
                      bool _out1311;
                      bool _out1312;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
                      DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1310, out _out1311, out _out1312, out _out1313);
                      _1992_recursiveGen = _out1310;
                      _1993_recOwned = _out1311;
                      _1994_recErased = _out1312;
                      _1995_recIdents = _out1313;
                      Dafny.ISequence<Dafny.Rune> _1996_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1314;
                      _out1314 = DCOMP.COMP.GenType(_533_toTpe, true, false);
                      _1996_rhsType = _out1314;
                      Dafny.ISequence<Dafny.Rune> _1997_uneraseFn;
                      _1997_uneraseFn = ((_1993_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1996_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1997_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1992_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1993_recOwned;
                      isErased = false;
                      readIdents = _1995_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1315;
                      bool _out1316;
                      bool _out1317;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1318;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_535_expr, _534_fromTpe, _1991_b), _1991_b, _533_toTpe), selfIdent, @params, mustOwn, out _out1315, out _out1316, out _out1317, out _out1318);
                      s = _out1315;
                      isOwned = _out1316;
                      isErased = _out1317;
                      readIdents = _out1318;
                    }
                  }
                }
              } else if (_source70.is_Nullable) {
                DAST._IType _1998___mcc_h1037 = _source70.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1999_recursiveGen;
                  bool _2000_recOwned;
                  bool _2001_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2002_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1319;
                  bool _out1320;
                  bool _out1321;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1319, out _out1320, out _out1321, out _out1322);
                  _1999_recursiveGen = _out1319;
                  _2000_recOwned = _out1320;
                  _2001_recErased = _out1321;
                  _2002_recIdents = _out1322;
                  if (!(_2000_recOwned)) {
                    _1999_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1999_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1999_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _2001_recErased;
                  readIdents = _2002_recIdents;
                }
              } else if (_source70.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2003___mcc_h1039 = _source70.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2004_recursiveGen;
                  bool _2005_recOwned;
                  bool _2006_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2007_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1323;
                  bool _out1324;
                  bool _out1325;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1323, out _out1324, out _out1325, out _out1326);
                  _2004_recursiveGen = _out1323;
                  _2005_recOwned = _out1324;
                  _2006_recErased = _out1325;
                  _2007_recIdents = _out1326;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2004_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2005_recOwned;
                  isErased = _2006_recErased;
                  readIdents = _2007_recIdents;
                }
              } else if (_source70.is_Array) {
                DAST._IType _2008___mcc_h1041 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2009_recursiveGen;
                  bool _2010_recOwned;
                  bool _2011_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2012_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1327;
                  bool _out1328;
                  bool _out1329;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1330;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1327, out _out1328, out _out1329, out _out1330);
                  _2009_recursiveGen = _out1327;
                  _2010_recOwned = _out1328;
                  _2011_recErased = _out1329;
                  _2012_recIdents = _out1330;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2009_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2010_recOwned;
                  isErased = _2011_recErased;
                  readIdents = _2012_recIdents;
                }
              } else if (_source70.is_Seq) {
                DAST._IType _2013___mcc_h1043 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2014_recursiveGen;
                  bool _2015_recOwned;
                  bool _2016_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2017_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1331;
                  bool _out1332;
                  bool _out1333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1331, out _out1332, out _out1333, out _out1334);
                  _2014_recursiveGen = _out1331;
                  _2015_recOwned = _out1332;
                  _2016_recErased = _out1333;
                  _2017_recIdents = _out1334;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2014_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2015_recOwned;
                  isErased = _2016_recErased;
                  readIdents = _2017_recIdents;
                }
              } else if (_source70.is_Set) {
                DAST._IType _2018___mcc_h1045 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2019_recursiveGen;
                  bool _2020_recOwned;
                  bool _2021_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2022_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1335;
                  bool _out1336;
                  bool _out1337;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1335, out _out1336, out _out1337, out _out1338);
                  _2019_recursiveGen = _out1335;
                  _2020_recOwned = _out1336;
                  _2021_recErased = _out1337;
                  _2022_recIdents = _out1338;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2019_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2020_recOwned;
                  isErased = _2021_recErased;
                  readIdents = _2022_recIdents;
                }
              } else if (_source70.is_Multiset) {
                DAST._IType _2023___mcc_h1047 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2024_recursiveGen;
                  bool _2025_recOwned;
                  bool _2026_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2027_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1339;
                  bool _out1340;
                  bool _out1341;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1342;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1339, out _out1340, out _out1341, out _out1342);
                  _2024_recursiveGen = _out1339;
                  _2025_recOwned = _out1340;
                  _2026_recErased = _out1341;
                  _2027_recIdents = _out1342;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2024_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2025_recOwned;
                  isErased = _2026_recErased;
                  readIdents = _2027_recIdents;
                }
              } else if (_source70.is_Map) {
                DAST._IType _2028___mcc_h1049 = _source70.dtor_key;
                DAST._IType _2029___mcc_h1050 = _source70.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _2030_recursiveGen;
                  bool _2031_recOwned;
                  bool _2032_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2033_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1343;
                  bool _out1344;
                  bool _out1345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1346;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1343, out _out1344, out _out1345, out _out1346);
                  _2030_recursiveGen = _out1343;
                  _2031_recOwned = _out1344;
                  _2032_recErased = _out1345;
                  _2033_recIdents = _out1346;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2030_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2031_recOwned;
                  isErased = _2032_recErased;
                  readIdents = _2033_recIdents;
                }
              } else if (_source70.is_Arrow) {
                Dafny.ISequence<DAST._IType> _2034___mcc_h1053 = _source70.dtor_args;
                DAST._IType _2035___mcc_h1054 = _source70.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _2036_recursiveGen;
                  bool _2037_recOwned;
                  bool _2038_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2039_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1347;
                  bool _out1348;
                  bool _out1349;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1350;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1347, out _out1348, out _out1349, out _out1350);
                  _2036_recursiveGen = _out1347;
                  _2037_recOwned = _out1348;
                  _2038_recErased = _out1349;
                  _2039_recIdents = _out1350;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2036_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2037_recOwned;
                  isErased = _2038_recErased;
                  readIdents = _2039_recIdents;
                }
              } else if (_source70.is_Primitive) {
                DAST._IPrimitive _2040___mcc_h1057 = _source70.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2041_recursiveGen;
                  bool _2042_recOwned;
                  bool _2043_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2044_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1351;
                  bool _out1352;
                  bool _out1353;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1351, out _out1352, out _out1353, out _out1354);
                  _2041_recursiveGen = _out1351;
                  _2042_recOwned = _out1352;
                  _2043_recErased = _out1353;
                  _2044_recIdents = _out1354;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2041_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2042_recOwned;
                  isErased = _2043_recErased;
                  readIdents = _2044_recIdents;
                }
              } else if (_source70.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _2045___mcc_h1059 = _source70.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2046_recursiveGen;
                  bool _2047_recOwned;
                  bool _2048_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2049_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1355;
                  bool _out1356;
                  bool _out1357;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1358;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1355, out _out1356, out _out1357, out _out1358);
                  _2046_recursiveGen = _out1355;
                  _2047_recOwned = _out1356;
                  _2048_recErased = _out1357;
                  _2049_recIdents = _out1358;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2046_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2047_recOwned;
                  isErased = _2048_recErased;
                  readIdents = _2049_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _2050___mcc_h1061 = _source70.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2051_recursiveGen;
                  bool _2052_recOwned;
                  bool _2053_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2054_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1359;
                  bool _out1360;
                  bool _out1361;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
                  DCOMP.COMP.GenExpr(_535_expr, selfIdent, @params, mustOwn, out _out1359, out _out1360, out _out1361, out _out1362);
                  _2051_recursiveGen = _out1359;
                  _2052_recOwned = _out1360;
                  _2053_recErased = _out1361;
                  _2054_recIdents = _out1362;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2051_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2052_recOwned;
                  isErased = _2053_recErased;
                  readIdents = _2054_recIdents;
                }
              }
            }
          }
        }
      } else if (_source22.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _2055___mcc_h22 = _source22.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2056_exprs = _2055___mcc_h22;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2057_generatedValues;
          _2057_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2058_i;
          _2058_i = BigInteger.Zero;
          bool _2059_allErased;
          _2059_allErased = true;
          while ((_2058_i) < (new BigInteger((_2056_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2060_recursiveGen;
            bool _2061___v66;
            bool _2062_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2063_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1363;
            bool _out1364;
            bool _out1365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1366;
            DCOMP.COMP.GenExpr((_2056_exprs).Select(_2058_i), selfIdent, @params, true, out _out1363, out _out1364, out _out1365, out _out1366);
            _2060_recursiveGen = _out1363;
            _2061___v66 = _out1364;
            _2062_isErased = _out1365;
            _2063_recIdents = _out1366;
            _2059_allErased = (_2059_allErased) && (_2062_isErased);
            _2057_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2057_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2060_recursiveGen, _2062_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2063_recIdents);
            _2058_i = (_2058_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2058_i = BigInteger.Zero;
          while ((_2058_i) < (new BigInteger((_2057_generatedValues).Count))) {
            if ((_2058_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2064_gen;
            _2064_gen = ((_2057_generatedValues).Select(_2058_i)).dtor__0;
            if ((((_2057_generatedValues).Select(_2058_i)).dtor__1) && (!(_2059_allErased))) {
              _2064_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2064_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2064_gen);
            _2058_i = (_2058_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _2059_allErased;
        }
      } else if (_source22.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _2065___mcc_h23 = _source22.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2066_exprs = _2065___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2067_generatedValues;
          _2067_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2068_i;
          _2068_i = BigInteger.Zero;
          bool _2069_allErased;
          _2069_allErased = true;
          while ((_2068_i) < (new BigInteger((_2066_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2070_recursiveGen;
            bool _2071___v67;
            bool _2072_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2073_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1367;
            bool _out1368;
            bool _out1369;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
            DCOMP.COMP.GenExpr((_2066_exprs).Select(_2068_i), selfIdent, @params, true, out _out1367, out _out1368, out _out1369, out _out1370);
            _2070_recursiveGen = _out1367;
            _2071___v67 = _out1368;
            _2072_isErased = _out1369;
            _2073_recIdents = _out1370;
            _2069_allErased = (_2069_allErased) && (_2072_isErased);
            _2067_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2067_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2070_recursiveGen, _2072_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2073_recIdents);
            _2068_i = (_2068_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2068_i = BigInteger.Zero;
          while ((_2068_i) < (new BigInteger((_2067_generatedValues).Count))) {
            if ((_2068_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2074_gen;
            _2074_gen = ((_2067_generatedValues).Select(_2068_i)).dtor__0;
            if ((((_2067_generatedValues).Select(_2068_i)).dtor__1) && (!(_2069_allErased))) {
              _2074_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2074_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2074_gen);
            _2068_i = (_2068_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashSet<_>>()"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_This) {
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source72 = selfIdent;
          if (_source72.is_Some) {
            Dafny.ISequence<Dafny.Rune> _2075___mcc_h1063 = _source72.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _2076_id = _2075___mcc_h1063;
            {
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(_2076_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                isOwned = true;
              } else {
                if ((_2076_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
                } else {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2076_id);
                }
                isOwned = false;
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2076_id);
              isErased = false;
            }
          } else {
            {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")");
              isOwned = true;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              isErased = true;
            }
          }
        }
      } else if (_source22.is_Ite) {
        DAST._IExpression _2077___mcc_h24 = _source22.dtor_cond;
        DAST._IExpression _2078___mcc_h25 = _source22.dtor_thn;
        DAST._IExpression _2079___mcc_h26 = _source22.dtor_els;
        DAST._IExpression _2080_f = _2079___mcc_h26;
        DAST._IExpression _2081_t = _2078___mcc_h25;
        DAST._IExpression _2082_cond = _2077___mcc_h24;
        {
          Dafny.ISequence<Dafny.Rune> _2083_condString;
          bool _2084___v68;
          bool _2085_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1371;
          bool _out1372;
          bool _out1373;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
          DCOMP.COMP.GenExpr(_2082_cond, selfIdent, @params, true, out _out1371, out _out1372, out _out1373, out _out1374);
          _2083_condString = _out1371;
          _2084___v68 = _out1372;
          _2085_condErased = _out1373;
          _2086_recIdentsCond = _out1374;
          if (!(_2085_condErased)) {
            _2083_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2083_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2087___v69;
          bool _2088_tHasToBeOwned;
          bool _2089___v70;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2090___v71;
          Dafny.ISequence<Dafny.Rune> _out1375;
          bool _out1376;
          bool _out1377;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1378;
          DCOMP.COMP.GenExpr(_2081_t, selfIdent, @params, mustOwn, out _out1375, out _out1376, out _out1377, out _out1378);
          _2087___v69 = _out1375;
          _2088_tHasToBeOwned = _out1376;
          _2089___v70 = _out1377;
          _2090___v71 = _out1378;
          Dafny.ISequence<Dafny.Rune> _2091_fString;
          bool _2092_fOwned;
          bool _2093_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2094_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1379;
          bool _out1380;
          bool _out1381;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1382;
          DCOMP.COMP.GenExpr(_2080_f, selfIdent, @params, _2088_tHasToBeOwned, out _out1379, out _out1380, out _out1381, out _out1382);
          _2091_fString = _out1379;
          _2092_fOwned = _out1380;
          _2093_fErased = _out1381;
          _2094_recIdentsF = _out1382;
          Dafny.ISequence<Dafny.Rune> _2095_tString;
          bool _2096___v72;
          bool _2097_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2098_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1383;
          bool _out1384;
          bool _out1385;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1386;
          DCOMP.COMP.GenExpr(_2081_t, selfIdent, @params, _2092_fOwned, out _out1383, out _out1384, out _out1385, out _out1386);
          _2095_tString = _out1383;
          _2096___v72 = _out1384;
          _2097_tErased = _out1385;
          _2098_recIdentsT = _out1386;
          if ((!(_2093_fErased)) || (!(_2097_tErased))) {
            if (_2093_fErased) {
              _2091_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2091_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2097_tErased) {
              _2095_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2095_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _2083_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2095_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _2091_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _2092_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2086_recIdentsCond, _2098_recIdentsT), _2094_recIdentsF);
          isErased = (_2093_fErased) || (_2097_tErased);
        }
      } else if (_source22.is_UnOp) {
        DAST._IUnaryOp _2099___mcc_h27 = _source22.dtor_unOp;
        DAST._IExpression _2100___mcc_h28 = _source22.dtor_expr;
        DAST._IUnaryOp _source73 = _2099___mcc_h27;
        if (_source73.is_Not) {
          DAST._IExpression _2101_e = _2100___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2102_recursiveGen;
            bool _2103___v73;
            bool _2104_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2105_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1387;
            bool _out1388;
            bool _out1389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1390;
            DCOMP.COMP.GenExpr(_2101_e, selfIdent, @params, true, out _out1387, out _out1388, out _out1389, out _out1390);
            _2102_recursiveGen = _out1387;
            _2103___v73 = _out1388;
            _2104_recErased = _out1389;
            _2105_recIdents = _out1390;
            if (!(_2104_recErased)) {
              _2102_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2102_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _2102_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2105_recIdents;
            isErased = true;
          }
        } else if (_source73.is_BitwiseNot) {
          DAST._IExpression _2106_e = _2100___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2107_recursiveGen;
            bool _2108___v74;
            bool _2109_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2110_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1391;
            bool _out1392;
            bool _out1393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
            DCOMP.COMP.GenExpr(_2106_e, selfIdent, @params, true, out _out1391, out _out1392, out _out1393, out _out1394);
            _2107_recursiveGen = _out1391;
            _2108___v74 = _out1392;
            _2109_recErased = _out1393;
            _2110_recIdents = _out1394;
            if (!(_2109_recErased)) {
              _2107_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2107_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _2107_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2110_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _2111_e = _2100___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2112_recursiveGen;
            bool _2113_recOwned;
            bool _2114_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2115_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1395;
            bool _out1396;
            bool _out1397;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1398;
            DCOMP.COMP.GenExpr(_2111_e, selfIdent, @params, false, out _out1395, out _out1396, out _out1397, out _out1398);
            _2112_recursiveGen = _out1395;
            _2113_recOwned = _out1396;
            _2114_recErased = _out1397;
            _2115_recIdents = _out1398;
            if (!(_2114_recErased)) {
              Dafny.ISequence<Dafny.Rune> _2116_eraseFn;
              _2116_eraseFn = ((_2113_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2112_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2116_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2112_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2112_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len())"));
            isOwned = true;
            readIdents = _2115_recIdents;
            isErased = true;
          }
        }
      } else if (_source22.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _2117___mcc_h29 = _source22.dtor_op;
        DAST._IExpression _2118___mcc_h30 = _source22.dtor_left;
        DAST._IExpression _2119___mcc_h31 = _source22.dtor_right;
        DAST._IExpression _2120_r = _2119___mcc_h31;
        DAST._IExpression _2121_l = _2118___mcc_h30;
        Dafny.ISequence<Dafny.Rune> _2122_op = _2117___mcc_h29;
        {
          Dafny.ISequence<Dafny.Rune> _2123_left;
          bool _2124___v75;
          bool _2125_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2126_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1399;
          bool _out1400;
          bool _out1401;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
          DCOMP.COMP.GenExpr(_2121_l, selfIdent, @params, true, out _out1399, out _out1400, out _out1401, out _out1402);
          _2123_left = _out1399;
          _2124___v75 = _out1400;
          _2125_leftErased = _out1401;
          _2126_recIdentsL = _out1402;
          Dafny.ISequence<Dafny.Rune> _2127_right;
          bool _2128___v76;
          bool _2129_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2130_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1403;
          bool _out1404;
          bool _out1405;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1406;
          DCOMP.COMP.GenExpr(_2120_r, selfIdent, @params, true, out _out1403, out _out1404, out _out1405, out _out1406);
          _2127_right = _out1403;
          _2128___v76 = _out1404;
          _2129_rightErased = _out1405;
          _2130_recIdentsR = _out1406;
          if (!(_2125_leftErased)) {
            _2123_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2123_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_2129_rightErased)) {
            _2127_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2127_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_2122_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _2123_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2127_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_2122_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _2123_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2127_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2123_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2122_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2127_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2126_recIdentsL, _2130_recIdentsR);
          isErased = true;
        }
      } else if (_source22.is_ArrayLen) {
        DAST._IExpression _2131___mcc_h32 = _source22.dtor_expr;
        DAST._IExpression _2132_expr = _2131___mcc_h32;
        {
          Dafny.ISequence<Dafny.Rune> _2133_recursiveGen;
          bool _2134___v77;
          bool _2135_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2136_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1407;
          bool _out1408;
          bool _out1409;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1410;
          DCOMP.COMP.GenExpr(_2132_expr, selfIdent, @params, true, out _out1407, out _out1408, out _out1409, out _out1410);
          _2133_recursiveGen = _out1407;
          _2134___v77 = _out1408;
          _2135_recErased = _out1409;
          _2136_recIdents = _out1410;
          if (!(_2135_recErased)) {
            _2133_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2133_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2133_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())"));
          isOwned = true;
          readIdents = _2136_recIdents;
          isErased = true;
        }
      } else if (_source22.is_Select) {
        DAST._IExpression _2137___mcc_h33 = _source22.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2138___mcc_h34 = _source22.dtor_field;
        bool _2139___mcc_h35 = _source22.dtor_isConstant;
        bool _2140___mcc_h36 = _source22.dtor_onDatatype;
        DAST._IExpression _source74 = _2137___mcc_h33;
        if (_source74.is_Literal) {
          DAST._ILiteral _2141___mcc_h37 = _source74.dtor_Literal_a0;
          bool _2142_isDatatype = _2140___mcc_h36;
          bool _2143_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2144_field = _2138___mcc_h34;
          DAST._IExpression _2145_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2146_onString;
            bool _2147_onOwned;
            bool _2148_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2149_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1411;
            bool _out1412;
            bool _out1413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1414;
            DCOMP.COMP.GenExpr(_2145_on, selfIdent, @params, false, out _out1411, out _out1412, out _out1413, out _out1414);
            _2146_onString = _out1411;
            _2147_onOwned = _out1412;
            _2148_onErased = _out1413;
            _2149_recIdents = _out1414;
            if (!(_2148_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2150_eraseFn;
              _2150_eraseFn = ((_2147_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2146_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2150_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2146_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2142_isDatatype) || (_2143_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2146_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2144_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2143_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2146_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2144_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2149_recIdents;
          }
        } else if (_source74.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2151___mcc_h39 = _source74.dtor_Ident_a0;
          bool _2152_isDatatype = _2140___mcc_h36;
          bool _2153_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2154_field = _2138___mcc_h34;
          DAST._IExpression _2155_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2156_onString;
            bool _2157_onOwned;
            bool _2158_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2159_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1415;
            bool _out1416;
            bool _out1417;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
            DCOMP.COMP.GenExpr(_2155_on, selfIdent, @params, false, out _out1415, out _out1416, out _out1417, out _out1418);
            _2156_onString = _out1415;
            _2157_onOwned = _out1416;
            _2158_onErased = _out1417;
            _2159_recIdents = _out1418;
            if (!(_2158_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2160_eraseFn;
              _2160_eraseFn = ((_2157_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2156_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2160_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2156_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2152_isDatatype) || (_2153_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2156_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2154_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2153_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2156_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2154_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2159_recIdents;
          }
        } else if (_source74.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2161___mcc_h41 = _source74.dtor_Companion_a0;
          bool _2162_isDatatype = _2140___mcc_h36;
          bool _2163_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2164_field = _2138___mcc_h34;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2165_c = _2161___mcc_h41;
          {
            Dafny.ISequence<Dafny.Rune> _2166_onString;
            bool _2167_onOwned;
            bool _2168_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1419;
            bool _out1420;
            bool _out1421;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1422;
            DCOMP.COMP.GenExpr(DAST.Expression.create_Companion(_2165_c), selfIdent, @params, false, out _out1419, out _out1420, out _out1421, out _out1422);
            _2166_onString = _out1419;
            _2167_onOwned = _out1420;
            _2168_onErased = _out1421;
            _2169_recIdents = _out1422;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2166_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2164_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            isOwned = true;
            isErased = false;
            readIdents = _2169_recIdents;
          }
        } else if (_source74.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2170___mcc_h43 = _source74.dtor_Tuple_a0;
          bool _2171_isDatatype = _2140___mcc_h36;
          bool _2172_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2173_field = _2138___mcc_h34;
          DAST._IExpression _2174_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2175_onString;
            bool _2176_onOwned;
            bool _2177_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2178_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1423;
            bool _out1424;
            bool _out1425;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1426;
            DCOMP.COMP.GenExpr(_2174_on, selfIdent, @params, false, out _out1423, out _out1424, out _out1425, out _out1426);
            _2175_onString = _out1423;
            _2176_onOwned = _out1424;
            _2177_onErased = _out1425;
            _2178_recIdents = _out1426;
            if (!(_2177_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2179_eraseFn;
              _2179_eraseFn = ((_2176_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2175_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2179_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2175_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2171_isDatatype) || (_2172_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2175_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2173_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2172_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2175_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2173_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2178_recIdents;
          }
        } else if (_source74.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2180___mcc_h45 = _source74.dtor_path;
          Dafny.ISequence<DAST._IExpression> _2181___mcc_h46 = _source74.dtor_args;
          bool _2182_isDatatype = _2140___mcc_h36;
          bool _2183_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2184_field = _2138___mcc_h34;
          DAST._IExpression _2185_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2186_onString;
            bool _2187_onOwned;
            bool _2188_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2189_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1427;
            bool _out1428;
            bool _out1429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1430;
            DCOMP.COMP.GenExpr(_2185_on, selfIdent, @params, false, out _out1427, out _out1428, out _out1429, out _out1430);
            _2186_onString = _out1427;
            _2187_onOwned = _out1428;
            _2188_onErased = _out1429;
            _2189_recIdents = _out1430;
            if (!(_2188_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2190_eraseFn;
              _2190_eraseFn = ((_2187_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2186_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2190_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2186_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2182_isDatatype) || (_2183_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2186_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2184_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2183_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2186_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2184_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2189_recIdents;
          }
        } else if (_source74.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _2191___mcc_h49 = _source74.dtor_dims;
          bool _2192_isDatatype = _2140___mcc_h36;
          bool _2193_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2194_field = _2138___mcc_h34;
          DAST._IExpression _2195_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2196_onString;
            bool _2197_onOwned;
            bool _2198_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2199_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1431;
            bool _out1432;
            bool _out1433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1434;
            DCOMP.COMP.GenExpr(_2195_on, selfIdent, @params, false, out _out1431, out _out1432, out _out1433, out _out1434);
            _2196_onString = _out1431;
            _2197_onOwned = _out1432;
            _2198_onErased = _out1433;
            _2199_recIdents = _out1434;
            if (!(_2198_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2200_eraseFn;
              _2200_eraseFn = ((_2197_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2196_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2200_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2196_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2192_isDatatype) || (_2193_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2196_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2194_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2193_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2196_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2194_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2199_recIdents;
          }
        } else if (_source74.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2201___mcc_h51 = _source74.dtor_path;
          Dafny.ISequence<Dafny.Rune> _2202___mcc_h52 = _source74.dtor_variant;
          bool _2203___mcc_h53 = _source74.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2204___mcc_h54 = _source74.dtor_contents;
          bool _2205_isDatatype = _2140___mcc_h36;
          bool _2206_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2207_field = _2138___mcc_h34;
          DAST._IExpression _2208_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2209_onString;
            bool _2210_onOwned;
            bool _2211_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2212_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1435;
            bool _out1436;
            bool _out1437;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1438;
            DCOMP.COMP.GenExpr(_2208_on, selfIdent, @params, false, out _out1435, out _out1436, out _out1437, out _out1438);
            _2209_onString = _out1435;
            _2210_onOwned = _out1436;
            _2211_onErased = _out1437;
            _2212_recIdents = _out1438;
            if (!(_2211_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2213_eraseFn;
              _2213_eraseFn = ((_2210_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2209_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2213_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2209_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2205_isDatatype) || (_2206_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2209_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2207_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2206_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2209_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2207_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2212_recIdents;
          }
        } else if (_source74.is_Convert) {
          DAST._IExpression _2214___mcc_h59 = _source74.dtor_value;
          DAST._IType _2215___mcc_h60 = _source74.dtor_from;
          DAST._IType _2216___mcc_h61 = _source74.dtor_typ;
          bool _2217_isDatatype = _2140___mcc_h36;
          bool _2218_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2219_field = _2138___mcc_h34;
          DAST._IExpression _2220_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2221_onString;
            bool _2222_onOwned;
            bool _2223_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2224_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1439;
            bool _out1440;
            bool _out1441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
            DCOMP.COMP.GenExpr(_2220_on, selfIdent, @params, false, out _out1439, out _out1440, out _out1441, out _out1442);
            _2221_onString = _out1439;
            _2222_onOwned = _out1440;
            _2223_onErased = _out1441;
            _2224_recIdents = _out1442;
            if (!(_2223_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2225_eraseFn;
              _2225_eraseFn = ((_2222_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2221_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2225_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2221_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2217_isDatatype) || (_2218_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2221_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2219_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2218_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2221_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2219_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2224_recIdents;
          }
        } else if (_source74.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2226___mcc_h65 = _source74.dtor_elements;
          bool _2227_isDatatype = _2140___mcc_h36;
          bool _2228_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2229_field = _2138___mcc_h34;
          DAST._IExpression _2230_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2231_onString;
            bool _2232_onOwned;
            bool _2233_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2234_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1443;
            bool _out1444;
            bool _out1445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1446;
            DCOMP.COMP.GenExpr(_2230_on, selfIdent, @params, false, out _out1443, out _out1444, out _out1445, out _out1446);
            _2231_onString = _out1443;
            _2232_onOwned = _out1444;
            _2233_onErased = _out1445;
            _2234_recIdents = _out1446;
            if (!(_2233_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2235_eraseFn;
              _2235_eraseFn = ((_2232_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2231_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2235_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2231_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2227_isDatatype) || (_2228_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2231_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2229_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2228_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2231_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2229_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2234_recIdents;
          }
        } else if (_source74.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2236___mcc_h67 = _source74.dtor_elements;
          bool _2237_isDatatype = _2140___mcc_h36;
          bool _2238_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2239_field = _2138___mcc_h34;
          DAST._IExpression _2240_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2241_onString;
            bool _2242_onOwned;
            bool _2243_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2244_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1447;
            bool _out1448;
            bool _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            DCOMP.COMP.GenExpr(_2240_on, selfIdent, @params, false, out _out1447, out _out1448, out _out1449, out _out1450);
            _2241_onString = _out1447;
            _2242_onOwned = _out1448;
            _2243_onErased = _out1449;
            _2244_recIdents = _out1450;
            if (!(_2243_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2245_eraseFn;
              _2245_eraseFn = ((_2242_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2241_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2245_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2241_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2237_isDatatype) || (_2238_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2241_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2239_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2238_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2241_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2239_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2244_recIdents;
          }
        } else if (_source74.is_This) {
          bool _2246_isDatatype = _2140___mcc_h36;
          bool _2247_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2248_field = _2138___mcc_h34;
          DAST._IExpression _2249_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2250_onString;
            bool _2251_onOwned;
            bool _2252_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2253_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1451;
            bool _out1452;
            bool _out1453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1454;
            DCOMP.COMP.GenExpr(_2249_on, selfIdent, @params, false, out _out1451, out _out1452, out _out1453, out _out1454);
            _2250_onString = _out1451;
            _2251_onOwned = _out1452;
            _2252_onErased = _out1453;
            _2253_recIdents = _out1454;
            if (!(_2252_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2254_eraseFn;
              _2254_eraseFn = ((_2251_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2250_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2254_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2250_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2246_isDatatype) || (_2247_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2250_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2248_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2247_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2250_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2248_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2253_recIdents;
          }
        } else if (_source74.is_Ite) {
          DAST._IExpression _2255___mcc_h69 = _source74.dtor_cond;
          DAST._IExpression _2256___mcc_h70 = _source74.dtor_thn;
          DAST._IExpression _2257___mcc_h71 = _source74.dtor_els;
          bool _2258_isDatatype = _2140___mcc_h36;
          bool _2259_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2260_field = _2138___mcc_h34;
          DAST._IExpression _2261_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2262_onString;
            bool _2263_onOwned;
            bool _2264_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2265_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1455;
            bool _out1456;
            bool _out1457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1458;
            DCOMP.COMP.GenExpr(_2261_on, selfIdent, @params, false, out _out1455, out _out1456, out _out1457, out _out1458);
            _2262_onString = _out1455;
            _2263_onOwned = _out1456;
            _2264_onErased = _out1457;
            _2265_recIdents = _out1458;
            if (!(_2264_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2266_eraseFn;
              _2266_eraseFn = ((_2263_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2262_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2266_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2262_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2258_isDatatype) || (_2259_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2262_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2260_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2259_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2262_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2260_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2265_recIdents;
          }
        } else if (_source74.is_UnOp) {
          DAST._IUnaryOp _2267___mcc_h75 = _source74.dtor_unOp;
          DAST._IExpression _2268___mcc_h76 = _source74.dtor_expr;
          bool _2269_isDatatype = _2140___mcc_h36;
          bool _2270_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2271_field = _2138___mcc_h34;
          DAST._IExpression _2272_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2273_onString;
            bool _2274_onOwned;
            bool _2275_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2276_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1459;
            bool _out1460;
            bool _out1461;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
            DCOMP.COMP.GenExpr(_2272_on, selfIdent, @params, false, out _out1459, out _out1460, out _out1461, out _out1462);
            _2273_onString = _out1459;
            _2274_onOwned = _out1460;
            _2275_onErased = _out1461;
            _2276_recIdents = _out1462;
            if (!(_2275_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2277_eraseFn;
              _2277_eraseFn = ((_2274_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2273_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2277_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2273_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2269_isDatatype) || (_2270_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2273_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2271_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2270_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2273_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2271_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2276_recIdents;
          }
        } else if (_source74.is_BinOp) {
          Dafny.ISequence<Dafny.Rune> _2278___mcc_h79 = _source74.dtor_op;
          DAST._IExpression _2279___mcc_h80 = _source74.dtor_left;
          DAST._IExpression _2280___mcc_h81 = _source74.dtor_right;
          bool _2281_isDatatype = _2140___mcc_h36;
          bool _2282_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2283_field = _2138___mcc_h34;
          DAST._IExpression _2284_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2285_onString;
            bool _2286_onOwned;
            bool _2287_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2288_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1463;
            bool _out1464;
            bool _out1465;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1466;
            DCOMP.COMP.GenExpr(_2284_on, selfIdent, @params, false, out _out1463, out _out1464, out _out1465, out _out1466);
            _2285_onString = _out1463;
            _2286_onOwned = _out1464;
            _2287_onErased = _out1465;
            _2288_recIdents = _out1466;
            if (!(_2287_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2289_eraseFn;
              _2289_eraseFn = ((_2286_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2285_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2289_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2285_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2281_isDatatype) || (_2282_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2285_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2283_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2282_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2285_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2283_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2288_recIdents;
          }
        } else if (_source74.is_ArrayLen) {
          DAST._IExpression _2290___mcc_h85 = _source74.dtor_expr;
          bool _2291_isDatatype = _2140___mcc_h36;
          bool _2292_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2293_field = _2138___mcc_h34;
          DAST._IExpression _2294_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2295_onString;
            bool _2296_onOwned;
            bool _2297_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2298_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1467;
            bool _out1468;
            bool _out1469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
            DCOMP.COMP.GenExpr(_2294_on, selfIdent, @params, false, out _out1467, out _out1468, out _out1469, out _out1470);
            _2295_onString = _out1467;
            _2296_onOwned = _out1468;
            _2297_onErased = _out1469;
            _2298_recIdents = _out1470;
            if (!(_2297_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2299_eraseFn;
              _2299_eraseFn = ((_2296_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2295_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2299_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2295_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2291_isDatatype) || (_2292_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2295_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2293_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2292_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2295_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2293_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2298_recIdents;
          }
        } else if (_source74.is_Select) {
          DAST._IExpression _2300___mcc_h87 = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2301___mcc_h88 = _source74.dtor_field;
          bool _2302___mcc_h89 = _source74.dtor_isConstant;
          bool _2303___mcc_h90 = _source74.dtor_onDatatype;
          bool _2304_isDatatype = _2140___mcc_h36;
          bool _2305_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2306_field = _2138___mcc_h34;
          DAST._IExpression _2307_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2308_onString;
            bool _2309_onOwned;
            bool _2310_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2311_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1471;
            bool _out1472;
            bool _out1473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1474;
            DCOMP.COMP.GenExpr(_2307_on, selfIdent, @params, false, out _out1471, out _out1472, out _out1473, out _out1474);
            _2308_onString = _out1471;
            _2309_onOwned = _out1472;
            _2310_onErased = _out1473;
            _2311_recIdents = _out1474;
            if (!(_2310_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2312_eraseFn;
              _2312_eraseFn = ((_2309_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2308_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2312_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2308_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2304_isDatatype) || (_2305_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2308_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2306_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2305_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2308_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2306_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2311_recIdents;
          }
        } else if (_source74.is_SelectFn) {
          DAST._IExpression _2313___mcc_h95 = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2314___mcc_h96 = _source74.dtor_field;
          bool _2315___mcc_h97 = _source74.dtor_onDatatype;
          bool _2316___mcc_h98 = _source74.dtor_isStatic;
          BigInteger _2317___mcc_h99 = _source74.dtor_arity;
          bool _2318_isDatatype = _2140___mcc_h36;
          bool _2319_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2320_field = _2138___mcc_h34;
          DAST._IExpression _2321_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2322_onString;
            bool _2323_onOwned;
            bool _2324_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2325_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1475;
            bool _out1476;
            bool _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            DCOMP.COMP.GenExpr(_2321_on, selfIdent, @params, false, out _out1475, out _out1476, out _out1477, out _out1478);
            _2322_onString = _out1475;
            _2323_onOwned = _out1476;
            _2324_onErased = _out1477;
            _2325_recIdents = _out1478;
            if (!(_2324_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2326_eraseFn;
              _2326_eraseFn = ((_2323_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2322_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2326_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2322_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2318_isDatatype) || (_2319_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2322_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2320_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2319_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2322_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2320_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2325_recIdents;
          }
        } else if (_source74.is_Index) {
          DAST._IExpression _2327___mcc_h105 = _source74.dtor_expr;
          bool _2328___mcc_h106 = _source74.dtor_isArray;
          Dafny.ISequence<DAST._IExpression> _2329___mcc_h107 = _source74.dtor_indices;
          bool _2330_isDatatype = _2140___mcc_h36;
          bool _2331_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2332_field = _2138___mcc_h34;
          DAST._IExpression _2333_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2334_onString;
            bool _2335_onOwned;
            bool _2336_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2337_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1479;
            bool _out1480;
            bool _out1481;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1482;
            DCOMP.COMP.GenExpr(_2333_on, selfIdent, @params, false, out _out1479, out _out1480, out _out1481, out _out1482);
            _2334_onString = _out1479;
            _2335_onOwned = _out1480;
            _2336_onErased = _out1481;
            _2337_recIdents = _out1482;
            if (!(_2336_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2338_eraseFn;
              _2338_eraseFn = ((_2335_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2334_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2338_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2334_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2330_isDatatype) || (_2331_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2334_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2332_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2331_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2334_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2332_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2337_recIdents;
          }
        } else if (_source74.is_IndexRange) {
          DAST._IExpression _2339___mcc_h111 = _source74.dtor_expr;
          bool _2340___mcc_h112 = _source74.dtor_isArray;
          DAST._IOptional<DAST._IExpression> _2341___mcc_h113 = _source74.dtor_low;
          DAST._IOptional<DAST._IExpression> _2342___mcc_h114 = _source74.dtor_high;
          bool _2343_isDatatype = _2140___mcc_h36;
          bool _2344_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2345_field = _2138___mcc_h34;
          DAST._IExpression _2346_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2347_onString;
            bool _2348_onOwned;
            bool _2349_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2350_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1483;
            bool _out1484;
            bool _out1485;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
            DCOMP.COMP.GenExpr(_2346_on, selfIdent, @params, false, out _out1483, out _out1484, out _out1485, out _out1486);
            _2347_onString = _out1483;
            _2348_onOwned = _out1484;
            _2349_onErased = _out1485;
            _2350_recIdents = _out1486;
            if (!(_2349_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2351_eraseFn;
              _2351_eraseFn = ((_2348_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2347_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2351_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2347_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2343_isDatatype) || (_2344_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2347_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2345_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2344_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2347_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2345_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2350_recIdents;
          }
        } else if (_source74.is_TupleSelect) {
          DAST._IExpression _2352___mcc_h119 = _source74.dtor_expr;
          BigInteger _2353___mcc_h120 = _source74.dtor_index;
          bool _2354_isDatatype = _2140___mcc_h36;
          bool _2355_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2356_field = _2138___mcc_h34;
          DAST._IExpression _2357_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2358_onString;
            bool _2359_onOwned;
            bool _2360_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2361_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1487;
            bool _out1488;
            bool _out1489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1490;
            DCOMP.COMP.GenExpr(_2357_on, selfIdent, @params, false, out _out1487, out _out1488, out _out1489, out _out1490);
            _2358_onString = _out1487;
            _2359_onOwned = _out1488;
            _2360_onErased = _out1489;
            _2361_recIdents = _out1490;
            if (!(_2360_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2362_eraseFn;
              _2362_eraseFn = ((_2359_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2358_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2362_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2358_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2354_isDatatype) || (_2355_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2358_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2356_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2355_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2358_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2356_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2361_recIdents;
          }
        } else if (_source74.is_Call) {
          DAST._IExpression _2363___mcc_h123 = _source74.dtor_on;
          Dafny.ISequence<Dafny.Rune> _2364___mcc_h124 = _source74.dtor_name;
          Dafny.ISequence<DAST._IType> _2365___mcc_h125 = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2366___mcc_h126 = _source74.dtor_args;
          bool _2367_isDatatype = _2140___mcc_h36;
          bool _2368_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2369_field = _2138___mcc_h34;
          DAST._IExpression _2370_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2371_onString;
            bool _2372_onOwned;
            bool _2373_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2374_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1491;
            bool _out1492;
            bool _out1493;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1494;
            DCOMP.COMP.GenExpr(_2370_on, selfIdent, @params, false, out _out1491, out _out1492, out _out1493, out _out1494);
            _2371_onString = _out1491;
            _2372_onOwned = _out1492;
            _2373_onErased = _out1493;
            _2374_recIdents = _out1494;
            if (!(_2373_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2375_eraseFn;
              _2375_eraseFn = ((_2372_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2371_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2375_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2371_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2367_isDatatype) || (_2368_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2371_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2369_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2368_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2371_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2369_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2374_recIdents;
          }
        } else if (_source74.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2376___mcc_h131 = _source74.dtor_params;
          DAST._IType _2377___mcc_h132 = _source74.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2378___mcc_h133 = _source74.dtor_body;
          bool _2379_isDatatype = _2140___mcc_h36;
          bool _2380_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2381_field = _2138___mcc_h34;
          DAST._IExpression _2382_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2383_onString;
            bool _2384_onOwned;
            bool _2385_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2386_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1495;
            bool _out1496;
            bool _out1497;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1498;
            DCOMP.COMP.GenExpr(_2382_on, selfIdent, @params, false, out _out1495, out _out1496, out _out1497, out _out1498);
            _2383_onString = _out1495;
            _2384_onOwned = _out1496;
            _2385_onErased = _out1497;
            _2386_recIdents = _out1498;
            if (!(_2385_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2387_eraseFn;
              _2387_eraseFn = ((_2384_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2383_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2387_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2383_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2379_isDatatype) || (_2380_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2383_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2381_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2380_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2383_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2381_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2386_recIdents;
          }
        } else if (_source74.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2388___mcc_h137 = _source74.dtor_values;
          DAST._IType _2389___mcc_h138 = _source74.dtor_retType;
          DAST._IExpression _2390___mcc_h139 = _source74.dtor_expr;
          bool _2391_isDatatype = _2140___mcc_h36;
          bool _2392_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2393_field = _2138___mcc_h34;
          DAST._IExpression _2394_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2395_onString;
            bool _2396_onOwned;
            bool _2397_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2398_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1499;
            bool _out1500;
            bool _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            DCOMP.COMP.GenExpr(_2394_on, selfIdent, @params, false, out _out1499, out _out1500, out _out1501, out _out1502);
            _2395_onString = _out1499;
            _2396_onOwned = _out1500;
            _2397_onErased = _out1501;
            _2398_recIdents = _out1502;
            if (!(_2397_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2399_eraseFn;
              _2399_eraseFn = ((_2396_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2395_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2399_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2395_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2391_isDatatype) || (_2392_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2395_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2393_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2392_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2395_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2393_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2398_recIdents;
          }
        } else if (_source74.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2400___mcc_h143 = _source74.dtor_name;
          DAST._IType _2401___mcc_h144 = _source74.dtor_typ;
          DAST._IExpression _2402___mcc_h145 = _source74.dtor_value;
          DAST._IExpression _2403___mcc_h146 = _source74.dtor_iifeBody;
          bool _2404_isDatatype = _2140___mcc_h36;
          bool _2405_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2406_field = _2138___mcc_h34;
          DAST._IExpression _2407_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2408_onString;
            bool _2409_onOwned;
            bool _2410_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2411_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1503;
            bool _out1504;
            bool _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            DCOMP.COMP.GenExpr(_2407_on, selfIdent, @params, false, out _out1503, out _out1504, out _out1505, out _out1506);
            _2408_onString = _out1503;
            _2409_onOwned = _out1504;
            _2410_onErased = _out1505;
            _2411_recIdents = _out1506;
            if (!(_2410_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2412_eraseFn;
              _2412_eraseFn = ((_2409_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2408_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2412_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2408_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2404_isDatatype) || (_2405_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2408_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2406_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2405_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2408_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2406_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2411_recIdents;
          }
        } else if (_source74.is_Apply) {
          DAST._IExpression _2413___mcc_h151 = _source74.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2414___mcc_h152 = _source74.dtor_args;
          bool _2415_isDatatype = _2140___mcc_h36;
          bool _2416_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2417_field = _2138___mcc_h34;
          DAST._IExpression _2418_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2419_onString;
            bool _2420_onOwned;
            bool _2421_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2422_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1507;
            bool _out1508;
            bool _out1509;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1510;
            DCOMP.COMP.GenExpr(_2418_on, selfIdent, @params, false, out _out1507, out _out1508, out _out1509, out _out1510);
            _2419_onString = _out1507;
            _2420_onOwned = _out1508;
            _2421_onErased = _out1509;
            _2422_recIdents = _out1510;
            if (!(_2421_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2423_eraseFn;
              _2423_eraseFn = ((_2420_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2419_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2423_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2419_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2415_isDatatype) || (_2416_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2419_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2417_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2416_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2419_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2417_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2422_recIdents;
          }
        } else if (_source74.is_TypeTest) {
          DAST._IExpression _2424___mcc_h155 = _source74.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2425___mcc_h156 = _source74.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2426___mcc_h157 = _source74.dtor_variant;
          bool _2427_isDatatype = _2140___mcc_h36;
          bool _2428_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2429_field = _2138___mcc_h34;
          DAST._IExpression _2430_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2431_onString;
            bool _2432_onOwned;
            bool _2433_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2434_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1511;
            bool _out1512;
            bool _out1513;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1514;
            DCOMP.COMP.GenExpr(_2430_on, selfIdent, @params, false, out _out1511, out _out1512, out _out1513, out _out1514);
            _2431_onString = _out1511;
            _2432_onOwned = _out1512;
            _2433_onErased = _out1513;
            _2434_recIdents = _out1514;
            if (!(_2433_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2435_eraseFn;
              _2435_eraseFn = ((_2432_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2431_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2435_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2431_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2427_isDatatype) || (_2428_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2431_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2429_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2428_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2431_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2429_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2434_recIdents;
          }
        } else {
          DAST._IType _2436___mcc_h161 = _source74.dtor_typ;
          bool _2437_isDatatype = _2140___mcc_h36;
          bool _2438_isConstant = _2139___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2439_field = _2138___mcc_h34;
          DAST._IExpression _2440_on = _2137___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2441_onString;
            bool _2442_onOwned;
            bool _2443_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2444_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1515;
            bool _out1516;
            bool _out1517;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
            DCOMP.COMP.GenExpr(_2440_on, selfIdent, @params, false, out _out1515, out _out1516, out _out1517, out _out1518);
            _2441_onString = _out1515;
            _2442_onOwned = _out1516;
            _2443_onErased = _out1517;
            _2444_recIdents = _out1518;
            if (!(_2443_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2445_eraseFn;
              _2445_eraseFn = ((_2442_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2441_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2445_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2441_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2437_isDatatype) || (_2438_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2441_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2439_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2438_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2441_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2439_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2444_recIdents;
          }
        }
      } else if (_source22.is_SelectFn) {
        DAST._IExpression _2446___mcc_h163 = _source22.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2447___mcc_h164 = _source22.dtor_field;
        bool _2448___mcc_h165 = _source22.dtor_onDatatype;
        bool _2449___mcc_h166 = _source22.dtor_isStatic;
        BigInteger _2450___mcc_h167 = _source22.dtor_arity;
        BigInteger _2451_arity = _2450___mcc_h167;
        bool _2452_isStatic = _2449___mcc_h166;
        bool _2453_isDatatype = _2448___mcc_h165;
        Dafny.ISequence<Dafny.Rune> _2454_field = _2447___mcc_h164;
        DAST._IExpression _2455_on = _2446___mcc_h163;
        {
          Dafny.ISequence<Dafny.Rune> _2456_onString;
          bool _2457_onOwned;
          bool _2458___v78;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2459_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1519;
          bool _out1520;
          bool _out1521;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1522;
          DCOMP.COMP.GenExpr(_2455_on, selfIdent, @params, false, out _out1519, out _out1520, out _out1521, out _out1522);
          _2456_onString = _out1519;
          _2457_onOwned = _out1520;
          _2458___v78 = _out1521;
          _2459_recIdents = _out1522;
          if (_2452_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2456_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2454_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2456_onString), ((_2457_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _2460_args;
            _2460_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _2461_i;
            _2461_i = BigInteger.Zero;
            while ((_2461_i) < (_2451_arity)) {
              if ((_2461_i).Sign == 1) {
                _2460_args = Dafny.Sequence<Dafny.Rune>.Concat(_2460_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2460_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2460_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_2461_i));
              _2461_i = (_2461_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2460_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _2454_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2460_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper(::std::rc::Rc::new("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
          readIdents = _2459_recIdents;
        }
      } else if (_source22.is_Index) {
        DAST._IExpression _2462___mcc_h168 = _source22.dtor_expr;
        bool _2463___mcc_h169 = _source22.dtor_isArray;
        Dafny.ISequence<DAST._IExpression> _2464___mcc_h170 = _source22.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2465_indices = _2464___mcc_h170;
        bool _2466_isArray = _2463___mcc_h169;
        DAST._IExpression _2467_on = _2462___mcc_h168;
        {
          Dafny.ISequence<Dafny.Rune> _2468_onString;
          bool _2469_onOwned;
          bool _2470_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2471_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1523;
          bool _out1524;
          bool _out1525;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1526;
          DCOMP.COMP.GenExpr(_2467_on, selfIdent, @params, false, out _out1523, out _out1524, out _out1525, out _out1526);
          _2468_onString = _out1523;
          _2469_onOwned = _out1524;
          _2470_onErased = _out1525;
          _2471_recIdents = _out1526;
          readIdents = _2471_recIdents;
          if (!(_2470_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2472_eraseFn;
            _2472_eraseFn = ((_2469_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2468_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2472_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2468_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2468_onString;
          BigInteger _2473_i;
          _2473_i = BigInteger.Zero;
          while ((_2473_i) < (new BigInteger((_2465_indices).Count))) {
            Dafny.ISequence<Dafny.Rune> _2474_idx;
            bool _2475___v79;
            bool _2476_idxErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2477_recIdentsIdx;
            Dafny.ISequence<Dafny.Rune> _out1527;
            bool _out1528;
            bool _out1529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1530;
            DCOMP.COMP.GenExpr((_2465_indices).Select(_2473_i), selfIdent, @params, true, out _out1527, out _out1528, out _out1529, out _out1530);
            _2474_idx = _out1527;
            _2475___v79 = _out1528;
            _2476_idxErased = _out1529;
            _2477_recIdentsIdx = _out1530;
            if (!(_2476_idxErased)) {
              _2474_idx = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2474_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2466_isArray) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[<usize as ::dafny_runtime::NumCast>::from(")), _2474_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2477_recIdentsIdx);
            _2473_i = (_2473_i) + (BigInteger.One);
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = false;
          }
          isErased = _2470_onErased;
        }
      } else if (_source22.is_IndexRange) {
        DAST._IExpression _2478___mcc_h171 = _source22.dtor_expr;
        bool _2479___mcc_h172 = _source22.dtor_isArray;
        DAST._IOptional<DAST._IExpression> _2480___mcc_h173 = _source22.dtor_low;
        DAST._IOptional<DAST._IExpression> _2481___mcc_h174 = _source22.dtor_high;
        DAST._IOptional<DAST._IExpression> _2482_high = _2481___mcc_h174;
        DAST._IOptional<DAST._IExpression> _2483_low = _2480___mcc_h173;
        bool _2484_isArray = _2479___mcc_h172;
        DAST._IExpression _2485_on = _2478___mcc_h171;
        {
          Dafny.ISequence<Dafny.Rune> _2486_onString;
          bool _2487_onOwned;
          bool _2488_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2489_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1531;
          bool _out1532;
          bool _out1533;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1534;
          DCOMP.COMP.GenExpr(_2485_on, selfIdent, @params, false, out _out1531, out _out1532, out _out1533, out _out1534);
          _2486_onString = _out1531;
          _2487_onOwned = _out1532;
          _2488_onErased = _out1533;
          _2489_recIdents = _out1534;
          readIdents = _2489_recIdents;
          if (!(_2488_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2490_eraseFn;
            _2490_eraseFn = ((_2487_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2486_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2490_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2486_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2486_onString;
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2491_lowString;
          _2491_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source75 = _2483_low;
          if (_source75.is_Some) {
            DAST._IExpression _2492___mcc_h1064 = _source75.dtor_Some_a0;
            DAST._IExpression _2493_l = _2492___mcc_h1064;
            {
              Dafny.ISequence<Dafny.Rune> _2494_lString;
              bool _2495___v80;
              bool _2496_lErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2497_recIdentsL;
              Dafny.ISequence<Dafny.Rune> _out1535;
              bool _out1536;
              bool _out1537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1538;
              DCOMP.COMP.GenExpr(_2493_l, selfIdent, @params, true, out _out1535, out _out1536, out _out1537, out _out1538);
              _2494_lString = _out1535;
              _2495___v80 = _out1536;
              _2496_lErased = _out1537;
              _2497_recIdentsL = _out1538;
              if (!(_2496_lErased)) {
                _2494_lString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2494_lString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2491_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2494_lString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2497_recIdentsL);
            }
          } else {
          }
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2498_highString;
          _2498_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source76 = _2482_high;
          if (_source76.is_Some) {
            DAST._IExpression _2499___mcc_h1065 = _source76.dtor_Some_a0;
            DAST._IExpression _2500_h = _2499___mcc_h1065;
            {
              Dafny.ISequence<Dafny.Rune> _2501_hString;
              bool _2502___v81;
              bool _2503_hErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2504_recIdentsH;
              Dafny.ISequence<Dafny.Rune> _out1539;
              bool _out1540;
              bool _out1541;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1542;
              DCOMP.COMP.GenExpr(_2500_h, selfIdent, @params, true, out _out1539, out _out1540, out _out1541, out _out1542);
              _2501_hString = _out1539;
              _2502___v81 = _out1540;
              _2503_hErased = _out1541;
              _2504_recIdentsH = _out1542;
              if (!(_2503_hErased)) {
                _2501_hString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2501_hString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2498_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2501_hString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2504_recIdentsH);
            }
          } else {
          }
          if (_2484_isArray) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source77) => {
            if (_source77.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2505___mcc_h1066 = _source77.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2505___mcc_h1066, _pat_let0_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let0_0, _2506_l => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2506_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2491_lowString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source78) => {
            if (_source78.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2507___mcc_h1067 = _source78.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2507___mcc_h1067, _pat_let1_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let1_0, _2508_h => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2508_h), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2498_highString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isErased = _2488_onErased;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".to_vec())"));
          isOwned = true;
        }
      } else if (_source22.is_TupleSelect) {
        DAST._IExpression _2509___mcc_h175 = _source22.dtor_expr;
        BigInteger _2510___mcc_h176 = _source22.dtor_index;
        BigInteger _2511_idx = _2510___mcc_h176;
        DAST._IExpression _2512_on = _2509___mcc_h175;
        {
          Dafny.ISequence<Dafny.Rune> _2513_onString;
          bool _2514___v82;
          bool _2515_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2516_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1543;
          bool _out1544;
          bool _out1545;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1546;
          DCOMP.COMP.GenExpr(_2512_on, selfIdent, @params, false, out _out1543, out _out1544, out _out1545, out _out1546);
          _2513_onString = _out1543;
          _2514___v82 = _out1544;
          _2515_tupErased = _out1545;
          _2516_recIdents = _out1546;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2513_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_2511_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _2515_tupErased;
          readIdents = _2516_recIdents;
        }
      } else if (_source22.is_Call) {
        DAST._IExpression _2517___mcc_h177 = _source22.dtor_on;
        Dafny.ISequence<Dafny.Rune> _2518___mcc_h178 = _source22.dtor_name;
        Dafny.ISequence<DAST._IType> _2519___mcc_h179 = _source22.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2520___mcc_h180 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2521_args = _2520___mcc_h180;
        Dafny.ISequence<DAST._IType> _2522_typeArgs = _2519___mcc_h179;
        Dafny.ISequence<Dafny.Rune> _2523_name = _2518___mcc_h178;
        DAST._IExpression _2524_on = _2517___mcc_h177;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2525_typeArgString;
          _2525_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2522_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2526_typeI;
            _2526_typeI = BigInteger.Zero;
            _2525_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_2526_typeI) < (new BigInteger((_2522_typeArgs).Count))) {
              if ((_2526_typeI).Sign == 1) {
                _2525_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2525_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _2527_typeString;
              Dafny.ISequence<Dafny.Rune> _out1547;
              _out1547 = DCOMP.COMP.GenType((_2522_typeArgs).Select(_2526_typeI), false, false);
              _2527_typeString = _out1547;
              _2525_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2525_typeArgString, _2527_typeString);
              _2526_typeI = (_2526_typeI) + (BigInteger.One);
            }
            _2525_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2525_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _2528_argString;
          _2528_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2529_i;
          _2529_i = BigInteger.Zero;
          while ((_2529_i) < (new BigInteger((_2521_args).Count))) {
            if ((_2529_i).Sign == 1) {
              _2528_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2528_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2530_argExpr;
            bool _2531_isOwned;
            bool _2532_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2533_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1548;
            bool _out1549;
            bool _out1550;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1551;
            DCOMP.COMP.GenExpr((_2521_args).Select(_2529_i), selfIdent, @params, false, out _out1548, out _out1549, out _out1550, out _out1551);
            _2530_argExpr = _out1548;
            _2531_isOwned = _out1549;
            _2532_argErased = _out1550;
            _2533_argIdents = _out1551;
            if (_2531_isOwned) {
              _2530_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2530_argExpr);
            }
            _2528_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2528_argString, _2530_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2533_argIdents);
            _2529_i = (_2529_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2534_enclosingString;
          bool _2535___v83;
          bool _2536___v84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2537_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1552;
          bool _out1553;
          bool _out1554;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1555;
          DCOMP.COMP.GenExpr(_2524_on, selfIdent, @params, false, out _out1552, out _out1553, out _out1554, out _out1555);
          _2534_enclosingString = _out1552;
          _2535___v83 = _out1553;
          _2536___v84 = _out1554;
          _2537_recIdents = _out1555;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2537_recIdents);
          DAST._IExpression _source79 = _2524_on;
          if (_source79.is_Literal) {
            DAST._ILiteral _2538___mcc_h1068 = _source79.dtor_Literal_a0;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2539___mcc_h1070 = _source79.dtor_Ident_a0;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2540___mcc_h1072 = _source79.dtor_Companion_a0;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2534_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (_2523_name));
            }
          } else if (_source79.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2541___mcc_h1074 = _source79.dtor_Tuple_a0;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2542___mcc_h1076 = _source79.dtor_path;
            Dafny.ISequence<DAST._IExpression> _2543___mcc_h1077 = _source79.dtor_args;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2544___mcc_h1080 = _source79.dtor_dims;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2545___mcc_h1082 = _source79.dtor_path;
            Dafny.ISequence<Dafny.Rune> _2546___mcc_h1083 = _source79.dtor_variant;
            bool _2547___mcc_h1084 = _source79.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2548___mcc_h1085 = _source79.dtor_contents;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Convert) {
            DAST._IExpression _2549___mcc_h1090 = _source79.dtor_value;
            DAST._IType _2550___mcc_h1091 = _source79.dtor_from;
            DAST._IType _2551___mcc_h1092 = _source79.dtor_typ;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2552___mcc_h1096 = _source79.dtor_elements;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2553___mcc_h1098 = _source79.dtor_elements;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_This) {
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Ite) {
            DAST._IExpression _2554___mcc_h1100 = _source79.dtor_cond;
            DAST._IExpression _2555___mcc_h1101 = _source79.dtor_thn;
            DAST._IExpression _2556___mcc_h1102 = _source79.dtor_els;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_UnOp) {
            DAST._IUnaryOp _2557___mcc_h1106 = _source79.dtor_unOp;
            DAST._IExpression _2558___mcc_h1107 = _source79.dtor_expr;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _2559___mcc_h1110 = _source79.dtor_op;
            DAST._IExpression _2560___mcc_h1111 = _source79.dtor_left;
            DAST._IExpression _2561___mcc_h1112 = _source79.dtor_right;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_ArrayLen) {
            DAST._IExpression _2562___mcc_h1116 = _source79.dtor_expr;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Select) {
            DAST._IExpression _2563___mcc_h1118 = _source79.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2564___mcc_h1119 = _source79.dtor_field;
            bool _2565___mcc_h1120 = _source79.dtor_isConstant;
            bool _2566___mcc_h1121 = _source79.dtor_onDatatype;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_SelectFn) {
            DAST._IExpression _2567___mcc_h1126 = _source79.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2568___mcc_h1127 = _source79.dtor_field;
            bool _2569___mcc_h1128 = _source79.dtor_onDatatype;
            bool _2570___mcc_h1129 = _source79.dtor_isStatic;
            BigInteger _2571___mcc_h1130 = _source79.dtor_arity;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Index) {
            DAST._IExpression _2572___mcc_h1136 = _source79.dtor_expr;
            bool _2573___mcc_h1137 = _source79.dtor_isArray;
            Dafny.ISequence<DAST._IExpression> _2574___mcc_h1138 = _source79.dtor_indices;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_IndexRange) {
            DAST._IExpression _2575___mcc_h1142 = _source79.dtor_expr;
            bool _2576___mcc_h1143 = _source79.dtor_isArray;
            DAST._IOptional<DAST._IExpression> _2577___mcc_h1144 = _source79.dtor_low;
            DAST._IOptional<DAST._IExpression> _2578___mcc_h1145 = _source79.dtor_high;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_TupleSelect) {
            DAST._IExpression _2579___mcc_h1150 = _source79.dtor_expr;
            BigInteger _2580___mcc_h1151 = _source79.dtor_index;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Call) {
            DAST._IExpression _2581___mcc_h1154 = _source79.dtor_on;
            Dafny.ISequence<Dafny.Rune> _2582___mcc_h1155 = _source79.dtor_name;
            Dafny.ISequence<DAST._IType> _2583___mcc_h1156 = _source79.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2584___mcc_h1157 = _source79.dtor_args;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2585___mcc_h1162 = _source79.dtor_params;
            DAST._IType _2586___mcc_h1163 = _source79.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2587___mcc_h1164 = _source79.dtor_body;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2588___mcc_h1168 = _source79.dtor_values;
            DAST._IType _2589___mcc_h1169 = _source79.dtor_retType;
            DAST._IExpression _2590___mcc_h1170 = _source79.dtor_expr;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2591___mcc_h1174 = _source79.dtor_name;
            DAST._IType _2592___mcc_h1175 = _source79.dtor_typ;
            DAST._IExpression _2593___mcc_h1176 = _source79.dtor_value;
            DAST._IExpression _2594___mcc_h1177 = _source79.dtor_iifeBody;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_Apply) {
            DAST._IExpression _2595___mcc_h1182 = _source79.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2596___mcc_h1183 = _source79.dtor_args;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else if (_source79.is_TypeTest) {
            DAST._IExpression _2597___mcc_h1186 = _source79.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2598___mcc_h1187 = _source79.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2599___mcc_h1188 = _source79.dtor_variant;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          } else {
            DAST._IType _2600___mcc_h1192 = _source79.dtor_typ;
            {
              _2534_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2534_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2523_name));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2534_enclosingString, _2525_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2528_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2601___mcc_h181 = _source22.dtor_params;
        DAST._IType _2602___mcc_h182 = _source22.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2603___mcc_h183 = _source22.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2604_body = _2603___mcc_h183;
        DAST._IType _2605_retType = _2602___mcc_h182;
        Dafny.ISequence<DAST._IFormal> _2606_params = _2601___mcc_h181;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2607_paramNames;
          _2607_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2608_i;
          _2608_i = BigInteger.Zero;
          while ((_2608_i) < (new BigInteger((_2606_params).Count))) {
            _2607_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2607_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2606_params).Select(_2608_i)).dtor_name));
            _2608_i = (_2608_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2609_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2610_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1556;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1557;
          DCOMP.COMP.GenStmts(_2604_body, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), _2607_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1556, out _out1557);
          _2609_recursiveGen = _out1556;
          _2610_recIdents = _out1557;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2611_allReadCloned;
          _2611_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2610_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2612_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2610_recIdents).Elements) {
              _2612_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2610_recIdents).Contains(_2612_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1754)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2607_paramNames).Contains(_2612_next))) {
              _2611_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2611_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2612_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2612_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2612_next));
            }
            _2610_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2610_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2612_next));
          }
          Dafny.ISequence<Dafny.Rune> _2613_paramsString;
          _2613_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Dafny.ISequence<Dafny.Rune> _2614_paramTypes;
          _2614_paramTypes = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2608_i = BigInteger.Zero;
          while ((_2608_i) < (new BigInteger((_2606_params).Count))) {
            if ((_2608_i).Sign == 1) {
              _2613_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2613_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              _2614_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_2614_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2615_typStr;
            Dafny.ISequence<Dafny.Rune> _out1558;
            _out1558 = DCOMP.COMP.GenType(((_2606_params).Select(_2608_i)).dtor_typ, false, true);
            _2615_typStr = _out1558;
            _2613_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2613_paramsString, ((_2606_params).Select(_2608_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2615_typStr);
            _2614_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2614_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), _2615_typStr);
            _2608_i = (_2608_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2616_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1559;
          _out1559 = DCOMP.COMP.GenType(_2605_retType, false, true);
          _2616_retTypeGen = _out1559;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn Fn("), _2614_paramTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _2616_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>({\n")), _2611_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(move |")), _2613_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2616_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2609_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2617___mcc_h184 = _source22.dtor_values;
        DAST._IType _2618___mcc_h185 = _source22.dtor_retType;
        DAST._IExpression _2619___mcc_h186 = _source22.dtor_expr;
        DAST._IExpression _2620_expr = _2619___mcc_h186;
        DAST._IType _2621_retType = _2618___mcc_h185;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2622_values = _2617___mcc_h184;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2623_paramNames;
          _2623_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2624_paramNamesSet;
          _2624_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2625_i;
          _2625_i = BigInteger.Zero;
          while ((_2625_i) < (new BigInteger((_2622_values).Count))) {
            _2623_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2623_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((_2622_values).Select(_2625_i)).dtor__0).dtor_name));
            _2624_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2624_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((((_2622_values).Select(_2625_i)).dtor__0).dtor_name));
            _2625_i = (_2625_i) + (BigInteger.One);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          Dafny.ISequence<Dafny.Rune> _2626_paramsString;
          _2626_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2625_i = BigInteger.Zero;
          while ((_2625_i) < (new BigInteger((_2622_values).Count))) {
            if ((_2625_i).Sign == 1) {
              _2626_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2626_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2627_typStr;
            Dafny.ISequence<Dafny.Rune> _out1560;
            _out1560 = DCOMP.COMP.GenType((((_2622_values).Select(_2625_i)).dtor__0).dtor_typ, false, true);
            _2627_typStr = _out1560;
            Dafny.ISequence<Dafny.Rune> _2628_valueGen;
            bool _2629___v87;
            bool _2630_valueErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2631_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1561;
            bool _out1562;
            bool _out1563;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1564;
            DCOMP.COMP.GenExpr(((_2622_values).Select(_2625_i)).dtor__1, selfIdent, @params, true, out _out1561, out _out1562, out _out1563, out _out1564);
            _2628_valueGen = _out1561;
            _2629___v87 = _out1562;
            _2630_valueErased = _out1563;
            _2631_recIdents = _out1564;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), (((_2622_values).Select(_2625_i)).dtor__0).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _2627_typStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2631_recIdents);
            if (_2630_valueErased) {
              _2628_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2628_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _2628_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            _2625_i = (_2625_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2632_recGen;
          bool _2633_recOwned;
          bool _2634_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2635_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1565;
          bool _out1566;
          bool _out1567;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1568;
          DCOMP.COMP.GenExpr(_2620_expr, selfIdent, _2623_paramNames, mustOwn, out _out1565, out _out1566, out _out1567, out _out1568);
          _2632_recGen = _out1565;
          _2633_recOwned = _out1566;
          _2634_recErased = _out1567;
          _2635_recIdents = _out1568;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2635_recIdents, _2624_paramNamesSet);
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _2632_recGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2633_recOwned;
          isErased = _2634_recErased;
        }
      } else if (_source22.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2636___mcc_h187 = _source22.dtor_name;
        DAST._IType _2637___mcc_h188 = _source22.dtor_typ;
        DAST._IExpression _2638___mcc_h189 = _source22.dtor_value;
        DAST._IExpression _2639___mcc_h190 = _source22.dtor_iifeBody;
        DAST._IExpression _2640_iifeBody = _2639___mcc_h190;
        DAST._IExpression _2641_value = _2638___mcc_h189;
        DAST._IType _2642_tpe = _2637___mcc_h188;
        Dafny.ISequence<Dafny.Rune> _2643_name = _2636___mcc_h187;
        {
          Dafny.ISequence<Dafny.Rune> _2644_valueGen;
          bool _2645_valueOwned;
          bool _2646_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2647_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1569;
          bool _out1570;
          bool _out1571;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1572;
          DCOMP.COMP.GenExpr(_2641_value, selfIdent, @params, false, out _out1569, out _out1570, out _out1571, out _out1572);
          _2644_valueGen = _out1569;
          _2645_valueOwned = _out1570;
          _2646_valueErased = _out1571;
          _2647_recIdents = _out1572;
          if (_2646_valueErased) {
            Dafny.ISequence<Dafny.Rune> _2648_eraseFn;
            _2648_eraseFn = ((_2645_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
            _2644_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::"), _2648_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2644_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2647_recIdents;
          Dafny.ISequence<Dafny.Rune> _2649_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1573;
          _out1573 = DCOMP.COMP.GenType(_2642_tpe, false, true);
          _2649_valueTypeGen = _out1573;
          Dafny.ISequence<Dafny.Rune> _2650_bodyGen;
          bool _2651_bodyOwned;
          bool _2652_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2653_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1574;
          bool _out1575;
          bool _out1576;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1577;
          DCOMP.COMP.GenExpr(_2640_iifeBody, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, ((_2645_valueOwned) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2643_name))))), mustOwn, out _out1574, out _out1575, out _out1576, out _out1577);
          _2650_bodyGen = _out1574;
          _2651_bodyOwned = _out1575;
          _2652_bodyErased = _out1576;
          _2653_bodyIdents = _out1577;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2653_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2643_name))));
          Dafny.ISequence<Dafny.Rune> _2654_eraseFn;
          _2654_eraseFn = ((_2645_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2643_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((_2645_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")))), _2649_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2644_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2650_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2651_bodyOwned;
          isErased = _2652_bodyErased;
        }
      } else if (_source22.is_Apply) {
        DAST._IExpression _2655___mcc_h191 = _source22.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2656___mcc_h192 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2657_args = _2656___mcc_h192;
        DAST._IExpression _2658_func = _2655___mcc_h191;
        {
          Dafny.ISequence<Dafny.Rune> _2659_funcString;
          bool _2660___v88;
          bool _2661_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2662_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1578;
          bool _out1579;
          bool _out1580;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1581;
          DCOMP.COMP.GenExpr(_2658_func, selfIdent, @params, false, out _out1578, out _out1579, out _out1580, out _out1581);
          _2659_funcString = _out1578;
          _2660___v88 = _out1579;
          _2661_funcErased = _out1580;
          _2662_recIdents = _out1581;
          readIdents = _2662_recIdents;
          Dafny.ISequence<Dafny.Rune> _2663_argString;
          _2663_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2664_i;
          _2664_i = BigInteger.Zero;
          while ((_2664_i) < (new BigInteger((_2657_args).Count))) {
            if ((_2664_i).Sign == 1) {
              _2663_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2663_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2665_argExpr;
            bool _2666_isOwned;
            bool _2667_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2668_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1582;
            bool _out1583;
            bool _out1584;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1585;
            DCOMP.COMP.GenExpr((_2657_args).Select(_2664_i), selfIdent, @params, false, out _out1582, out _out1583, out _out1584, out _out1585);
            _2665_argExpr = _out1582;
            _2666_isOwned = _out1583;
            _2667_argErased = _out1584;
            _2668_argIdents = _out1585;
            if (_2666_isOwned) {
              _2665_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2665_argExpr);
            }
            _2663_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2663_argString, _2665_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2668_argIdents);
            _2664_i = (_2664_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2659_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2663_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_TypeTest) {
        DAST._IExpression _2669___mcc_h193 = _source22.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2670___mcc_h194 = _source22.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2671___mcc_h195 = _source22.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2672_variant = _2671___mcc_h195;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2673_dType = _2670___mcc_h194;
        DAST._IExpression _2674_on = _2669___mcc_h193;
        {
          Dafny.ISequence<Dafny.Rune> _2675_exprGen;
          bool _2676___v89;
          bool _2677_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2678_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1586;
          bool _out1587;
          bool _out1588;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1589;
          DCOMP.COMP.GenExpr(_2674_on, selfIdent, @params, false, out _out1586, out _out1587, out _out1588, out _out1589);
          _2675_exprGen = _out1586;
          _2676___v89 = _out1587;
          _2677_exprErased = _out1588;
          _2678_recIdents = _out1589;
          Dafny.ISequence<Dafny.Rune> _2679_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1590;
          _out1590 = DCOMP.COMP.GenPath(_2673_dType);
          _2679_dTypePath = _out1590;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2675_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2679_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2672_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2678_recIdents;
        }
      } else {
        DAST._IType _2680___mcc_h196 = _source22.dtor_typ;
        DAST._IType _2681_typ = _2680___mcc_h196;
        {
          Dafny.ISequence<Dafny.Rune> _2682_typString;
          Dafny.ISequence<Dafny.Rune> _out1591;
          _out1591 = DCOMP.COMP.GenType(_2681_typ, false, false);
          _2682_typString = _out1591;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2682_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
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
      BigInteger _2683_i;
      _2683_i = BigInteger.Zero;
      while ((_2683_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2684_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1592;
        _out1592 = DCOMP.COMP.GenModule((p).Select(_2683_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2684_generated = _out1592;
        if ((_2683_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2684_generated);
        _2683_i = (_2683_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2685_i;
      _2685_i = BigInteger.Zero;
      while ((_2685_i) < (new BigInteger((fullName).Count))) {
        if ((_2685_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2685_i));
        _2685_i = (_2685_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

