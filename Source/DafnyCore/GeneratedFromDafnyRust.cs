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
      hash = ((hash << 5) + hash) + 7;
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
      hash = ((hash << 5) + hash) + 8;
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
      hash = ((hash << 5) + hash) + 9;
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
      hash = ((hash << 5) + hash) + 10;
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
    DAST._IExpression dtor_idx { get; }
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
    public static _IAssignLhs create_Index(DAST._IExpression expr, DAST._IExpression idx) {
      return new AssignLhs_Index(expr, idx);
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
    public DAST._IExpression dtor_idx {
      get {
        var d = this;
        return ((AssignLhs_Index)d)._idx;
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
    public readonly DAST._IExpression _idx;
    public AssignLhs_Index(DAST._IExpression expr, DAST._IExpression idx) : base() {
      this._expr = expr;
      this._idx = idx;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Index(_expr, _idx);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.AssignLhs_Index;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._idx, oth._idx);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._idx));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.AssignLhs.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._idx);
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
    DAST._IExpression dtor_idx { get; }
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
    public static _IExpression create_ArrayLen(DAST._IExpression expr) {
      return new Expression_ArrayLen(expr);
    }
    public static _IExpression create_Select(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool isConstant, bool onDatatype) {
      return new Expression_Select(expr, field, isConstant, onDatatype);
    }
    public static _IExpression create_SelectFn(DAST._IExpression expr, Dafny.ISequence<Dafny.Rune> field, bool onDatatype, bool isStatic, BigInteger arity) {
      return new Expression_SelectFn(expr, field, onDatatype, isStatic, arity);
    }
    public static _IExpression create_Index(DAST._IExpression expr, DAST._IExpression idx) {
      return new Expression_Index(expr, idx);
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
    public bool is_ArrayLen { get { return this is Expression_ArrayLen; } }
    public bool is_Select { get { return this is Expression_Select; } }
    public bool is_SelectFn { get { return this is Expression_SelectFn; } }
    public bool is_Index { get { return this is Expression_Index; } }
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
        if (d is Expression_ArrayLen) { return ((Expression_ArrayLen)d)._expr; }
        if (d is Expression_Select) { return ((Expression_Select)d)._expr; }
        if (d is Expression_SelectFn) { return ((Expression_SelectFn)d)._expr; }
        if (d is Expression_Index) { return ((Expression_Index)d)._expr; }
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
    public DAST._IExpression dtor_idx {
      get {
        var d = this;
        return ((Expression_Index)d)._idx;
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
    public readonly DAST._IExpression _idx;
    public Expression_Index(DAST._IExpression expr, DAST._IExpression idx) : base() {
      this._expr = expr;
      this._idx = idx;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Index(_expr, _idx);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Index;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._idx, oth._idx);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._idx));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._idx);
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
      hash = ((hash << 5) + hash) + 18;
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
      hash = ((hash << 5) + hash) + 19;
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
      hash = ((hash << 5) + hash) + 20;
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
      hash = ((hash << 5) + hash) + 21;
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
      hash = ((hash << 5) + hash) + 22;
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
      hash = ((hash << 5) + hash) + 23;
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
      hash = ((hash << 5) + hash) + 24;
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
          if (inBinding) {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<_>");
          } else {
            if (inFn) {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<::std::boxed::Box<dyn ::std::ops::Fn(");
            } else {
              s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper<impl ::std::ops::Fn(");
            }
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
            _out52 = DCOMP.COMP.GenType(_163_result, inBinding, inFn);
            _167_resultType = _out52;
            if (inFn) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _167_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + 'static>>"));
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _167_resultType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + Clone + 'static>"));
            }
          }
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _207_i;
      _207_i = BigInteger.Zero;
      while ((_207_i) < (new BigInteger((stmts).Count))) {
        DAST._IStatement _208_stmt;
        _208_stmt = (stmts).Select(_207_i);
        Dafny.ISequence<Dafny.Rune> _209_stmtString;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _210_recIdents;
        Dafny.ISequence<Dafny.Rune> _out62;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out63;
        DCOMP.COMP.GenStmt(_208_stmt, selfIdent, @params, (isLast) && ((_207_i) == ((new BigInteger((stmts).Count)) - (BigInteger.One))), earlyReturn, out _out62, out _out63);
        _209_stmtString = _out62;
        _210_recIdents = _out63;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _210_recIdents);
        if ((_207_i).Sign == 1) {
          generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, _209_stmtString);
        _207_i = (_207_i) + (BigInteger.One);
      }
    }
    public static void GenAssignLhs(DAST._IAssignLhs lhs, Dafny.ISequence<Dafny.Rune> rhs, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, out Dafny.ISequence<Dafny.Rune> generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IAssignLhs _source13 = lhs;
      if (_source13.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _211___mcc_h0 = _source13.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _source14 = _211___mcc_h0;
        Dafny.ISequence<Dafny.Rune> _212___mcc_h1 = _source14;
        Dafny.ISequence<Dafny.Rune> _213_id = _212___mcc_h1;
        {
          if ((@params).Contains(_213_id)) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*r#"), _213_id);
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _213_id);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_213_id);
          needsIIFE = false;
        }
      } else if (_source13.is_Select) {
        DAST._IExpression _214___mcc_h2 = _source13.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _215___mcc_h3 = _source13.dtor_field;
        Dafny.ISequence<Dafny.Rune> _216_field = _215___mcc_h3;
        DAST._IExpression _217_on = _214___mcc_h2;
        {
          Dafny.ISequence<Dafny.Rune> _218_onExpr;
          bool _219_onOwned;
          bool _220_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _221_recIdents;
          Dafny.ISequence<Dafny.Rune> _out64;
          bool _out65;
          bool _out66;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out67;
          DCOMP.COMP.GenExpr(_217_on, selfIdent, @params, false, out _out64, out _out65, out _out66, out _out67);
          _218_onExpr = _out64;
          _219_onOwned = _out65;
          _220_onErased = _out66;
          _221_recIdents = _out67;
          if (!(_220_onErased)) {
            Dafny.ISequence<Dafny.Rune> _222_eraseFn;
            _222_eraseFn = ((_219_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _218_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _222_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _218_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*("), _218_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _216_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()) = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          readIdents = _221_recIdents;
          needsIIFE = true;
        }
      } else {
        DAST._IExpression _223___mcc_h4 = _source13.dtor_expr;
        DAST._IExpression _224___mcc_h5 = _source13.dtor_idx;
        DAST._IExpression _225_idx = _224___mcc_h5;
        DAST._IExpression _226_on = _223___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _227_onExpr;
          bool _228_onOwned;
          bool _229_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _230_recIdents;
          Dafny.ISequence<Dafny.Rune> _out68;
          bool _out69;
          bool _out70;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out71;
          DCOMP.COMP.GenExpr(_226_on, selfIdent, @params, false, out _out68, out _out69, out _out70, out _out71);
          _227_onExpr = _out68;
          _228_onOwned = _out69;
          _229_onErased = _out70;
          _230_recIdents = _out71;
          if (!(_229_onErased)) {
            Dafny.ISequence<Dafny.Rune> _231_eraseFn;
            _231_eraseFn = ((_228_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _227_onExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _231_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _227_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _232_idxString;
          bool _233___v13;
          bool _234_idxErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _235_idxIdents;
          Dafny.ISequence<Dafny.Rune> _out72;
          bool _out73;
          bool _out74;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out75;
          DCOMP.COMP.GenExpr(_225_idx, selfIdent, @params, true, out _out72, out _out73, out _out74, out _out75);
          _232_idxString = _out72;
          _233___v13 = _out73;
          _234_idxErased = _out74;
          _235_idxIdents = _out75;
          if (!(_234_idxErased)) {
            _232_idxString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _232_idxString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet __idx = <usize as ::dafny_runtime::NumCast>::from("), _232_idxString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap();\n"));
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, _227_onExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow_mut()[__idx] = ")), rhs), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n}"));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_230_recIdents, _235_idxIdents);
          needsIIFE = true;
        }
      }
    }
    public static void GenStmt(DAST._IStatement stmt, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool isLast, Dafny.ISequence<Dafny.Rune> earlyReturn, out Dafny.ISequence<Dafny.Rune> generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      generated = Dafny.Sequence<Dafny.Rune>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IStatement _source15 = stmt;
      if (_source15.is_DeclareVar) {
        Dafny.ISequence<Dafny.Rune> _236___mcc_h0 = _source15.dtor_name;
        DAST._IType _237___mcc_h1 = _source15.dtor_typ;
        DAST._IOptional<DAST._IExpression> _238___mcc_h2 = _source15.dtor_maybeValue;
        DAST._IOptional<DAST._IExpression> _source16 = _238___mcc_h2;
        if (_source16.is_Some) {
          DAST._IExpression _239___mcc_h3 = _source16.dtor_Some_a0;
          DAST._IExpression _240_expression = _239___mcc_h3;
          DAST._IType _241_typ = _237___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _242_name = _236___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _243_expr;
            bool _244___v14;
            bool _245_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _246_recIdents;
            Dafny.ISequence<Dafny.Rune> _out76;
            bool _out77;
            bool _out78;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out79;
            DCOMP.COMP.GenExpr(_240_expression, selfIdent, @params, true, out _out76, out _out77, out _out78, out _out79);
            _243_expr = _out76;
            _244___v14 = _out77;
            _245_recErased = _out78;
            _246_recIdents = _out79;
            if (_245_recErased) {
              _243_expr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _243_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            Dafny.ISequence<Dafny.Rune> _247_typeString;
            Dafny.ISequence<Dafny.Rune> _out80;
            _out80 = DCOMP.COMP.GenType(_241_typ, true, false);
            _247_typeString = _out80;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _242_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _247_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _243_expr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = _246_recIdents;
          }
        } else {
          DAST._IType _248_typ = _237___mcc_h1;
          Dafny.ISequence<Dafny.Rune> _249_name = _236___mcc_h0;
          {
            Dafny.ISequence<Dafny.Rune> _250_typeString;
            Dafny.ISequence<Dafny.Rune> _out81;
            _out81 = DCOMP.COMP.GenType(_248_typ, true, false);
            _250_typeString = _out81;
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#"), _249_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _250_typeString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        }
      } else if (_source15.is_Assign) {
        DAST._IAssignLhs _251___mcc_h4 = _source15.dtor_lhs;
        DAST._IExpression _252___mcc_h5 = _source15.dtor_value;
        DAST._IExpression _253_expression = _252___mcc_h5;
        DAST._IAssignLhs _254_lhs = _251___mcc_h4;
        {
          Dafny.ISequence<Dafny.Rune> _255_lhsGen;
          bool _256_needsIIFE;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _257_recIdents;
          Dafny.ISequence<Dafny.Rune> _out82;
          bool _out83;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out84;
          DCOMP.COMP.GenAssignLhs(_254_lhs, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__rhs"), selfIdent, @params, out _out82, out _out83, out _out84);
          _255_lhsGen = _out82;
          _256_needsIIFE = _out83;
          _257_recIdents = _out84;
          Dafny.ISequence<Dafny.Rune> _258_exprGen;
          bool _259___v15;
          bool _260_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _261_exprIdents;
          Dafny.ISequence<Dafny.Rune> _out85;
          bool _out86;
          bool _out87;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out88;
          DCOMP.COMP.GenExpr(_253_expression, selfIdent, @params, true, out _out85, out _out86, out _out87, out _out88);
          _258_exprGen = _out85;
          _259___v15 = _out86;
          _260_exprErased = _out87;
          _261_exprIdents = _out88;
          if (_260_exprErased) {
            _258_exprGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _258_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (_256_needsIIFE) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet __rhs = "), _258_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _255_lhsGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_255_lhsGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _258_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_257_recIdents, _261_exprIdents);
        }
      } else if (_source15.is_If) {
        DAST._IExpression _262___mcc_h6 = _source15.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _263___mcc_h7 = _source15.dtor_thn;
        Dafny.ISequence<DAST._IStatement> _264___mcc_h8 = _source15.dtor_els;
        Dafny.ISequence<DAST._IStatement> _265_els = _264___mcc_h8;
        Dafny.ISequence<DAST._IStatement> _266_thn = _263___mcc_h7;
        DAST._IExpression _267_cond = _262___mcc_h6;
        {
          Dafny.ISequence<Dafny.Rune> _268_condString;
          bool _269___v16;
          bool _270_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _271_recIdents;
          Dafny.ISequence<Dafny.Rune> _out89;
          bool _out90;
          bool _out91;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out92;
          DCOMP.COMP.GenExpr(_267_cond, selfIdent, @params, true, out _out89, out _out90, out _out91, out _out92);
          _268_condString = _out89;
          _269___v16 = _out90;
          _270_condErased = _out91;
          _271_recIdents = _out92;
          if (!(_270_condErased)) {
            _268_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _268_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _271_recIdents;
          Dafny.ISequence<Dafny.Rune> _272_thnString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _273_thnIdents;
          Dafny.ISequence<Dafny.Rune> _out93;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out94;
          DCOMP.COMP.GenStmts(_266_thn, selfIdent, @params, isLast, earlyReturn, out _out93, out _out94);
          _272_thnString = _out93;
          _273_thnIdents = _out94;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _273_thnIdents);
          Dafny.ISequence<Dafny.Rune> _274_elsString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _275_elsIdents;
          Dafny.ISequence<Dafny.Rune> _out95;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out96;
          DCOMP.COMP.GenStmts(_265_els, selfIdent, @params, isLast, earlyReturn, out _out95, out _out96);
          _274_elsString = _out95;
          _275_elsIdents = _out96;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _275_elsIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), _268_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _272_thnString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _274_elsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_While) {
        DAST._IExpression _276___mcc_h9 = _source15.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _277___mcc_h10 = _source15.dtor_body;
        Dafny.ISequence<DAST._IStatement> _278_body = _277___mcc_h10;
        DAST._IExpression _279_cond = _276___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _280_condString;
          bool _281___v17;
          bool _282_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _283_recIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          bool _out98;
          bool _out99;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
          DCOMP.COMP.GenExpr(_279_cond, selfIdent, @params, true, out _out97, out _out98, out _out99, out _out100);
          _280_condString = _out97;
          _281___v17 = _out98;
          _282_condErased = _out99;
          _283_recIdents = _out100;
          if (!(_282_condErased)) {
            _280_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase("), _280_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _283_recIdents;
          Dafny.ISequence<Dafny.Rune> _284_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _285_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          DCOMP.COMP.GenStmts(_278_body, selfIdent, @params, false, earlyReturn, out _out101, out _out102);
          _284_bodyString = _out101;
          _285_bodyIdents = _out102;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _285_bodyIdents);
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), _280_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _284_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_Call) {
        DAST._IExpression _286___mcc_h11 = _source15.dtor_on;
        Dafny.ISequence<Dafny.Rune> _287___mcc_h12 = _source15.dtor_name;
        Dafny.ISequence<DAST._IType> _288___mcc_h13 = _source15.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _289___mcc_h14 = _source15.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _290___mcc_h15 = _source15.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _291_maybeOutVars = _290___mcc_h15;
        Dafny.ISequence<DAST._IExpression> _292_args = _289___mcc_h14;
        Dafny.ISequence<DAST._IType> _293_typeArgs = _288___mcc_h13;
        Dafny.ISequence<Dafny.Rune> _294_name = _287___mcc_h12;
        DAST._IExpression _295_on = _286___mcc_h11;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _296_typeArgString;
          _296_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_293_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _297_typeI;
            _297_typeI = BigInteger.Zero;
            _296_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_297_typeI) < (new BigInteger((_293_typeArgs).Count))) {
              if ((_297_typeI).Sign == 1) {
                _296_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_296_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _298_typeString;
              Dafny.ISequence<Dafny.Rune> _out103;
              _out103 = DCOMP.COMP.GenType((_293_typeArgs).Select(_297_typeI), false, false);
              _298_typeString = _out103;
              _296_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_296_typeArgString, _298_typeString);
              _297_typeI = (_297_typeI) + (BigInteger.One);
            }
            _296_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_296_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _299_argString;
          _299_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _300_i;
          _300_i = BigInteger.Zero;
          while ((_300_i) < (new BigInteger((_292_args).Count))) {
            if ((_300_i).Sign == 1) {
              _299_argString = Dafny.Sequence<Dafny.Rune>.Concat(_299_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _301_argExpr;
            bool _302_isOwned;
            bool _303_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _304_argIdents;
            Dafny.ISequence<Dafny.Rune> _out104;
            bool _out105;
            bool _out106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
            DCOMP.COMP.GenExpr((_292_args).Select(_300_i), selfIdent, @params, false, out _out104, out _out105, out _out106, out _out107);
            _301_argExpr = _out104;
            _302_isOwned = _out105;
            _303_argErased = _out106;
            _304_argIdents = _out107;
            if (_302_isOwned) {
              _301_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _301_argExpr);
            }
            _299_argString = Dafny.Sequence<Dafny.Rune>.Concat(_299_argString, _301_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _304_argIdents);
            _300_i = (_300_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _305_enclosingString;
          bool _306___v18;
          bool _307___v19;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _308_enclosingIdents;
          Dafny.ISequence<Dafny.Rune> _out108;
          bool _out109;
          bool _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          DCOMP.COMP.GenExpr(_295_on, selfIdent, @params, false, out _out108, out _out109, out _out110, out _out111);
          _305_enclosingString = _out108;
          _306___v18 = _out109;
          _307___v19 = _out110;
          _308_enclosingIdents = _out111;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _308_enclosingIdents);
          DAST._IExpression _source17 = _295_on;
          if (_source17.is_Literal) {
            DAST._ILiteral _309___mcc_h19 = _source17.dtor_Literal_a0;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _310___mcc_h21 = _source17.dtor_Ident_a0;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _311___mcc_h23 = _source17.dtor_Companion_a0;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_305_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source17.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _312___mcc_h25 = _source17.dtor_Tuple_a0;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _313___mcc_h27 = _source17.dtor_path;
            Dafny.ISequence<DAST._IExpression> _314___mcc_h28 = _source17.dtor_args;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _315___mcc_h31 = _source17.dtor_dims;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _316___mcc_h33 = _source17.dtor_path;
            Dafny.ISequence<Dafny.Rune> _317___mcc_h34 = _source17.dtor_variant;
            bool _318___mcc_h35 = _source17.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _319___mcc_h36 = _source17.dtor_contents;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Convert) {
            DAST._IExpression _320___mcc_h41 = _source17.dtor_value;
            DAST._IType _321___mcc_h42 = _source17.dtor_from;
            DAST._IType _322___mcc_h43 = _source17.dtor_typ;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _323___mcc_h47 = _source17.dtor_elements;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _324___mcc_h49 = _source17.dtor_elements;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_This) {
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Ite) {
            DAST._IExpression _325___mcc_h51 = _source17.dtor_cond;
            DAST._IExpression _326___mcc_h52 = _source17.dtor_thn;
            DAST._IExpression _327___mcc_h53 = _source17.dtor_els;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_UnOp) {
            DAST._IUnaryOp _328___mcc_h57 = _source17.dtor_unOp;
            DAST._IExpression _329___mcc_h58 = _source17.dtor_expr;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _330___mcc_h61 = _source17.dtor_op;
            DAST._IExpression _331___mcc_h62 = _source17.dtor_left;
            DAST._IExpression _332___mcc_h63 = _source17.dtor_right;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_ArrayLen) {
            DAST._IExpression _333___mcc_h67 = _source17.dtor_expr;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Select) {
            DAST._IExpression _334___mcc_h69 = _source17.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _335___mcc_h70 = _source17.dtor_field;
            bool _336___mcc_h71 = _source17.dtor_isConstant;
            bool _337___mcc_h72 = _source17.dtor_onDatatype;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_SelectFn) {
            DAST._IExpression _338___mcc_h77 = _source17.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _339___mcc_h78 = _source17.dtor_field;
            bool _340___mcc_h79 = _source17.dtor_onDatatype;
            bool _341___mcc_h80 = _source17.dtor_isStatic;
            BigInteger _342___mcc_h81 = _source17.dtor_arity;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Index) {
            DAST._IExpression _343___mcc_h87 = _source17.dtor_expr;
            DAST._IExpression _344___mcc_h88 = _source17.dtor_idx;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_TupleSelect) {
            DAST._IExpression _345___mcc_h91 = _source17.dtor_expr;
            BigInteger _346___mcc_h92 = _source17.dtor_index;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Call) {
            DAST._IExpression _347___mcc_h95 = _source17.dtor_on;
            Dafny.ISequence<Dafny.Rune> _348___mcc_h96 = _source17.dtor_name;
            Dafny.ISequence<DAST._IType> _349___mcc_h97 = _source17.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _350___mcc_h98 = _source17.dtor_args;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _351___mcc_h103 = _source17.dtor_params;
            DAST._IType _352___mcc_h104 = _source17.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _353___mcc_h105 = _source17.dtor_body;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _354___mcc_h109 = _source17.dtor_name;
            DAST._IType _355___mcc_h110 = _source17.dtor_typ;
            DAST._IExpression _356___mcc_h111 = _source17.dtor_value;
            DAST._IExpression _357___mcc_h112 = _source17.dtor_iifeBody;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_Apply) {
            DAST._IExpression _358___mcc_h117 = _source17.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _359___mcc_h118 = _source17.dtor_args;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source17.is_TypeTest) {
            DAST._IExpression _360___mcc_h121 = _source17.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _361___mcc_h122 = _source17.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _362___mcc_h123 = _source17.dtor_variant;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _363___mcc_h127 = _source17.dtor_typ;
            {
              _305_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _364_receiver;
          _364_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source18 = _291_maybeOutVars;
          if (_source18.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _365___mcc_h129 = _source18.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _366_outVars = _365___mcc_h129;
            {
              if ((new BigInteger((_366_outVars).Count)) > (BigInteger.One)) {
                _364_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _367_outI;
              _367_outI = BigInteger.Zero;
              while ((_367_outI) < (new BigInteger((_366_outVars).Count))) {
                if ((_367_outI).Sign == 1) {
                  _364_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_364_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _368_outVar;
                _368_outVar = (_366_outVars).Select(_367_outI);
                _364_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_364_receiver, (_368_outVar));
                _367_outI = (_367_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_366_outVars).Count)) > (BigInteger.One)) {
                _364_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_364_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_364_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_364_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _305_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _294_name), _296_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _299_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source15.is_Return) {
        DAST._IExpression _369___mcc_h16 = _source15.dtor_expr;
        DAST._IExpression _370_expr = _369___mcc_h16;
        {
          Dafny.ISequence<Dafny.Rune> _371_exprString;
          bool _372___v22;
          bool _373_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _374_recIdents;
          Dafny.ISequence<Dafny.Rune> _out112;
          bool _out113;
          bool _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          DCOMP.COMP.GenExpr(_370_expr, selfIdent, @params, true, out _out112, out _out113, out _out114, out _out115);
          _371_exprString = _out112;
          _372___v22 = _out113;
          _373_recErased = _out114;
          _374_recIdents = _out115;
          _371_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _371_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _374_recIdents;
          if (isLast) {
            generated = _371_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _371_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source15.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source15.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _375___mcc_h17 = _source15.dtor_body;
        Dafny.ISequence<DAST._IStatement> _376_body = _375___mcc_h17;
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if (!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#_this = self.clone();\n"));
          }
          BigInteger _377_paramI;
          _377_paramI = BigInteger.Zero;
          while ((_377_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _378_param;
            _378_param = (@params).Select(_377_paramI);
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#")), _378_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _378_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
            _377_paramI = (_377_paramI) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _379_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _380_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
          DCOMP.COMP.GenStmts(_376_body, ((!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out116, out _out117);
          _379_bodyString = _out116;
          _380_bodyIdents = _out117;
          readIdents = _380_bodyIdents;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'TAIL_CALL_START: loop {\n")), _379_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_JumpTailCallStart) {
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue 'TAIL_CALL_START;");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source15.is_Halt) {
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"Halt\");");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else {
        DAST._IExpression _381___mcc_h18 = _source15.dtor_Print_a0;
        DAST._IExpression _382_e = _381___mcc_h18;
        {
          Dafny.ISequence<Dafny.Rune> _383_printedExpr;
          bool _384_isOwned;
          bool _385___v23;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _386_recIdents;
          Dafny.ISequence<Dafny.Rune> _out118;
          bool _out119;
          bool _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          DCOMP.COMP.GenExpr(_382_e, selfIdent, @params, false, out _out118, out _out119, out _out120, out _out121);
          _383_printedExpr = _out118;
          _384_isOwned = _out119;
          _385___v23 = _out120;
          _386_recIdents = _out121;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_384_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _383_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _386_recIdents;
        }
      }
    }
    public static void GenExpr(DAST._IExpression e, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool mustOwn, out Dafny.ISequence<Dafny.Rune> s, out bool isOwned, out bool isErased, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      isOwned = false;
      isErased = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source19 = e;
      if (_source19.is_Literal) {
        DAST._ILiteral _387___mcc_h0 = _source19.dtor_Literal_a0;
        DAST._ILiteral _source20 = _387___mcc_h0;
        if (_source20.is_BoolLiteral) {
          bool _388___mcc_h1 = _source20.dtor_BoolLiteral_a0;
          if ((_388___mcc_h1) == (false)) {
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
          Dafny.ISequence<Dafny.Rune> _389___mcc_h2 = _source20.dtor_IntLiteral_a0;
          DAST._IType _390___mcc_h3 = _source20.dtor_IntLiteral_a1;
          DAST._IType _391_t = _390___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _392_i = _389___mcc_h2;
          {
            DAST._IType _source21 = _391_t;
            if (_source21.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _393___mcc_h173 = _source21.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _394___mcc_h174 = _source21.dtor_typeArgs;
              DAST._IResolvedType _395___mcc_h175 = _source21.dtor_resolved;
              {
                s = _392_i;
              }
            } else if (_source21.is_Nullable) {
              DAST._IType _396___mcc_h179 = _source21.dtor_Nullable_a0;
              {
                s = _392_i;
              }
            } else if (_source21.is_Tuple) {
              Dafny.ISequence<DAST._IType> _397___mcc_h181 = _source21.dtor_Tuple_a0;
              {
                s = _392_i;
              }
            } else if (_source21.is_Array) {
              DAST._IType _398___mcc_h183 = _source21.dtor_element;
              {
                s = _392_i;
              }
            } else if (_source21.is_Seq) {
              DAST._IType _399___mcc_h185 = _source21.dtor_element;
              {
                s = _392_i;
              }
            } else if (_source21.is_Set) {
              DAST._IType _400___mcc_h187 = _source21.dtor_element;
              {
                s = _392_i;
              }
            } else if (_source21.is_Multiset) {
              DAST._IType _401___mcc_h189 = _source21.dtor_element;
              {
                s = _392_i;
              }
            } else if (_source21.is_Map) {
              DAST._IType _402___mcc_h191 = _source21.dtor_key;
              DAST._IType _403___mcc_h192 = _source21.dtor_value;
              {
                s = _392_i;
              }
            } else if (_source21.is_Arrow) {
              Dafny.ISequence<DAST._IType> _404___mcc_h195 = _source21.dtor_args;
              DAST._IType _405___mcc_h196 = _source21.dtor_result;
              {
                s = _392_i;
              }
            } else if (_source21.is_Primitive) {
              DAST._IPrimitive _406___mcc_h199 = _source21.dtor_Primitive_a0;
              DAST._IPrimitive _source22 = _406___mcc_h199;
              if (_source22.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _392_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source22.is_Real) {
                {
                  s = _392_i;
                }
              } else if (_source22.is_String) {
                {
                  s = _392_i;
                }
              } else if (_source22.is_Bool) {
                {
                  s = _392_i;
                }
              } else {
                {
                  s = _392_i;
                }
              }
            } else if (_source21.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _407___mcc_h201 = _source21.dtor_Passthrough_a0;
              {
                s = _392_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _408___mcc_h203 = _source21.dtor_TypeArg_a0;
              {
                s = _392_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _409___mcc_h4 = _source20.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _410___mcc_h5 = _source20.dtor_DecLiteral_a1;
          DAST._IType _411___mcc_h6 = _source20.dtor_DecLiteral_a2;
          DAST._IType _412_t = _411___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _413_d = _410___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _414_n = _409___mcc_h4;
          {
            DAST._IType _source23 = _412_t;
            if (_source23.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _415___mcc_h205 = _source23.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _416___mcc_h206 = _source23.dtor_typeArgs;
              DAST._IResolvedType _417___mcc_h207 = _source23.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Nullable) {
              DAST._IType _418___mcc_h211 = _source23.dtor_Nullable_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Tuple) {
              Dafny.ISequence<DAST._IType> _419___mcc_h213 = _source23.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Array) {
              DAST._IType _420___mcc_h215 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Seq) {
              DAST._IType _421___mcc_h217 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Set) {
              DAST._IType _422___mcc_h219 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Multiset) {
              DAST._IType _423___mcc_h221 = _source23.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Map) {
              DAST._IType _424___mcc_h223 = _source23.dtor_key;
              DAST._IType _425___mcc_h224 = _source23.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Arrow) {
              Dafny.ISequence<DAST._IType> _426___mcc_h227 = _source23.dtor_args;
              DAST._IType _427___mcc_h228 = _source23.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source23.is_Primitive) {
              DAST._IPrimitive _428___mcc_h231 = _source23.dtor_Primitive_a0;
              DAST._IPrimitive _source24 = _428___mcc_h231;
              if (_source24.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source24.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _414_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source24.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source24.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source23.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _429___mcc_h233 = _source23.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _430___mcc_h235 = _source23.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_414_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _413_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _431___mcc_h7 = _source20.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _432_l = _431___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _432_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source20.is_CharLiteral) {
          Dafny.Rune _433___mcc_h8 = _source20.dtor_CharLiteral_a0;
          Dafny.Rune _434_c = _433___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_434_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
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
        Dafny.ISequence<Dafny.Rune> _435___mcc_h9 = _source19.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _436_name = _435___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _436_name);
          if (!((@params).Contains(_436_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_436_name);
        }
      } else if (_source19.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _437___mcc_h10 = _source19.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _438_path = _437___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out122;
          _out122 = DCOMP.COMP.GenPath(_438_path);
          s = _out122;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source19.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _439___mcc_h11 = _source19.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _440_values = _439___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _441_i;
          _441_i = BigInteger.Zero;
          bool _442_allErased;
          _442_allErased = true;
          while ((_441_i) < (new BigInteger((_440_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _443___v26;
            bool _444___v27;
            bool _445_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _446___v28;
            Dafny.ISequence<Dafny.Rune> _out123;
            bool _out124;
            bool _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            DCOMP.COMP.GenExpr((_440_values).Select(_441_i), selfIdent, @params, true, out _out123, out _out124, out _out125, out _out126);
            _443___v26 = _out123;
            _444___v27 = _out124;
            _445_isErased = _out125;
            _446___v28 = _out126;
            _442_allErased = (_442_allErased) && (_445_isErased);
            _441_i = (_441_i) + (BigInteger.One);
          }
          _441_i = BigInteger.Zero;
          while ((_441_i) < (new BigInteger((_440_values).Count))) {
            if ((_441_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _447_recursiveGen;
            bool _448___v29;
            bool _449_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _450_recIdents;
            Dafny.ISequence<Dafny.Rune> _out127;
            bool _out128;
            bool _out129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
            DCOMP.COMP.GenExpr((_440_values).Select(_441_i), selfIdent, @params, true, out _out127, out _out128, out _out129, out _out130);
            _447_recursiveGen = _out127;
            _448___v29 = _out128;
            _449_isErased = _out129;
            _450_recIdents = _out130;
            if ((_449_isErased) && (!(_442_allErased))) {
              _447_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _447_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _447_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _450_recIdents);
            _441_i = (_441_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _442_allErased;
        }
      } else if (_source19.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _451___mcc_h12 = _source19.dtor_path;
        Dafny.ISequence<DAST._IExpression> _452___mcc_h13 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _453_args = _452___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _454_path = _451___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _455_path;
          Dafny.ISequence<Dafny.Rune> _out131;
          _out131 = DCOMP.COMP.GenPath(_454_path);
          _455_path = _out131;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _455_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _456_i;
          _456_i = BigInteger.Zero;
          while ((_456_i) < (new BigInteger((_453_args).Count))) {
            if ((_456_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _457_recursiveGen;
            bool _458___v30;
            bool _459_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _460_recIdents;
            Dafny.ISequence<Dafny.Rune> _out132;
            bool _out133;
            bool _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            DCOMP.COMP.GenExpr((_453_args).Select(_456_i), selfIdent, @params, true, out _out132, out _out133, out _out134, out _out135);
            _457_recursiveGen = _out132;
            _458___v30 = _out133;
            _459_isErased = _out134;
            _460_recIdents = _out135;
            if (_459_isErased) {
              _457_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _457_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _457_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _460_recIdents);
            _456_i = (_456_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _461___mcc_h14 = _source19.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _462_dims = _461___mcc_h14;
        {
          BigInteger _463_i;
          _463_i = (new BigInteger((_462_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_463_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _464_recursiveGen;
            bool _465___v31;
            bool _466_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _467_recIdents;
            Dafny.ISequence<Dafny.Rune> _out136;
            bool _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP.COMP.GenExpr((_462_dims).Select(_463_i), selfIdent, @params, true, out _out136, out _out137, out _out138, out _out139);
            _464_recursiveGen = _out136;
            _465___v31 = _out137;
            _466_isErased = _out138;
            _467_recIdents = _out139;
            if (!(_466_isErased)) {
              _464_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _464_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _464_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _467_recIdents);
            _463_i = (_463_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _468___mcc_h15 = _source19.dtor_path;
        Dafny.ISequence<Dafny.Rune> _469___mcc_h16 = _source19.dtor_variant;
        bool _470___mcc_h17 = _source19.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _471___mcc_h18 = _source19.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _472_values = _471___mcc_h18;
        bool _473_isCo = _470___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _474_variant = _469___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _475_path = _468___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _476_path;
          Dafny.ISequence<Dafny.Rune> _out140;
          _out140 = DCOMP.COMP.GenPath(_475_path);
          _476_path = _out140;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _476_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _474_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _477_i;
          _477_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_477_i) < (new BigInteger((_472_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_472_values).Select(_477_i);
            Dafny.ISequence<Dafny.Rune> _478_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _479_value = _let_tmp_rhs0.dtor__1;
            if ((_477_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_473_isCo) {
              Dafny.ISequence<Dafny.Rune> _480_recursiveGen;
              bool _481___v32;
              bool _482_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _483_recIdents;
              Dafny.ISequence<Dafny.Rune> _out141;
              bool _out142;
              bool _out143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
              DCOMP.COMP.GenExpr(_479_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out141, out _out142, out _out143, out _out144);
              _480_recursiveGen = _out141;
              _481___v32 = _out142;
              _482_isErased = _out143;
              _483_recIdents = _out144;
              if (!(_482_isErased)) {
                _480_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _480_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _480_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _480_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _483_recIdents);
              Dafny.ISequence<Dafny.Rune> _484_allReadCloned;
              _484_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_483_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _485_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_483_recIdents).Elements) {
                  _485_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_483_recIdents).Contains(_485_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1140)");
              after__ASSIGN_SUCH_THAT_0:;
                _484_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_484_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _485_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _485_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _483_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_483_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_485_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _478_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _484_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _480_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _486_recursiveGen;
              bool _487___v33;
              bool _488_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _489_recIdents;
              Dafny.ISequence<Dafny.Rune> _out145;
              bool _out146;
              bool _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              DCOMP.COMP.GenExpr(_479_value, selfIdent, @params, true, out _out145, out _out146, out _out147, out _out148);
              _486_recursiveGen = _out145;
              _487___v33 = _out146;
              _488_isErased = _out147;
              _489_recIdents = _out148;
              if (!(_488_isErased)) {
                _486_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _486_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _486_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _486_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _478_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _486_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _489_recIdents);
            }
            _477_i = (_477_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_Convert) {
        DAST._IExpression _490___mcc_h19 = _source19.dtor_value;
        DAST._IType _491___mcc_h20 = _source19.dtor_from;
        DAST._IType _492___mcc_h21 = _source19.dtor_typ;
        DAST._IType _493_toTpe = _492___mcc_h21;
        DAST._IType _494_fromTpe = _491___mcc_h20;
        DAST._IExpression _495_expr = _490___mcc_h19;
        {
          if (object.Equals(_494_fromTpe, _493_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _496_recursiveGen;
            bool _497_recOwned;
            bool _498_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _499_recIdents;
            Dafny.ISequence<Dafny.Rune> _out149;
            bool _out150;
            bool _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out149, out _out150, out _out151, out _out152);
            _496_recursiveGen = _out149;
            _497_recOwned = _out150;
            _498_recErased = _out151;
            _499_recIdents = _out152;
            s = _496_recursiveGen;
            isOwned = _497_recOwned;
            isErased = _498_recErased;
            readIdents = _499_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source25 = _System.Tuple2<DAST._IType, DAST._IType>.create(_494_fromTpe, _493_toTpe);
            DAST._IType _500___mcc_h237 = _source25.dtor__0;
            DAST._IType _501___mcc_h238 = _source25.dtor__1;
            DAST._IType _source26 = _500___mcc_h237;
            if (_source26.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _502___mcc_h241 = _source26.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _503___mcc_h242 = _source26.dtor_typeArgs;
              DAST._IResolvedType _504___mcc_h243 = _source26.dtor_resolved;
              DAST._IResolvedType _source27 = _504___mcc_h243;
              if (_source27.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _505___mcc_h253 = _source27.dtor_path;
                DAST._IType _source28 = _501___mcc_h238;
                if (_source28.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _506___mcc_h257 = _source28.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _507___mcc_h258 = _source28.dtor_typeArgs;
                  DAST._IResolvedType _508___mcc_h259 = _source28.dtor_resolved;
                  DAST._IResolvedType _source29 = _508___mcc_h259;
                  if (_source29.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _509___mcc_h263 = _source29.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _510_recursiveGen;
                      bool _511_recOwned;
                      bool _512_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _513_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out153;
                      bool _out154;
                      bool _out155;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out153, out _out154, out _out155, out _out156);
                      _510_recursiveGen = _out153;
                      _511_recOwned = _out154;
                      _512_recErased = _out155;
                      _513_recIdents = _out156;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _510_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _511_recOwned;
                      isErased = _512_recErased;
                      readIdents = _513_recIdents;
                    }
                  } else if (_source29.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _514___mcc_h265 = _source29.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _515_recursiveGen;
                      bool _516_recOwned;
                      bool _517_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _518_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out157;
                      bool _out158;
                      bool _out159;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out157, out _out158, out _out159, out _out160);
                      _515_recursiveGen = _out157;
                      _516_recOwned = _out158;
                      _517_recErased = _out159;
                      _518_recIdents = _out160;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _515_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _516_recOwned;
                      isErased = _517_recErased;
                      readIdents = _518_recIdents;
                    }
                  } else {
                    DAST._IType _519___mcc_h267 = _source29.dtor_Newtype_a0;
                    DAST._IType _520_b = _519___mcc_h267;
                    {
                      if (object.Equals(_494_fromTpe, _520_b)) {
                        Dafny.ISequence<Dafny.Rune> _521_recursiveGen;
                        bool _522_recOwned;
                        bool _523_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _524_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out161;
                        bool _out162;
                        bool _out163;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out161, out _out162, out _out163, out _out164);
                        _521_recursiveGen = _out161;
                        _522_recOwned = _out162;
                        _523_recErased = _out163;
                        _524_recIdents = _out164;
                        Dafny.ISequence<Dafny.Rune> _525_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out165;
                        _out165 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _525_rhsType = _out165;
                        Dafny.ISequence<Dafny.Rune> _526_uneraseFn;
                        _526_uneraseFn = ((_522_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _525_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _526_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _521_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _522_recOwned;
                        isErased = false;
                        readIdents = _524_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out166;
                        bool _out167;
                        bool _out168;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _520_b), _520_b, _493_toTpe), selfIdent, @params, mustOwn, out _out166, out _out167, out _out168, out _out169);
                        s = _out166;
                        isOwned = _out167;
                        isErased = _out168;
                        readIdents = _out169;
                      }
                    }
                  }
                } else if (_source28.is_Nullable) {
                  DAST._IType _527___mcc_h269 = _source28.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _528_recursiveGen;
                    bool _529_recOwned;
                    bool _530_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _531_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out170;
                    bool _out171;
                    bool _out172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out170, out _out171, out _out172, out _out173);
                    _528_recursiveGen = _out170;
                    _529_recOwned = _out171;
                    _530_recErased = _out172;
                    _531_recIdents = _out173;
                    if (!(_529_recOwned)) {
                      _528_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_528_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _528_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _530_recErased;
                    readIdents = _531_recIdents;
                  }
                } else if (_source28.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _532___mcc_h271 = _source28.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _533_recursiveGen;
                    bool _534_recOwned;
                    bool _535_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _536_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out174;
                    bool _out175;
                    bool _out176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out174, out _out175, out _out176, out _out177);
                    _533_recursiveGen = _out174;
                    _534_recOwned = _out175;
                    _535_recErased = _out176;
                    _536_recIdents = _out177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _533_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _534_recOwned;
                    isErased = _535_recErased;
                    readIdents = _536_recIdents;
                  }
                } else if (_source28.is_Array) {
                  DAST._IType _537___mcc_h273 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _538_recursiveGen;
                    bool _539_recOwned;
                    bool _540_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _541_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out178;
                    bool _out179;
                    bool _out180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out178, out _out179, out _out180, out _out181);
                    _538_recursiveGen = _out178;
                    _539_recOwned = _out179;
                    _540_recErased = _out180;
                    _541_recIdents = _out181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _538_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _539_recOwned;
                    isErased = _540_recErased;
                    readIdents = _541_recIdents;
                  }
                } else if (_source28.is_Seq) {
                  DAST._IType _542___mcc_h275 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _543_recursiveGen;
                    bool _544_recOwned;
                    bool _545_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _546_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out182;
                    bool _out183;
                    bool _out184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out182, out _out183, out _out184, out _out185);
                    _543_recursiveGen = _out182;
                    _544_recOwned = _out183;
                    _545_recErased = _out184;
                    _546_recIdents = _out185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _543_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _544_recOwned;
                    isErased = _545_recErased;
                    readIdents = _546_recIdents;
                  }
                } else if (_source28.is_Set) {
                  DAST._IType _547___mcc_h277 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _548_recursiveGen;
                    bool _549_recOwned;
                    bool _550_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _551_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out186;
                    bool _out187;
                    bool _out188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out186, out _out187, out _out188, out _out189);
                    _548_recursiveGen = _out186;
                    _549_recOwned = _out187;
                    _550_recErased = _out188;
                    _551_recIdents = _out189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _548_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _549_recOwned;
                    isErased = _550_recErased;
                    readIdents = _551_recIdents;
                  }
                } else if (_source28.is_Multiset) {
                  DAST._IType _552___mcc_h279 = _source28.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _553_recursiveGen;
                    bool _554_recOwned;
                    bool _555_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _556_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out190;
                    bool _out191;
                    bool _out192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out190, out _out191, out _out192, out _out193);
                    _553_recursiveGen = _out190;
                    _554_recOwned = _out191;
                    _555_recErased = _out192;
                    _556_recIdents = _out193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _553_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _554_recOwned;
                    isErased = _555_recErased;
                    readIdents = _556_recIdents;
                  }
                } else if (_source28.is_Map) {
                  DAST._IType _557___mcc_h281 = _source28.dtor_key;
                  DAST._IType _558___mcc_h282 = _source28.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _559_recursiveGen;
                    bool _560_recOwned;
                    bool _561_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _562_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out194;
                    bool _out195;
                    bool _out196;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out194, out _out195, out _out196, out _out197);
                    _559_recursiveGen = _out194;
                    _560_recOwned = _out195;
                    _561_recErased = _out196;
                    _562_recIdents = _out197;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _559_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _560_recOwned;
                    isErased = _561_recErased;
                    readIdents = _562_recIdents;
                  }
                } else if (_source28.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _563___mcc_h285 = _source28.dtor_args;
                  DAST._IType _564___mcc_h286 = _source28.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _565_recursiveGen;
                    bool _566_recOwned;
                    bool _567_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _568_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out198;
                    bool _out199;
                    bool _out200;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out198, out _out199, out _out200, out _out201);
                    _565_recursiveGen = _out198;
                    _566_recOwned = _out199;
                    _567_recErased = _out200;
                    _568_recIdents = _out201;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _565_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _566_recOwned;
                    isErased = _567_recErased;
                    readIdents = _568_recIdents;
                  }
                } else if (_source28.is_Primitive) {
                  DAST._IPrimitive _569___mcc_h289 = _source28.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _570_recursiveGen;
                    bool _571_recOwned;
                    bool _572_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _573_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out202;
                    bool _out203;
                    bool _out204;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out205;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out202, out _out203, out _out204, out _out205);
                    _570_recursiveGen = _out202;
                    _571_recOwned = _out203;
                    _572_recErased = _out204;
                    _573_recIdents = _out205;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _570_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _571_recOwned;
                    isErased = _572_recErased;
                    readIdents = _573_recIdents;
                  }
                } else if (_source28.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _574___mcc_h291 = _source28.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _575_recursiveGen;
                    bool _576_recOwned;
                    bool _577_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _578_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out206;
                    bool _out207;
                    bool _out208;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out206, out _out207, out _out208, out _out209);
                    _575_recursiveGen = _out206;
                    _576_recOwned = _out207;
                    _577_recErased = _out208;
                    _578_recIdents = _out209;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _575_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _576_recOwned;
                    isErased = _577_recErased;
                    readIdents = _578_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _579___mcc_h293 = _source28.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _580_recursiveGen;
                    bool _581_recOwned;
                    bool _582_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _583_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out210;
                    bool _out211;
                    bool _out212;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out210, out _out211, out _out212, out _out213);
                    _580_recursiveGen = _out210;
                    _581_recOwned = _out211;
                    _582_recErased = _out212;
                    _583_recIdents = _out213;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _580_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _581_recOwned;
                    isErased = _582_recErased;
                    readIdents = _583_recIdents;
                  }
                }
              } else if (_source27.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _584___mcc_h295 = _source27.dtor_path;
                DAST._IType _source30 = _501___mcc_h238;
                if (_source30.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _585___mcc_h299 = _source30.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _586___mcc_h300 = _source30.dtor_typeArgs;
                  DAST._IResolvedType _587___mcc_h301 = _source30.dtor_resolved;
                  DAST._IResolvedType _source31 = _587___mcc_h301;
                  if (_source31.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _588___mcc_h305 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _589_recursiveGen;
                      bool _590_recOwned;
                      bool _591_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _592_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out214;
                      bool _out215;
                      bool _out216;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out214, out _out215, out _out216, out _out217);
                      _589_recursiveGen = _out214;
                      _590_recOwned = _out215;
                      _591_recErased = _out216;
                      _592_recIdents = _out217;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _589_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _590_recOwned;
                      isErased = _591_recErased;
                      readIdents = _592_recIdents;
                    }
                  } else if (_source31.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _593___mcc_h307 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _594_recursiveGen;
                      bool _595_recOwned;
                      bool _596_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _597_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out218;
                      bool _out219;
                      bool _out220;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out221;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out218, out _out219, out _out220, out _out221);
                      _594_recursiveGen = _out218;
                      _595_recOwned = _out219;
                      _596_recErased = _out220;
                      _597_recIdents = _out221;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _594_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _595_recOwned;
                      isErased = _596_recErased;
                      readIdents = _597_recIdents;
                    }
                  } else {
                    DAST._IType _598___mcc_h309 = _source31.dtor_Newtype_a0;
                    DAST._IType _599_b = _598___mcc_h309;
                    {
                      if (object.Equals(_494_fromTpe, _599_b)) {
                        Dafny.ISequence<Dafny.Rune> _600_recursiveGen;
                        bool _601_recOwned;
                        bool _602_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _603_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out222;
                        bool _out223;
                        bool _out224;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out222, out _out223, out _out224, out _out225);
                        _600_recursiveGen = _out222;
                        _601_recOwned = _out223;
                        _602_recErased = _out224;
                        _603_recIdents = _out225;
                        Dafny.ISequence<Dafny.Rune> _604_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out226;
                        _out226 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _604_rhsType = _out226;
                        Dafny.ISequence<Dafny.Rune> _605_uneraseFn;
                        _605_uneraseFn = ((_601_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _604_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _605_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _600_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _601_recOwned;
                        isErased = false;
                        readIdents = _603_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out227;
                        bool _out228;
                        bool _out229;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _599_b), _599_b, _493_toTpe), selfIdent, @params, mustOwn, out _out227, out _out228, out _out229, out _out230);
                        s = _out227;
                        isOwned = _out228;
                        isErased = _out229;
                        readIdents = _out230;
                      }
                    }
                  }
                } else if (_source30.is_Nullable) {
                  DAST._IType _606___mcc_h311 = _source30.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _607_recursiveGen;
                    bool _608_recOwned;
                    bool _609_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _610_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out231;
                    bool _out232;
                    bool _out233;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out231, out _out232, out _out233, out _out234);
                    _607_recursiveGen = _out231;
                    _608_recOwned = _out232;
                    _609_recErased = _out233;
                    _610_recIdents = _out234;
                    if (!(_608_recOwned)) {
                      _607_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_607_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _607_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _609_recErased;
                    readIdents = _610_recIdents;
                  }
                } else if (_source30.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _611___mcc_h313 = _source30.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _612_recursiveGen;
                    bool _613_recOwned;
                    bool _614_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _615_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out235;
                    bool _out236;
                    bool _out237;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out235, out _out236, out _out237, out _out238);
                    _612_recursiveGen = _out235;
                    _613_recOwned = _out236;
                    _614_recErased = _out237;
                    _615_recIdents = _out238;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _612_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _613_recOwned;
                    isErased = _614_recErased;
                    readIdents = _615_recIdents;
                  }
                } else if (_source30.is_Array) {
                  DAST._IType _616___mcc_h315 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _617_recursiveGen;
                    bool _618_recOwned;
                    bool _619_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _620_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out239;
                    bool _out240;
                    bool _out241;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out242;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out239, out _out240, out _out241, out _out242);
                    _617_recursiveGen = _out239;
                    _618_recOwned = _out240;
                    _619_recErased = _out241;
                    _620_recIdents = _out242;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _617_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _618_recOwned;
                    isErased = _619_recErased;
                    readIdents = _620_recIdents;
                  }
                } else if (_source30.is_Seq) {
                  DAST._IType _621___mcc_h317 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _622_recursiveGen;
                    bool _623_recOwned;
                    bool _624_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _625_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out243;
                    bool _out244;
                    bool _out245;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out243, out _out244, out _out245, out _out246);
                    _622_recursiveGen = _out243;
                    _623_recOwned = _out244;
                    _624_recErased = _out245;
                    _625_recIdents = _out246;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _622_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _623_recOwned;
                    isErased = _624_recErased;
                    readIdents = _625_recIdents;
                  }
                } else if (_source30.is_Set) {
                  DAST._IType _626___mcc_h319 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _627_recursiveGen;
                    bool _628_recOwned;
                    bool _629_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _630_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out247;
                    bool _out248;
                    bool _out249;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out247, out _out248, out _out249, out _out250);
                    _627_recursiveGen = _out247;
                    _628_recOwned = _out248;
                    _629_recErased = _out249;
                    _630_recIdents = _out250;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _627_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _628_recOwned;
                    isErased = _629_recErased;
                    readIdents = _630_recIdents;
                  }
                } else if (_source30.is_Multiset) {
                  DAST._IType _631___mcc_h321 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _632_recursiveGen;
                    bool _633_recOwned;
                    bool _634_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _635_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out251;
                    bool _out252;
                    bool _out253;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out251, out _out252, out _out253, out _out254);
                    _632_recursiveGen = _out251;
                    _633_recOwned = _out252;
                    _634_recErased = _out253;
                    _635_recIdents = _out254;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _632_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _633_recOwned;
                    isErased = _634_recErased;
                    readIdents = _635_recIdents;
                  }
                } else if (_source30.is_Map) {
                  DAST._IType _636___mcc_h323 = _source30.dtor_key;
                  DAST._IType _637___mcc_h324 = _source30.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _638_recursiveGen;
                    bool _639_recOwned;
                    bool _640_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _641_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out255;
                    bool _out256;
                    bool _out257;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out255, out _out256, out _out257, out _out258);
                    _638_recursiveGen = _out255;
                    _639_recOwned = _out256;
                    _640_recErased = _out257;
                    _641_recIdents = _out258;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _638_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _639_recOwned;
                    isErased = _640_recErased;
                    readIdents = _641_recIdents;
                  }
                } else if (_source30.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _642___mcc_h327 = _source30.dtor_args;
                  DAST._IType _643___mcc_h328 = _source30.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _644_recursiveGen;
                    bool _645_recOwned;
                    bool _646_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _647_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out259;
                    bool _out260;
                    bool _out261;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out259, out _out260, out _out261, out _out262);
                    _644_recursiveGen = _out259;
                    _645_recOwned = _out260;
                    _646_recErased = _out261;
                    _647_recIdents = _out262;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _644_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _645_recOwned;
                    isErased = _646_recErased;
                    readIdents = _647_recIdents;
                  }
                } else if (_source30.is_Primitive) {
                  DAST._IPrimitive _648___mcc_h331 = _source30.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _649_recursiveGen;
                    bool _650_recOwned;
                    bool _651_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _652_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out263;
                    bool _out264;
                    bool _out265;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out263, out _out264, out _out265, out _out266);
                    _649_recursiveGen = _out263;
                    _650_recOwned = _out264;
                    _651_recErased = _out265;
                    _652_recIdents = _out266;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _649_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _650_recOwned;
                    isErased = _651_recErased;
                    readIdents = _652_recIdents;
                  }
                } else if (_source30.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _653___mcc_h333 = _source30.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _654_recursiveGen;
                    bool _655_recOwned;
                    bool _656_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _657_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out267;
                    bool _out268;
                    bool _out269;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out267, out _out268, out _out269, out _out270);
                    _654_recursiveGen = _out267;
                    _655_recOwned = _out268;
                    _656_recErased = _out269;
                    _657_recIdents = _out270;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _654_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _655_recOwned;
                    isErased = _656_recErased;
                    readIdents = _657_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _658___mcc_h335 = _source30.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _659_recursiveGen;
                    bool _660_recOwned;
                    bool _661_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _662_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out271;
                    bool _out272;
                    bool _out273;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out271, out _out272, out _out273, out _out274);
                    _659_recursiveGen = _out271;
                    _660_recOwned = _out272;
                    _661_recErased = _out273;
                    _662_recIdents = _out274;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _659_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _660_recOwned;
                    isErased = _661_recErased;
                    readIdents = _662_recIdents;
                  }
                }
              } else {
                DAST._IType _663___mcc_h337 = _source27.dtor_Newtype_a0;
                DAST._IType _source32 = _501___mcc_h238;
                if (_source32.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _664___mcc_h341 = _source32.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _665___mcc_h342 = _source32.dtor_typeArgs;
                  DAST._IResolvedType _666___mcc_h343 = _source32.dtor_resolved;
                  DAST._IResolvedType _source33 = _666___mcc_h343;
                  if (_source33.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _667___mcc_h350 = _source33.dtor_path;
                    DAST._IType _668_b = _663___mcc_h337;
                    {
                      if (object.Equals(_668_b, _493_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _669_recursiveGen;
                        bool _670_recOwned;
                        bool _671_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _672_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out275;
                        bool _out276;
                        bool _out277;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out275, out _out276, out _out277, out _out278);
                        _669_recursiveGen = _out275;
                        _670_recOwned = _out276;
                        _671_recErased = _out277;
                        _672_recIdents = _out278;
                        Dafny.ISequence<Dafny.Rune> _673_uneraseFn;
                        _673_uneraseFn = ((_670_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _673_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _669_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _670_recOwned;
                        isErased = true;
                        readIdents = _672_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out279;
                        bool _out280;
                        bool _out281;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _668_b), _668_b, _493_toTpe), selfIdent, @params, mustOwn, out _out279, out _out280, out _out281, out _out282);
                        s = _out279;
                        isOwned = _out280;
                        isErased = _out281;
                        readIdents = _out282;
                      }
                    }
                  } else if (_source33.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _674___mcc_h353 = _source33.dtor_path;
                    DAST._IType _675_b = _663___mcc_h337;
                    {
                      if (object.Equals(_675_b, _493_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _676_recursiveGen;
                        bool _677_recOwned;
                        bool _678_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _679_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out283;
                        bool _out284;
                        bool _out285;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out283, out _out284, out _out285, out _out286);
                        _676_recursiveGen = _out283;
                        _677_recOwned = _out284;
                        _678_recErased = _out285;
                        _679_recIdents = _out286;
                        Dafny.ISequence<Dafny.Rune> _680_uneraseFn;
                        _680_uneraseFn = ((_677_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _680_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _676_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _677_recOwned;
                        isErased = true;
                        readIdents = _679_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out287;
                        bool _out288;
                        bool _out289;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _675_b), _675_b, _493_toTpe), selfIdent, @params, mustOwn, out _out287, out _out288, out _out289, out _out290);
                        s = _out287;
                        isOwned = _out288;
                        isErased = _out289;
                        readIdents = _out290;
                      }
                    }
                  } else {
                    DAST._IType _681___mcc_h356 = _source33.dtor_Newtype_a0;
                    DAST._IType _682_b = _681___mcc_h356;
                    {
                      if (object.Equals(_494_fromTpe, _682_b)) {
                        Dafny.ISequence<Dafny.Rune> _683_recursiveGen;
                        bool _684_recOwned;
                        bool _685_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _686_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out291;
                        bool _out292;
                        bool _out293;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out291, out _out292, out _out293, out _out294);
                        _683_recursiveGen = _out291;
                        _684_recOwned = _out292;
                        _685_recErased = _out293;
                        _686_recIdents = _out294;
                        Dafny.ISequence<Dafny.Rune> _687_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out295;
                        _out295 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _687_rhsType = _out295;
                        Dafny.ISequence<Dafny.Rune> _688_uneraseFn;
                        _688_uneraseFn = ((_684_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _687_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _688_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _683_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _684_recOwned;
                        isErased = false;
                        readIdents = _686_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out296;
                        bool _out297;
                        bool _out298;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _682_b), _682_b, _493_toTpe), selfIdent, @params, mustOwn, out _out296, out _out297, out _out298, out _out299);
                        s = _out296;
                        isOwned = _out297;
                        isErased = _out298;
                        readIdents = _out299;
                      }
                    }
                  }
                } else if (_source32.is_Nullable) {
                  DAST._IType _689___mcc_h359 = _source32.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _690_recursiveGen;
                    bool _691_recOwned;
                    bool _692_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _693_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out300;
                    bool _out301;
                    bool _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out300, out _out301, out _out302, out _out303);
                    _690_recursiveGen = _out300;
                    _691_recOwned = _out301;
                    _692_recErased = _out302;
                    _693_recIdents = _out303;
                    if (!(_691_recOwned)) {
                      _690_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_690_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _690_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _692_recErased;
                    readIdents = _693_recIdents;
                  }
                } else if (_source32.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _694___mcc_h362 = _source32.dtor_Tuple_a0;
                  DAST._IType _695_b = _663___mcc_h337;
                  {
                    if (object.Equals(_695_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _696_recursiveGen;
                      bool _697_recOwned;
                      bool _698_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _699_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out304;
                      bool _out305;
                      bool _out306;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out304, out _out305, out _out306, out _out307);
                      _696_recursiveGen = _out304;
                      _697_recOwned = _out305;
                      _698_recErased = _out306;
                      _699_recIdents = _out307;
                      Dafny.ISequence<Dafny.Rune> _700_uneraseFn;
                      _700_uneraseFn = ((_697_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _700_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _696_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _697_recOwned;
                      isErased = true;
                      readIdents = _699_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out308;
                      bool _out309;
                      bool _out310;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _695_b), _695_b, _493_toTpe), selfIdent, @params, mustOwn, out _out308, out _out309, out _out310, out _out311);
                      s = _out308;
                      isOwned = _out309;
                      isErased = _out310;
                      readIdents = _out311;
                    }
                  }
                } else if (_source32.is_Array) {
                  DAST._IType _701___mcc_h365 = _source32.dtor_element;
                  DAST._IType _702_b = _663___mcc_h337;
                  {
                    if (object.Equals(_702_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _703_recursiveGen;
                      bool _704_recOwned;
                      bool _705_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _706_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out312;
                      bool _out313;
                      bool _out314;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out312, out _out313, out _out314, out _out315);
                      _703_recursiveGen = _out312;
                      _704_recOwned = _out313;
                      _705_recErased = _out314;
                      _706_recIdents = _out315;
                      Dafny.ISequence<Dafny.Rune> _707_uneraseFn;
                      _707_uneraseFn = ((_704_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _707_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _703_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _704_recOwned;
                      isErased = true;
                      readIdents = _706_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out316;
                      bool _out317;
                      bool _out318;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _702_b), _702_b, _493_toTpe), selfIdent, @params, mustOwn, out _out316, out _out317, out _out318, out _out319);
                      s = _out316;
                      isOwned = _out317;
                      isErased = _out318;
                      readIdents = _out319;
                    }
                  }
                } else if (_source32.is_Seq) {
                  DAST._IType _708___mcc_h368 = _source32.dtor_element;
                  DAST._IType _709_b = _663___mcc_h337;
                  {
                    if (object.Equals(_709_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _710_recursiveGen;
                      bool _711_recOwned;
                      bool _712_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _713_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out320;
                      bool _out321;
                      bool _out322;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out320, out _out321, out _out322, out _out323);
                      _710_recursiveGen = _out320;
                      _711_recOwned = _out321;
                      _712_recErased = _out322;
                      _713_recIdents = _out323;
                      Dafny.ISequence<Dafny.Rune> _714_uneraseFn;
                      _714_uneraseFn = ((_711_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _714_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _710_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _711_recOwned;
                      isErased = true;
                      readIdents = _713_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out324;
                      bool _out325;
                      bool _out326;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _709_b), _709_b, _493_toTpe), selfIdent, @params, mustOwn, out _out324, out _out325, out _out326, out _out327);
                      s = _out324;
                      isOwned = _out325;
                      isErased = _out326;
                      readIdents = _out327;
                    }
                  }
                } else if (_source32.is_Set) {
                  DAST._IType _715___mcc_h371 = _source32.dtor_element;
                  DAST._IType _716_b = _663___mcc_h337;
                  {
                    if (object.Equals(_716_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _717_recursiveGen;
                      bool _718_recOwned;
                      bool _719_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _720_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out328;
                      bool _out329;
                      bool _out330;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out328, out _out329, out _out330, out _out331);
                      _717_recursiveGen = _out328;
                      _718_recOwned = _out329;
                      _719_recErased = _out330;
                      _720_recIdents = _out331;
                      Dafny.ISequence<Dafny.Rune> _721_uneraseFn;
                      _721_uneraseFn = ((_718_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _721_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _717_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _718_recOwned;
                      isErased = true;
                      readIdents = _720_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out332;
                      bool _out333;
                      bool _out334;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _716_b), _716_b, _493_toTpe), selfIdent, @params, mustOwn, out _out332, out _out333, out _out334, out _out335);
                      s = _out332;
                      isOwned = _out333;
                      isErased = _out334;
                      readIdents = _out335;
                    }
                  }
                } else if (_source32.is_Multiset) {
                  DAST._IType _722___mcc_h374 = _source32.dtor_element;
                  DAST._IType _723_b = _663___mcc_h337;
                  {
                    if (object.Equals(_723_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _724_recursiveGen;
                      bool _725_recOwned;
                      bool _726_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _727_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out336;
                      bool _out337;
                      bool _out338;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out336, out _out337, out _out338, out _out339);
                      _724_recursiveGen = _out336;
                      _725_recOwned = _out337;
                      _726_recErased = _out338;
                      _727_recIdents = _out339;
                      Dafny.ISequence<Dafny.Rune> _728_uneraseFn;
                      _728_uneraseFn = ((_725_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _728_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _724_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _725_recOwned;
                      isErased = true;
                      readIdents = _727_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out340;
                      bool _out341;
                      bool _out342;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _723_b), _723_b, _493_toTpe), selfIdent, @params, mustOwn, out _out340, out _out341, out _out342, out _out343);
                      s = _out340;
                      isOwned = _out341;
                      isErased = _out342;
                      readIdents = _out343;
                    }
                  }
                } else if (_source32.is_Map) {
                  DAST._IType _729___mcc_h377 = _source32.dtor_key;
                  DAST._IType _730___mcc_h378 = _source32.dtor_value;
                  DAST._IType _731_b = _663___mcc_h337;
                  {
                    if (object.Equals(_731_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _732_recursiveGen;
                      bool _733_recOwned;
                      bool _734_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _735_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out344;
                      bool _out345;
                      bool _out346;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out347;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out344, out _out345, out _out346, out _out347);
                      _732_recursiveGen = _out344;
                      _733_recOwned = _out345;
                      _734_recErased = _out346;
                      _735_recIdents = _out347;
                      Dafny.ISequence<Dafny.Rune> _736_uneraseFn;
                      _736_uneraseFn = ((_733_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _736_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _732_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _733_recOwned;
                      isErased = true;
                      readIdents = _735_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out348;
                      bool _out349;
                      bool _out350;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _731_b), _731_b, _493_toTpe), selfIdent, @params, mustOwn, out _out348, out _out349, out _out350, out _out351);
                      s = _out348;
                      isOwned = _out349;
                      isErased = _out350;
                      readIdents = _out351;
                    }
                  }
                } else if (_source32.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _737___mcc_h383 = _source32.dtor_args;
                  DAST._IType _738___mcc_h384 = _source32.dtor_result;
                  DAST._IType _739_b = _663___mcc_h337;
                  {
                    if (object.Equals(_739_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _740_recursiveGen;
                      bool _741_recOwned;
                      bool _742_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _743_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out352;
                      bool _out353;
                      bool _out354;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out352, out _out353, out _out354, out _out355);
                      _740_recursiveGen = _out352;
                      _741_recOwned = _out353;
                      _742_recErased = _out354;
                      _743_recIdents = _out355;
                      Dafny.ISequence<Dafny.Rune> _744_uneraseFn;
                      _744_uneraseFn = ((_741_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _744_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _740_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _741_recOwned;
                      isErased = true;
                      readIdents = _743_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out356;
                      bool _out357;
                      bool _out358;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out359;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _739_b), _739_b, _493_toTpe), selfIdent, @params, mustOwn, out _out356, out _out357, out _out358, out _out359);
                      s = _out356;
                      isOwned = _out357;
                      isErased = _out358;
                      readIdents = _out359;
                    }
                  }
                } else if (_source32.is_Primitive) {
                  DAST._IPrimitive _745___mcc_h389 = _source32.dtor_Primitive_a0;
                  DAST._IType _746_b = _663___mcc_h337;
                  {
                    if (object.Equals(_746_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _747_recursiveGen;
                      bool _748_recOwned;
                      bool _749_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _750_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out360;
                      bool _out361;
                      bool _out362;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out360, out _out361, out _out362, out _out363);
                      _747_recursiveGen = _out360;
                      _748_recOwned = _out361;
                      _749_recErased = _out362;
                      _750_recIdents = _out363;
                      Dafny.ISequence<Dafny.Rune> _751_uneraseFn;
                      _751_uneraseFn = ((_748_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _751_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _747_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _748_recOwned;
                      isErased = true;
                      readIdents = _750_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out364;
                      bool _out365;
                      bool _out366;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _746_b), _746_b, _493_toTpe), selfIdent, @params, mustOwn, out _out364, out _out365, out _out366, out _out367);
                      s = _out364;
                      isOwned = _out365;
                      isErased = _out366;
                      readIdents = _out367;
                    }
                  }
                } else if (_source32.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _752___mcc_h392 = _source32.dtor_Passthrough_a0;
                  DAST._IType _753_b = _663___mcc_h337;
                  {
                    if (object.Equals(_753_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _754_recursiveGen;
                      bool _755_recOwned;
                      bool _756_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _757_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out368;
                      bool _out369;
                      bool _out370;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out368, out _out369, out _out370, out _out371);
                      _754_recursiveGen = _out368;
                      _755_recOwned = _out369;
                      _756_recErased = _out370;
                      _757_recIdents = _out371;
                      Dafny.ISequence<Dafny.Rune> _758_uneraseFn;
                      _758_uneraseFn = ((_755_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _758_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _754_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _755_recOwned;
                      isErased = true;
                      readIdents = _757_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out372;
                      bool _out373;
                      bool _out374;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _753_b), _753_b, _493_toTpe), selfIdent, @params, mustOwn, out _out372, out _out373, out _out374, out _out375);
                      s = _out372;
                      isOwned = _out373;
                      isErased = _out374;
                      readIdents = _out375;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _759___mcc_h395 = _source32.dtor_TypeArg_a0;
                  DAST._IType _760_b = _663___mcc_h337;
                  {
                    if (object.Equals(_760_b, _493_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _761_recursiveGen;
                      bool _762_recOwned;
                      bool _763_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _764_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out376;
                      bool _out377;
                      bool _out378;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out376, out _out377, out _out378, out _out379);
                      _761_recursiveGen = _out376;
                      _762_recOwned = _out377;
                      _763_recErased = _out378;
                      _764_recIdents = _out379;
                      Dafny.ISequence<Dafny.Rune> _765_uneraseFn;
                      _765_uneraseFn = ((_762_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _765_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _761_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _762_recOwned;
                      isErased = true;
                      readIdents = _764_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out380;
                      bool _out381;
                      bool _out382;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _760_b), _760_b, _493_toTpe), selfIdent, @params, mustOwn, out _out380, out _out381, out _out382, out _out383);
                      s = _out380;
                      isOwned = _out381;
                      isErased = _out382;
                      readIdents = _out383;
                    }
                  }
                }
              }
            } else if (_source26.is_Nullable) {
              DAST._IType _766___mcc_h398 = _source26.dtor_Nullable_a0;
              DAST._IType _source34 = _501___mcc_h238;
              if (_source34.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _767___mcc_h402 = _source34.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _768___mcc_h403 = _source34.dtor_typeArgs;
                DAST._IResolvedType _769___mcc_h404 = _source34.dtor_resolved;
                DAST._IResolvedType _source35 = _769___mcc_h404;
                if (_source35.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _770___mcc_h411 = _source35.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _771_recursiveGen;
                    bool _772_recOwned;
                    bool _773_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _774_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out384;
                    bool _out385;
                    bool _out386;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out384, out _out385, out _out386, out _out387);
                    _771_recursiveGen = _out384;
                    _772_recOwned = _out385;
                    _773_recErased = _out386;
                    _774_recIdents = _out387;
                    if (!(_772_recOwned)) {
                      _771_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_771_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_771_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _772_recOwned;
                    isErased = _773_recErased;
                    readIdents = _774_recIdents;
                  }
                } else if (_source35.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _775___mcc_h414 = _source35.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _776_recursiveGen;
                    bool _777_recOwned;
                    bool _778_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _779_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out388;
                    bool _out389;
                    bool _out390;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out388, out _out389, out _out390, out _out391);
                    _776_recursiveGen = _out388;
                    _777_recOwned = _out389;
                    _778_recErased = _out390;
                    _779_recIdents = _out391;
                    if (!(_777_recOwned)) {
                      _776_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_776_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_776_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _777_recOwned;
                    isErased = _778_recErased;
                    readIdents = _779_recIdents;
                  }
                } else {
                  DAST._IType _780___mcc_h417 = _source35.dtor_Newtype_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _781_recursiveGen;
                    bool _782_recOwned;
                    bool _783_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _784_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out392;
                    bool _out393;
                    bool _out394;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out392, out _out393, out _out394, out _out395);
                    _781_recursiveGen = _out392;
                    _782_recOwned = _out393;
                    _783_recErased = _out394;
                    _784_recIdents = _out395;
                    if (!(_782_recOwned)) {
                      _781_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_781_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_781_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _782_recOwned;
                    isErased = _783_recErased;
                    readIdents = _784_recIdents;
                  }
                }
              } else if (_source34.is_Nullable) {
                DAST._IType _785___mcc_h420 = _source34.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _786_recursiveGen;
                  bool _787_recOwned;
                  bool _788_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _789_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out396;
                  bool _out397;
                  bool _out398;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out396, out _out397, out _out398, out _out399);
                  _786_recursiveGen = _out396;
                  _787_recOwned = _out397;
                  _788_recErased = _out398;
                  _789_recIdents = _out399;
                  if (!(_787_recOwned)) {
                    _786_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_786_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_786_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _787_recOwned;
                  isErased = _788_recErased;
                  readIdents = _789_recIdents;
                }
              } else if (_source34.is_Tuple) {
                Dafny.ISequence<DAST._IType> _790___mcc_h423 = _source34.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _791_recursiveGen;
                  bool _792_recOwned;
                  bool _793_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _794_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out400;
                  bool _out401;
                  bool _out402;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out400, out _out401, out _out402, out _out403);
                  _791_recursiveGen = _out400;
                  _792_recOwned = _out401;
                  _793_recErased = _out402;
                  _794_recIdents = _out403;
                  if (!(_792_recOwned)) {
                    _791_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_791_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_791_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _792_recOwned;
                  isErased = _793_recErased;
                  readIdents = _794_recIdents;
                }
              } else if (_source34.is_Array) {
                DAST._IType _795___mcc_h426 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _796_recursiveGen;
                  bool _797_recOwned;
                  bool _798_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _799_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out404;
                  bool _out405;
                  bool _out406;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out404, out _out405, out _out406, out _out407);
                  _796_recursiveGen = _out404;
                  _797_recOwned = _out405;
                  _798_recErased = _out406;
                  _799_recIdents = _out407;
                  if (!(_797_recOwned)) {
                    _796_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_796_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_796_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _797_recOwned;
                  isErased = _798_recErased;
                  readIdents = _799_recIdents;
                }
              } else if (_source34.is_Seq) {
                DAST._IType _800___mcc_h429 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _801_recursiveGen;
                  bool _802_recOwned;
                  bool _803_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _804_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out408;
                  bool _out409;
                  bool _out410;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out408, out _out409, out _out410, out _out411);
                  _801_recursiveGen = _out408;
                  _802_recOwned = _out409;
                  _803_recErased = _out410;
                  _804_recIdents = _out411;
                  if (!(_802_recOwned)) {
                    _801_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_801_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_801_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _802_recOwned;
                  isErased = _803_recErased;
                  readIdents = _804_recIdents;
                }
              } else if (_source34.is_Set) {
                DAST._IType _805___mcc_h432 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _806_recursiveGen;
                  bool _807_recOwned;
                  bool _808_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _809_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out412;
                  bool _out413;
                  bool _out414;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out412, out _out413, out _out414, out _out415);
                  _806_recursiveGen = _out412;
                  _807_recOwned = _out413;
                  _808_recErased = _out414;
                  _809_recIdents = _out415;
                  if (!(_807_recOwned)) {
                    _806_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_806_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_806_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _807_recOwned;
                  isErased = _808_recErased;
                  readIdents = _809_recIdents;
                }
              } else if (_source34.is_Multiset) {
                DAST._IType _810___mcc_h435 = _source34.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _811_recursiveGen;
                  bool _812_recOwned;
                  bool _813_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _814_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out416;
                  bool _out417;
                  bool _out418;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out416, out _out417, out _out418, out _out419);
                  _811_recursiveGen = _out416;
                  _812_recOwned = _out417;
                  _813_recErased = _out418;
                  _814_recIdents = _out419;
                  if (!(_812_recOwned)) {
                    _811_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_811_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_811_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _812_recOwned;
                  isErased = _813_recErased;
                  readIdents = _814_recIdents;
                }
              } else if (_source34.is_Map) {
                DAST._IType _815___mcc_h438 = _source34.dtor_key;
                DAST._IType _816___mcc_h439 = _source34.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _817_recursiveGen;
                  bool _818_recOwned;
                  bool _819_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _820_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out420;
                  bool _out421;
                  bool _out422;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out420, out _out421, out _out422, out _out423);
                  _817_recursiveGen = _out420;
                  _818_recOwned = _out421;
                  _819_recErased = _out422;
                  _820_recIdents = _out423;
                  if (!(_818_recOwned)) {
                    _817_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_817_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_817_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _818_recOwned;
                  isErased = _819_recErased;
                  readIdents = _820_recIdents;
                }
              } else if (_source34.is_Arrow) {
                Dafny.ISequence<DAST._IType> _821___mcc_h444 = _source34.dtor_args;
                DAST._IType _822___mcc_h445 = _source34.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _823_recursiveGen;
                  bool _824_recOwned;
                  bool _825_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _826_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out424;
                  bool _out425;
                  bool _out426;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out424, out _out425, out _out426, out _out427);
                  _823_recursiveGen = _out424;
                  _824_recOwned = _out425;
                  _825_recErased = _out426;
                  _826_recIdents = _out427;
                  if (!(_824_recOwned)) {
                    _823_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_823_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_823_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _824_recOwned;
                  isErased = _825_recErased;
                  readIdents = _826_recIdents;
                }
              } else if (_source34.is_Primitive) {
                DAST._IPrimitive _827___mcc_h450 = _source34.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _828_recursiveGen;
                  bool _829_recOwned;
                  bool _830_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _831_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out428;
                  bool _out429;
                  bool _out430;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out428, out _out429, out _out430, out _out431);
                  _828_recursiveGen = _out428;
                  _829_recOwned = _out429;
                  _830_recErased = _out430;
                  _831_recIdents = _out431;
                  if (!(_829_recOwned)) {
                    _828_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_828_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_828_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _829_recOwned;
                  isErased = _830_recErased;
                  readIdents = _831_recIdents;
                }
              } else if (_source34.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _832___mcc_h453 = _source34.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _833_recursiveGen;
                  bool _834_recOwned;
                  bool _835_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _836_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out432;
                  bool _out433;
                  bool _out434;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out432, out _out433, out _out434, out _out435);
                  _833_recursiveGen = _out432;
                  _834_recOwned = _out433;
                  _835_recErased = _out434;
                  _836_recIdents = _out435;
                  if (!(_834_recOwned)) {
                    _833_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_833_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_833_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _834_recOwned;
                  isErased = _835_recErased;
                  readIdents = _836_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _837___mcc_h456 = _source34.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _838_recursiveGen;
                  bool _839_recOwned;
                  bool _840_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _841_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out436;
                  bool _out437;
                  bool _out438;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out436, out _out437, out _out438, out _out439);
                  _838_recursiveGen = _out436;
                  _839_recOwned = _out437;
                  _840_recErased = _out438;
                  _841_recIdents = _out439;
                  if (!(_839_recOwned)) {
                    _838_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_838_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_838_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _839_recOwned;
                  isErased = _840_recErased;
                  readIdents = _841_recIdents;
                }
              }
            } else if (_source26.is_Tuple) {
              Dafny.ISequence<DAST._IType> _842___mcc_h459 = _source26.dtor_Tuple_a0;
              DAST._IType _source36 = _501___mcc_h238;
              if (_source36.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _843___mcc_h463 = _source36.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _844___mcc_h464 = _source36.dtor_typeArgs;
                DAST._IResolvedType _845___mcc_h465 = _source36.dtor_resolved;
                DAST._IResolvedType _source37 = _845___mcc_h465;
                if (_source37.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _846___mcc_h469 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _847_recursiveGen;
                    bool _848_recOwned;
                    bool _849_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _850_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out440;
                    bool _out441;
                    bool _out442;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out440, out _out441, out _out442, out _out443);
                    _847_recursiveGen = _out440;
                    _848_recOwned = _out441;
                    _849_recErased = _out442;
                    _850_recIdents = _out443;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _847_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _848_recOwned;
                    isErased = _849_recErased;
                    readIdents = _850_recIdents;
                  }
                } else if (_source37.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _851___mcc_h471 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _852_recursiveGen;
                    bool _853_recOwned;
                    bool _854_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _855_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out444;
                    bool _out445;
                    bool _out446;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out444, out _out445, out _out446, out _out447);
                    _852_recursiveGen = _out444;
                    _853_recOwned = _out445;
                    _854_recErased = _out446;
                    _855_recIdents = _out447;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _852_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _853_recOwned;
                    isErased = _854_recErased;
                    readIdents = _855_recIdents;
                  }
                } else {
                  DAST._IType _856___mcc_h473 = _source37.dtor_Newtype_a0;
                  DAST._IType _857_b = _856___mcc_h473;
                  {
                    if (object.Equals(_494_fromTpe, _857_b)) {
                      Dafny.ISequence<Dafny.Rune> _858_recursiveGen;
                      bool _859_recOwned;
                      bool _860_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _861_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out448;
                      bool _out449;
                      bool _out450;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out448, out _out449, out _out450, out _out451);
                      _858_recursiveGen = _out448;
                      _859_recOwned = _out449;
                      _860_recErased = _out450;
                      _861_recIdents = _out451;
                      Dafny.ISequence<Dafny.Rune> _862_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out452;
                      _out452 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _862_rhsType = _out452;
                      Dafny.ISequence<Dafny.Rune> _863_uneraseFn;
                      _863_uneraseFn = ((_859_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _862_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _863_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _858_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _859_recOwned;
                      isErased = false;
                      readIdents = _861_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out453;
                      bool _out454;
                      bool _out455;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _857_b), _857_b, _493_toTpe), selfIdent, @params, mustOwn, out _out453, out _out454, out _out455, out _out456);
                      s = _out453;
                      isOwned = _out454;
                      isErased = _out455;
                      readIdents = _out456;
                    }
                  }
                }
              } else if (_source36.is_Nullable) {
                DAST._IType _864___mcc_h475 = _source36.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _865_recursiveGen;
                  bool _866_recOwned;
                  bool _867_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _868_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out457;
                  bool _out458;
                  bool _out459;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out457, out _out458, out _out459, out _out460);
                  _865_recursiveGen = _out457;
                  _866_recOwned = _out458;
                  _867_recErased = _out459;
                  _868_recIdents = _out460;
                  if (!(_866_recOwned)) {
                    _865_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_865_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _865_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _867_recErased;
                  readIdents = _868_recIdents;
                }
              } else if (_source36.is_Tuple) {
                Dafny.ISequence<DAST._IType> _869___mcc_h477 = _source36.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _870_recursiveGen;
                  bool _871_recOwned;
                  bool _872_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _873_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out461;
                  bool _out462;
                  bool _out463;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out461, out _out462, out _out463, out _out464);
                  _870_recursiveGen = _out461;
                  _871_recOwned = _out462;
                  _872_recErased = _out463;
                  _873_recIdents = _out464;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _870_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _871_recOwned;
                  isErased = _872_recErased;
                  readIdents = _873_recIdents;
                }
              } else if (_source36.is_Array) {
                DAST._IType _874___mcc_h479 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _875_recursiveGen;
                  bool _876_recOwned;
                  bool _877_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _878_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out465;
                  bool _out466;
                  bool _out467;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out465, out _out466, out _out467, out _out468);
                  _875_recursiveGen = _out465;
                  _876_recOwned = _out466;
                  _877_recErased = _out467;
                  _878_recIdents = _out468;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _875_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _876_recOwned;
                  isErased = _877_recErased;
                  readIdents = _878_recIdents;
                }
              } else if (_source36.is_Seq) {
                DAST._IType _879___mcc_h481 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _880_recursiveGen;
                  bool _881_recOwned;
                  bool _882_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _883_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out469;
                  bool _out470;
                  bool _out471;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out469, out _out470, out _out471, out _out472);
                  _880_recursiveGen = _out469;
                  _881_recOwned = _out470;
                  _882_recErased = _out471;
                  _883_recIdents = _out472;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _880_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _881_recOwned;
                  isErased = _882_recErased;
                  readIdents = _883_recIdents;
                }
              } else if (_source36.is_Set) {
                DAST._IType _884___mcc_h483 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _885_recursiveGen;
                  bool _886_recOwned;
                  bool _887_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _888_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out473;
                  bool _out474;
                  bool _out475;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out473, out _out474, out _out475, out _out476);
                  _885_recursiveGen = _out473;
                  _886_recOwned = _out474;
                  _887_recErased = _out475;
                  _888_recIdents = _out476;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _885_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _886_recOwned;
                  isErased = _887_recErased;
                  readIdents = _888_recIdents;
                }
              } else if (_source36.is_Multiset) {
                DAST._IType _889___mcc_h485 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _890_recursiveGen;
                  bool _891_recOwned;
                  bool _892_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _893_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out477;
                  bool _out478;
                  bool _out479;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out477, out _out478, out _out479, out _out480);
                  _890_recursiveGen = _out477;
                  _891_recOwned = _out478;
                  _892_recErased = _out479;
                  _893_recIdents = _out480;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _890_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _891_recOwned;
                  isErased = _892_recErased;
                  readIdents = _893_recIdents;
                }
              } else if (_source36.is_Map) {
                DAST._IType _894___mcc_h487 = _source36.dtor_key;
                DAST._IType _895___mcc_h488 = _source36.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _896_recursiveGen;
                  bool _897_recOwned;
                  bool _898_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _899_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out481;
                  bool _out482;
                  bool _out483;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out481, out _out482, out _out483, out _out484);
                  _896_recursiveGen = _out481;
                  _897_recOwned = _out482;
                  _898_recErased = _out483;
                  _899_recIdents = _out484;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _896_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _897_recOwned;
                  isErased = _898_recErased;
                  readIdents = _899_recIdents;
                }
              } else if (_source36.is_Arrow) {
                Dafny.ISequence<DAST._IType> _900___mcc_h491 = _source36.dtor_args;
                DAST._IType _901___mcc_h492 = _source36.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _902_recursiveGen;
                  bool _903_recOwned;
                  bool _904_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _905_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out485;
                  bool _out486;
                  bool _out487;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out488;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out485, out _out486, out _out487, out _out488);
                  _902_recursiveGen = _out485;
                  _903_recOwned = _out486;
                  _904_recErased = _out487;
                  _905_recIdents = _out488;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _902_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _903_recOwned;
                  isErased = _904_recErased;
                  readIdents = _905_recIdents;
                }
              } else if (_source36.is_Primitive) {
                DAST._IPrimitive _906___mcc_h495 = _source36.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _907_recursiveGen;
                  bool _908_recOwned;
                  bool _909_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _910_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out489;
                  bool _out490;
                  bool _out491;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out489, out _out490, out _out491, out _out492);
                  _907_recursiveGen = _out489;
                  _908_recOwned = _out490;
                  _909_recErased = _out491;
                  _910_recIdents = _out492;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _907_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _908_recOwned;
                  isErased = _909_recErased;
                  readIdents = _910_recIdents;
                }
              } else if (_source36.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _911___mcc_h497 = _source36.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _912_recursiveGen;
                  bool _913_recOwned;
                  bool _914_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _915_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out493;
                  bool _out494;
                  bool _out495;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out493, out _out494, out _out495, out _out496);
                  _912_recursiveGen = _out493;
                  _913_recOwned = _out494;
                  _914_recErased = _out495;
                  _915_recIdents = _out496;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _912_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _913_recOwned;
                  isErased = _914_recErased;
                  readIdents = _915_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _916___mcc_h499 = _source36.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _917_recursiveGen;
                  bool _918_recOwned;
                  bool _919_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _920_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out497;
                  bool _out498;
                  bool _out499;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out497, out _out498, out _out499, out _out500);
                  _917_recursiveGen = _out497;
                  _918_recOwned = _out498;
                  _919_recErased = _out499;
                  _920_recIdents = _out500;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _917_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _918_recOwned;
                  isErased = _919_recErased;
                  readIdents = _920_recIdents;
                }
              }
            } else if (_source26.is_Array) {
              DAST._IType _921___mcc_h501 = _source26.dtor_element;
              DAST._IType _source38 = _501___mcc_h238;
              if (_source38.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _922___mcc_h505 = _source38.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _923___mcc_h506 = _source38.dtor_typeArgs;
                DAST._IResolvedType _924___mcc_h507 = _source38.dtor_resolved;
                DAST._IResolvedType _source39 = _924___mcc_h507;
                if (_source39.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _925___mcc_h511 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _926_recursiveGen;
                    bool _927_recOwned;
                    bool _928_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _929_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out501;
                    bool _out502;
                    bool _out503;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out501, out _out502, out _out503, out _out504);
                    _926_recursiveGen = _out501;
                    _927_recOwned = _out502;
                    _928_recErased = _out503;
                    _929_recIdents = _out504;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _926_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _927_recOwned;
                    isErased = _928_recErased;
                    readIdents = _929_recIdents;
                  }
                } else if (_source39.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _930___mcc_h513 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _931_recursiveGen;
                    bool _932_recOwned;
                    bool _933_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _934_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out505;
                    bool _out506;
                    bool _out507;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out505, out _out506, out _out507, out _out508);
                    _931_recursiveGen = _out505;
                    _932_recOwned = _out506;
                    _933_recErased = _out507;
                    _934_recIdents = _out508;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _931_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _932_recOwned;
                    isErased = _933_recErased;
                    readIdents = _934_recIdents;
                  }
                } else {
                  DAST._IType _935___mcc_h515 = _source39.dtor_Newtype_a0;
                  DAST._IType _936_b = _935___mcc_h515;
                  {
                    if (object.Equals(_494_fromTpe, _936_b)) {
                      Dafny.ISequence<Dafny.Rune> _937_recursiveGen;
                      bool _938_recOwned;
                      bool _939_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _940_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out509;
                      bool _out510;
                      bool _out511;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out509, out _out510, out _out511, out _out512);
                      _937_recursiveGen = _out509;
                      _938_recOwned = _out510;
                      _939_recErased = _out511;
                      _940_recIdents = _out512;
                      Dafny.ISequence<Dafny.Rune> _941_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out513;
                      _out513 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _941_rhsType = _out513;
                      Dafny.ISequence<Dafny.Rune> _942_uneraseFn;
                      _942_uneraseFn = ((_938_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _941_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _942_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _937_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _938_recOwned;
                      isErased = false;
                      readIdents = _940_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out514;
                      bool _out515;
                      bool _out516;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _936_b), _936_b, _493_toTpe), selfIdent, @params, mustOwn, out _out514, out _out515, out _out516, out _out517);
                      s = _out514;
                      isOwned = _out515;
                      isErased = _out516;
                      readIdents = _out517;
                    }
                  }
                }
              } else if (_source38.is_Nullable) {
                DAST._IType _943___mcc_h517 = _source38.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _944_recursiveGen;
                  bool _945_recOwned;
                  bool _946_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _947_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out518;
                  bool _out519;
                  bool _out520;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out518, out _out519, out _out520, out _out521);
                  _944_recursiveGen = _out518;
                  _945_recOwned = _out519;
                  _946_recErased = _out520;
                  _947_recIdents = _out521;
                  if (!(_945_recOwned)) {
                    _944_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_944_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _944_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _946_recErased;
                  readIdents = _947_recIdents;
                }
              } else if (_source38.is_Tuple) {
                Dafny.ISequence<DAST._IType> _948___mcc_h519 = _source38.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _949_recursiveGen;
                  bool _950_recOwned;
                  bool _951_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _952_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out522;
                  bool _out523;
                  bool _out524;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out522, out _out523, out _out524, out _out525);
                  _949_recursiveGen = _out522;
                  _950_recOwned = _out523;
                  _951_recErased = _out524;
                  _952_recIdents = _out525;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _949_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _950_recOwned;
                  isErased = _951_recErased;
                  readIdents = _952_recIdents;
                }
              } else if (_source38.is_Array) {
                DAST._IType _953___mcc_h521 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _954_recursiveGen;
                  bool _955_recOwned;
                  bool _956_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _957_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out526;
                  bool _out527;
                  bool _out528;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out526, out _out527, out _out528, out _out529);
                  _954_recursiveGen = _out526;
                  _955_recOwned = _out527;
                  _956_recErased = _out528;
                  _957_recIdents = _out529;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _954_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _955_recOwned;
                  isErased = _956_recErased;
                  readIdents = _957_recIdents;
                }
              } else if (_source38.is_Seq) {
                DAST._IType _958___mcc_h523 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _959_recursiveGen;
                  bool _960_recOwned;
                  bool _961_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _962_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out530;
                  bool _out531;
                  bool _out532;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out530, out _out531, out _out532, out _out533);
                  _959_recursiveGen = _out530;
                  _960_recOwned = _out531;
                  _961_recErased = _out532;
                  _962_recIdents = _out533;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _959_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _960_recOwned;
                  isErased = _961_recErased;
                  readIdents = _962_recIdents;
                }
              } else if (_source38.is_Set) {
                DAST._IType _963___mcc_h525 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _964_recursiveGen;
                  bool _965_recOwned;
                  bool _966_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _967_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out534;
                  bool _out535;
                  bool _out536;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out537;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out534, out _out535, out _out536, out _out537);
                  _964_recursiveGen = _out534;
                  _965_recOwned = _out535;
                  _966_recErased = _out536;
                  _967_recIdents = _out537;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _964_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _965_recOwned;
                  isErased = _966_recErased;
                  readIdents = _967_recIdents;
                }
              } else if (_source38.is_Multiset) {
                DAST._IType _968___mcc_h527 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _969_recursiveGen;
                  bool _970_recOwned;
                  bool _971_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _972_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out538;
                  bool _out539;
                  bool _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out538, out _out539, out _out540, out _out541);
                  _969_recursiveGen = _out538;
                  _970_recOwned = _out539;
                  _971_recErased = _out540;
                  _972_recIdents = _out541;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _969_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _970_recOwned;
                  isErased = _971_recErased;
                  readIdents = _972_recIdents;
                }
              } else if (_source38.is_Map) {
                DAST._IType _973___mcc_h529 = _source38.dtor_key;
                DAST._IType _974___mcc_h530 = _source38.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _975_recursiveGen;
                  bool _976_recOwned;
                  bool _977_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _978_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out542;
                  bool _out543;
                  bool _out544;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out542, out _out543, out _out544, out _out545);
                  _975_recursiveGen = _out542;
                  _976_recOwned = _out543;
                  _977_recErased = _out544;
                  _978_recIdents = _out545;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _975_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _976_recOwned;
                  isErased = _977_recErased;
                  readIdents = _978_recIdents;
                }
              } else if (_source38.is_Arrow) {
                Dafny.ISequence<DAST._IType> _979___mcc_h533 = _source38.dtor_args;
                DAST._IType _980___mcc_h534 = _source38.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _981_recursiveGen;
                  bool _982_recOwned;
                  bool _983_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _984_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out546;
                  bool _out547;
                  bool _out548;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out546, out _out547, out _out548, out _out549);
                  _981_recursiveGen = _out546;
                  _982_recOwned = _out547;
                  _983_recErased = _out548;
                  _984_recIdents = _out549;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _981_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _982_recOwned;
                  isErased = _983_recErased;
                  readIdents = _984_recIdents;
                }
              } else if (_source38.is_Primitive) {
                DAST._IPrimitive _985___mcc_h537 = _source38.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _986_recursiveGen;
                  bool _987_recOwned;
                  bool _988_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _989_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out550;
                  bool _out551;
                  bool _out552;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out550, out _out551, out _out552, out _out553);
                  _986_recursiveGen = _out550;
                  _987_recOwned = _out551;
                  _988_recErased = _out552;
                  _989_recIdents = _out553;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _986_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _987_recOwned;
                  isErased = _988_recErased;
                  readIdents = _989_recIdents;
                }
              } else if (_source38.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _990___mcc_h539 = _source38.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _991_recursiveGen;
                  bool _992_recOwned;
                  bool _993_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _994_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out554;
                  bool _out555;
                  bool _out556;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out554, out _out555, out _out556, out _out557);
                  _991_recursiveGen = _out554;
                  _992_recOwned = _out555;
                  _993_recErased = _out556;
                  _994_recIdents = _out557;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _991_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _992_recOwned;
                  isErased = _993_recErased;
                  readIdents = _994_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _995___mcc_h541 = _source38.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _996_recursiveGen;
                  bool _997_recOwned;
                  bool _998_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _999_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out558;
                  bool _out559;
                  bool _out560;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out561;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out558, out _out559, out _out560, out _out561);
                  _996_recursiveGen = _out558;
                  _997_recOwned = _out559;
                  _998_recErased = _out560;
                  _999_recIdents = _out561;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _996_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _997_recOwned;
                  isErased = _998_recErased;
                  readIdents = _999_recIdents;
                }
              }
            } else if (_source26.is_Seq) {
              DAST._IType _1000___mcc_h543 = _source26.dtor_element;
              DAST._IType _source40 = _501___mcc_h238;
              if (_source40.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1001___mcc_h547 = _source40.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1002___mcc_h548 = _source40.dtor_typeArgs;
                DAST._IResolvedType _1003___mcc_h549 = _source40.dtor_resolved;
                DAST._IResolvedType _source41 = _1003___mcc_h549;
                if (_source41.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1004___mcc_h553 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1005_recursiveGen;
                    bool _1006_recOwned;
                    bool _1007_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1008_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out562;
                    bool _out563;
                    bool _out564;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out562, out _out563, out _out564, out _out565);
                    _1005_recursiveGen = _out562;
                    _1006_recOwned = _out563;
                    _1007_recErased = _out564;
                    _1008_recIdents = _out565;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1005_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1006_recOwned;
                    isErased = _1007_recErased;
                    readIdents = _1008_recIdents;
                  }
                } else if (_source41.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1009___mcc_h555 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1010_recursiveGen;
                    bool _1011_recOwned;
                    bool _1012_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1013_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out566;
                    bool _out567;
                    bool _out568;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out566, out _out567, out _out568, out _out569);
                    _1010_recursiveGen = _out566;
                    _1011_recOwned = _out567;
                    _1012_recErased = _out568;
                    _1013_recIdents = _out569;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1010_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1011_recOwned;
                    isErased = _1012_recErased;
                    readIdents = _1013_recIdents;
                  }
                } else {
                  DAST._IType _1014___mcc_h557 = _source41.dtor_Newtype_a0;
                  DAST._IType _1015_b = _1014___mcc_h557;
                  {
                    if (object.Equals(_494_fromTpe, _1015_b)) {
                      Dafny.ISequence<Dafny.Rune> _1016_recursiveGen;
                      bool _1017_recOwned;
                      bool _1018_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1019_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out570;
                      bool _out571;
                      bool _out572;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out573;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out570, out _out571, out _out572, out _out573);
                      _1016_recursiveGen = _out570;
                      _1017_recOwned = _out571;
                      _1018_recErased = _out572;
                      _1019_recIdents = _out573;
                      Dafny.ISequence<Dafny.Rune> _1020_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out574;
                      _out574 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1020_rhsType = _out574;
                      Dafny.ISequence<Dafny.Rune> _1021_uneraseFn;
                      _1021_uneraseFn = ((_1017_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1020_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1021_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1016_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1017_recOwned;
                      isErased = false;
                      readIdents = _1019_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out575;
                      bool _out576;
                      bool _out577;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1015_b), _1015_b, _493_toTpe), selfIdent, @params, mustOwn, out _out575, out _out576, out _out577, out _out578);
                      s = _out575;
                      isOwned = _out576;
                      isErased = _out577;
                      readIdents = _out578;
                    }
                  }
                }
              } else if (_source40.is_Nullable) {
                DAST._IType _1022___mcc_h559 = _source40.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1023_recursiveGen;
                  bool _1024_recOwned;
                  bool _1025_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1026_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out579;
                  bool _out580;
                  bool _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out579, out _out580, out _out581, out _out582);
                  _1023_recursiveGen = _out579;
                  _1024_recOwned = _out580;
                  _1025_recErased = _out581;
                  _1026_recIdents = _out582;
                  if (!(_1024_recOwned)) {
                    _1023_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1023_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1023_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1025_recErased;
                  readIdents = _1026_recIdents;
                }
              } else if (_source40.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1027___mcc_h561 = _source40.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1028_recursiveGen;
                  bool _1029_recOwned;
                  bool _1030_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1031_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out583;
                  bool _out584;
                  bool _out585;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out583, out _out584, out _out585, out _out586);
                  _1028_recursiveGen = _out583;
                  _1029_recOwned = _out584;
                  _1030_recErased = _out585;
                  _1031_recIdents = _out586;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1028_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1029_recOwned;
                  isErased = _1030_recErased;
                  readIdents = _1031_recIdents;
                }
              } else if (_source40.is_Array) {
                DAST._IType _1032___mcc_h563 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1033_recursiveGen;
                  bool _1034_recOwned;
                  bool _1035_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1036_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out587;
                  bool _out588;
                  bool _out589;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out587, out _out588, out _out589, out _out590);
                  _1033_recursiveGen = _out587;
                  _1034_recOwned = _out588;
                  _1035_recErased = _out589;
                  _1036_recIdents = _out590;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1033_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1034_recOwned;
                  isErased = _1035_recErased;
                  readIdents = _1036_recIdents;
                }
              } else if (_source40.is_Seq) {
                DAST._IType _1037___mcc_h565 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1038_recursiveGen;
                  bool _1039_recOwned;
                  bool _1040_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1041_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out591;
                  bool _out592;
                  bool _out593;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out591, out _out592, out _out593, out _out594);
                  _1038_recursiveGen = _out591;
                  _1039_recOwned = _out592;
                  _1040_recErased = _out593;
                  _1041_recIdents = _out594;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1038_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1039_recOwned;
                  isErased = _1040_recErased;
                  readIdents = _1041_recIdents;
                }
              } else if (_source40.is_Set) {
                DAST._IType _1042___mcc_h567 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1043_recursiveGen;
                  bool _1044_recOwned;
                  bool _1045_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1046_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out595;
                  bool _out596;
                  bool _out597;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out595, out _out596, out _out597, out _out598);
                  _1043_recursiveGen = _out595;
                  _1044_recOwned = _out596;
                  _1045_recErased = _out597;
                  _1046_recIdents = _out598;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1043_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1044_recOwned;
                  isErased = _1045_recErased;
                  readIdents = _1046_recIdents;
                }
              } else if (_source40.is_Multiset) {
                DAST._IType _1047___mcc_h569 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1048_recursiveGen;
                  bool _1049_recOwned;
                  bool _1050_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1051_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out599;
                  bool _out600;
                  bool _out601;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out599, out _out600, out _out601, out _out602);
                  _1048_recursiveGen = _out599;
                  _1049_recOwned = _out600;
                  _1050_recErased = _out601;
                  _1051_recIdents = _out602;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1048_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1049_recOwned;
                  isErased = _1050_recErased;
                  readIdents = _1051_recIdents;
                }
              } else if (_source40.is_Map) {
                DAST._IType _1052___mcc_h571 = _source40.dtor_key;
                DAST._IType _1053___mcc_h572 = _source40.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1054_recursiveGen;
                  bool _1055_recOwned;
                  bool _1056_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1057_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out603;
                  bool _out604;
                  bool _out605;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out603, out _out604, out _out605, out _out606);
                  _1054_recursiveGen = _out603;
                  _1055_recOwned = _out604;
                  _1056_recErased = _out605;
                  _1057_recIdents = _out606;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1054_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1055_recOwned;
                  isErased = _1056_recErased;
                  readIdents = _1057_recIdents;
                }
              } else if (_source40.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1058___mcc_h575 = _source40.dtor_args;
                DAST._IType _1059___mcc_h576 = _source40.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1060_recursiveGen;
                  bool _1061_recOwned;
                  bool _1062_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1063_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out607;
                  bool _out608;
                  bool _out609;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out607, out _out608, out _out609, out _out610);
                  _1060_recursiveGen = _out607;
                  _1061_recOwned = _out608;
                  _1062_recErased = _out609;
                  _1063_recIdents = _out610;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1060_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1061_recOwned;
                  isErased = _1062_recErased;
                  readIdents = _1063_recIdents;
                }
              } else if (_source40.is_Primitive) {
                DAST._IPrimitive _1064___mcc_h579 = _source40.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1065_recursiveGen;
                  bool _1066_recOwned;
                  bool _1067_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1068_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out611;
                  bool _out612;
                  bool _out613;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out611, out _out612, out _out613, out _out614);
                  _1065_recursiveGen = _out611;
                  _1066_recOwned = _out612;
                  _1067_recErased = _out613;
                  _1068_recIdents = _out614;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1065_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1066_recOwned;
                  isErased = _1067_recErased;
                  readIdents = _1068_recIdents;
                }
              } else if (_source40.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1069___mcc_h581 = _source40.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1070_recursiveGen;
                  bool _1071_recOwned;
                  bool _1072_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1073_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out615;
                  bool _out616;
                  bool _out617;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out618;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out615, out _out616, out _out617, out _out618);
                  _1070_recursiveGen = _out615;
                  _1071_recOwned = _out616;
                  _1072_recErased = _out617;
                  _1073_recIdents = _out618;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1070_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1071_recOwned;
                  isErased = _1072_recErased;
                  readIdents = _1073_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1074___mcc_h583 = _source40.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1075_recursiveGen;
                  bool _1076_recOwned;
                  bool _1077_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1078_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out619;
                  bool _out620;
                  bool _out621;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out619, out _out620, out _out621, out _out622);
                  _1075_recursiveGen = _out619;
                  _1076_recOwned = _out620;
                  _1077_recErased = _out621;
                  _1078_recIdents = _out622;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1075_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1076_recOwned;
                  isErased = _1077_recErased;
                  readIdents = _1078_recIdents;
                }
              }
            } else if (_source26.is_Set) {
              DAST._IType _1079___mcc_h585 = _source26.dtor_element;
              DAST._IType _source42 = _501___mcc_h238;
              if (_source42.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1080___mcc_h589 = _source42.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1081___mcc_h590 = _source42.dtor_typeArgs;
                DAST._IResolvedType _1082___mcc_h591 = _source42.dtor_resolved;
                DAST._IResolvedType _source43 = _1082___mcc_h591;
                if (_source43.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1083___mcc_h595 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1084_recursiveGen;
                    bool _1085_recOwned;
                    bool _1086_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1087_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out623;
                    bool _out624;
                    bool _out625;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out626;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out623, out _out624, out _out625, out _out626);
                    _1084_recursiveGen = _out623;
                    _1085_recOwned = _out624;
                    _1086_recErased = _out625;
                    _1087_recIdents = _out626;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1084_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1085_recOwned;
                    isErased = _1086_recErased;
                    readIdents = _1087_recIdents;
                  }
                } else if (_source43.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1088___mcc_h597 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1089_recursiveGen;
                    bool _1090_recOwned;
                    bool _1091_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1092_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out627;
                    bool _out628;
                    bool _out629;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out627, out _out628, out _out629, out _out630);
                    _1089_recursiveGen = _out627;
                    _1090_recOwned = _out628;
                    _1091_recErased = _out629;
                    _1092_recIdents = _out630;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1089_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1090_recOwned;
                    isErased = _1091_recErased;
                    readIdents = _1092_recIdents;
                  }
                } else {
                  DAST._IType _1093___mcc_h599 = _source43.dtor_Newtype_a0;
                  DAST._IType _1094_b = _1093___mcc_h599;
                  {
                    if (object.Equals(_494_fromTpe, _1094_b)) {
                      Dafny.ISequence<Dafny.Rune> _1095_recursiveGen;
                      bool _1096_recOwned;
                      bool _1097_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1098_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out631;
                      bool _out632;
                      bool _out633;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out631, out _out632, out _out633, out _out634);
                      _1095_recursiveGen = _out631;
                      _1096_recOwned = _out632;
                      _1097_recErased = _out633;
                      _1098_recIdents = _out634;
                      Dafny.ISequence<Dafny.Rune> _1099_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out635;
                      _out635 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1099_rhsType = _out635;
                      Dafny.ISequence<Dafny.Rune> _1100_uneraseFn;
                      _1100_uneraseFn = ((_1096_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1099_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1100_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1095_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1096_recOwned;
                      isErased = false;
                      readIdents = _1098_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out636;
                      bool _out637;
                      bool _out638;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1094_b), _1094_b, _493_toTpe), selfIdent, @params, mustOwn, out _out636, out _out637, out _out638, out _out639);
                      s = _out636;
                      isOwned = _out637;
                      isErased = _out638;
                      readIdents = _out639;
                    }
                  }
                }
              } else if (_source42.is_Nullable) {
                DAST._IType _1101___mcc_h601 = _source42.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1102_recursiveGen;
                  bool _1103_recOwned;
                  bool _1104_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1105_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out640;
                  bool _out641;
                  bool _out642;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out640, out _out641, out _out642, out _out643);
                  _1102_recursiveGen = _out640;
                  _1103_recOwned = _out641;
                  _1104_recErased = _out642;
                  _1105_recIdents = _out643;
                  if (!(_1103_recOwned)) {
                    _1102_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1102_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1102_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1104_recErased;
                  readIdents = _1105_recIdents;
                }
              } else if (_source42.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1106___mcc_h603 = _source42.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1107_recursiveGen;
                  bool _1108_recOwned;
                  bool _1109_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1110_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out644;
                  bool _out645;
                  bool _out646;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out644, out _out645, out _out646, out _out647);
                  _1107_recursiveGen = _out644;
                  _1108_recOwned = _out645;
                  _1109_recErased = _out646;
                  _1110_recIdents = _out647;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1107_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1108_recOwned;
                  isErased = _1109_recErased;
                  readIdents = _1110_recIdents;
                }
              } else if (_source42.is_Array) {
                DAST._IType _1111___mcc_h605 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1112_recursiveGen;
                  bool _1113_recOwned;
                  bool _1114_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1115_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out648;
                  bool _out649;
                  bool _out650;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out651;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out648, out _out649, out _out650, out _out651);
                  _1112_recursiveGen = _out648;
                  _1113_recOwned = _out649;
                  _1114_recErased = _out650;
                  _1115_recIdents = _out651;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1112_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1113_recOwned;
                  isErased = _1114_recErased;
                  readIdents = _1115_recIdents;
                }
              } else if (_source42.is_Seq) {
                DAST._IType _1116___mcc_h607 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1117_recursiveGen;
                  bool _1118_recOwned;
                  bool _1119_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1120_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out652;
                  bool _out653;
                  bool _out654;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out652, out _out653, out _out654, out _out655);
                  _1117_recursiveGen = _out652;
                  _1118_recOwned = _out653;
                  _1119_recErased = _out654;
                  _1120_recIdents = _out655;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1117_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1118_recOwned;
                  isErased = _1119_recErased;
                  readIdents = _1120_recIdents;
                }
              } else if (_source42.is_Set) {
                DAST._IType _1121___mcc_h609 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1122_recursiveGen;
                  bool _1123_recOwned;
                  bool _1124_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1125_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out656;
                  bool _out657;
                  bool _out658;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out659;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out656, out _out657, out _out658, out _out659);
                  _1122_recursiveGen = _out656;
                  _1123_recOwned = _out657;
                  _1124_recErased = _out658;
                  _1125_recIdents = _out659;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1122_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1123_recOwned;
                  isErased = _1124_recErased;
                  readIdents = _1125_recIdents;
                }
              } else if (_source42.is_Multiset) {
                DAST._IType _1126___mcc_h611 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1127_recursiveGen;
                  bool _1128_recOwned;
                  bool _1129_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1130_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out660;
                  bool _out661;
                  bool _out662;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out660, out _out661, out _out662, out _out663);
                  _1127_recursiveGen = _out660;
                  _1128_recOwned = _out661;
                  _1129_recErased = _out662;
                  _1130_recIdents = _out663;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1127_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1128_recOwned;
                  isErased = _1129_recErased;
                  readIdents = _1130_recIdents;
                }
              } else if (_source42.is_Map) {
                DAST._IType _1131___mcc_h613 = _source42.dtor_key;
                DAST._IType _1132___mcc_h614 = _source42.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1133_recursiveGen;
                  bool _1134_recOwned;
                  bool _1135_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1136_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out664;
                  bool _out665;
                  bool _out666;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out664, out _out665, out _out666, out _out667);
                  _1133_recursiveGen = _out664;
                  _1134_recOwned = _out665;
                  _1135_recErased = _out666;
                  _1136_recIdents = _out667;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1133_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1134_recOwned;
                  isErased = _1135_recErased;
                  readIdents = _1136_recIdents;
                }
              } else if (_source42.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1137___mcc_h617 = _source42.dtor_args;
                DAST._IType _1138___mcc_h618 = _source42.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1139_recursiveGen;
                  bool _1140_recOwned;
                  bool _1141_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1142_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out668;
                  bool _out669;
                  bool _out670;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out671;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out668, out _out669, out _out670, out _out671);
                  _1139_recursiveGen = _out668;
                  _1140_recOwned = _out669;
                  _1141_recErased = _out670;
                  _1142_recIdents = _out671;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1139_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1140_recOwned;
                  isErased = _1141_recErased;
                  readIdents = _1142_recIdents;
                }
              } else if (_source42.is_Primitive) {
                DAST._IPrimitive _1143___mcc_h621 = _source42.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1144_recursiveGen;
                  bool _1145_recOwned;
                  bool _1146_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1147_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out672;
                  bool _out673;
                  bool _out674;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out675;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out672, out _out673, out _out674, out _out675);
                  _1144_recursiveGen = _out672;
                  _1145_recOwned = _out673;
                  _1146_recErased = _out674;
                  _1147_recIdents = _out675;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1144_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1145_recOwned;
                  isErased = _1146_recErased;
                  readIdents = _1147_recIdents;
                }
              } else if (_source42.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1148___mcc_h623 = _source42.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1149_recursiveGen;
                  bool _1150_recOwned;
                  bool _1151_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1152_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out676;
                  bool _out677;
                  bool _out678;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out676, out _out677, out _out678, out _out679);
                  _1149_recursiveGen = _out676;
                  _1150_recOwned = _out677;
                  _1151_recErased = _out678;
                  _1152_recIdents = _out679;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1149_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1150_recOwned;
                  isErased = _1151_recErased;
                  readIdents = _1152_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1153___mcc_h625 = _source42.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1154_recursiveGen;
                  bool _1155_recOwned;
                  bool _1156_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1157_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out680;
                  bool _out681;
                  bool _out682;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out683;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out680, out _out681, out _out682, out _out683);
                  _1154_recursiveGen = _out680;
                  _1155_recOwned = _out681;
                  _1156_recErased = _out682;
                  _1157_recIdents = _out683;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1154_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1155_recOwned;
                  isErased = _1156_recErased;
                  readIdents = _1157_recIdents;
                }
              }
            } else if (_source26.is_Multiset) {
              DAST._IType _1158___mcc_h627 = _source26.dtor_element;
              DAST._IType _source44 = _501___mcc_h238;
              if (_source44.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1159___mcc_h631 = _source44.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1160___mcc_h632 = _source44.dtor_typeArgs;
                DAST._IResolvedType _1161___mcc_h633 = _source44.dtor_resolved;
                DAST._IResolvedType _source45 = _1161___mcc_h633;
                if (_source45.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1162___mcc_h637 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1163_recursiveGen;
                    bool _1164_recOwned;
                    bool _1165_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1166_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out684;
                    bool _out685;
                    bool _out686;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out687;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out684, out _out685, out _out686, out _out687);
                    _1163_recursiveGen = _out684;
                    _1164_recOwned = _out685;
                    _1165_recErased = _out686;
                    _1166_recIdents = _out687;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1163_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1164_recOwned;
                    isErased = _1165_recErased;
                    readIdents = _1166_recIdents;
                  }
                } else if (_source45.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1167___mcc_h639 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1168_recursiveGen;
                    bool _1169_recOwned;
                    bool _1170_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1171_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out688;
                    bool _out689;
                    bool _out690;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out688, out _out689, out _out690, out _out691);
                    _1168_recursiveGen = _out688;
                    _1169_recOwned = _out689;
                    _1170_recErased = _out690;
                    _1171_recIdents = _out691;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1168_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1169_recOwned;
                    isErased = _1170_recErased;
                    readIdents = _1171_recIdents;
                  }
                } else {
                  DAST._IType _1172___mcc_h641 = _source45.dtor_Newtype_a0;
                  DAST._IType _1173_b = _1172___mcc_h641;
                  {
                    if (object.Equals(_494_fromTpe, _1173_b)) {
                      Dafny.ISequence<Dafny.Rune> _1174_recursiveGen;
                      bool _1175_recOwned;
                      bool _1176_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1177_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out692;
                      bool _out693;
                      bool _out694;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out695;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out692, out _out693, out _out694, out _out695);
                      _1174_recursiveGen = _out692;
                      _1175_recOwned = _out693;
                      _1176_recErased = _out694;
                      _1177_recIdents = _out695;
                      Dafny.ISequence<Dafny.Rune> _1178_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out696;
                      _out696 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1178_rhsType = _out696;
                      Dafny.ISequence<Dafny.Rune> _1179_uneraseFn;
                      _1179_uneraseFn = ((_1175_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1178_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1179_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1174_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1175_recOwned;
                      isErased = false;
                      readIdents = _1177_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out697;
                      bool _out698;
                      bool _out699;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1173_b), _1173_b, _493_toTpe), selfIdent, @params, mustOwn, out _out697, out _out698, out _out699, out _out700);
                      s = _out697;
                      isOwned = _out698;
                      isErased = _out699;
                      readIdents = _out700;
                    }
                  }
                }
              } else if (_source44.is_Nullable) {
                DAST._IType _1180___mcc_h643 = _source44.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1181_recursiveGen;
                  bool _1182_recOwned;
                  bool _1183_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1184_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out701;
                  bool _out702;
                  bool _out703;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out704;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out701, out _out702, out _out703, out _out704);
                  _1181_recursiveGen = _out701;
                  _1182_recOwned = _out702;
                  _1183_recErased = _out703;
                  _1184_recIdents = _out704;
                  if (!(_1182_recOwned)) {
                    _1181_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1181_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1181_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1183_recErased;
                  readIdents = _1184_recIdents;
                }
              } else if (_source44.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1185___mcc_h645 = _source44.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1186_recursiveGen;
                  bool _1187_recOwned;
                  bool _1188_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1189_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out705;
                  bool _out706;
                  bool _out707;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out708;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out705, out _out706, out _out707, out _out708);
                  _1186_recursiveGen = _out705;
                  _1187_recOwned = _out706;
                  _1188_recErased = _out707;
                  _1189_recIdents = _out708;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1186_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1187_recOwned;
                  isErased = _1188_recErased;
                  readIdents = _1189_recIdents;
                }
              } else if (_source44.is_Array) {
                DAST._IType _1190___mcc_h647 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1191_recursiveGen;
                  bool _1192_recOwned;
                  bool _1193_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1194_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out709;
                  bool _out710;
                  bool _out711;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out709, out _out710, out _out711, out _out712);
                  _1191_recursiveGen = _out709;
                  _1192_recOwned = _out710;
                  _1193_recErased = _out711;
                  _1194_recIdents = _out712;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1191_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1192_recOwned;
                  isErased = _1193_recErased;
                  readIdents = _1194_recIdents;
                }
              } else if (_source44.is_Seq) {
                DAST._IType _1195___mcc_h649 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1196_recursiveGen;
                  bool _1197_recOwned;
                  bool _1198_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1199_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out713;
                  bool _out714;
                  bool _out715;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out716;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out713, out _out714, out _out715, out _out716);
                  _1196_recursiveGen = _out713;
                  _1197_recOwned = _out714;
                  _1198_recErased = _out715;
                  _1199_recIdents = _out716;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1196_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1197_recOwned;
                  isErased = _1198_recErased;
                  readIdents = _1199_recIdents;
                }
              } else if (_source44.is_Set) {
                DAST._IType _1200___mcc_h651 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1201_recursiveGen;
                  bool _1202_recOwned;
                  bool _1203_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1204_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out717;
                  bool _out718;
                  bool _out719;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out720;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out717, out _out718, out _out719, out _out720);
                  _1201_recursiveGen = _out717;
                  _1202_recOwned = _out718;
                  _1203_recErased = _out719;
                  _1204_recIdents = _out720;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1201_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1202_recOwned;
                  isErased = _1203_recErased;
                  readIdents = _1204_recIdents;
                }
              } else if (_source44.is_Multiset) {
                DAST._IType _1205___mcc_h653 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1206_recursiveGen;
                  bool _1207_recOwned;
                  bool _1208_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1209_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out721;
                  bool _out722;
                  bool _out723;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out721, out _out722, out _out723, out _out724);
                  _1206_recursiveGen = _out721;
                  _1207_recOwned = _out722;
                  _1208_recErased = _out723;
                  _1209_recIdents = _out724;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1206_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1207_recOwned;
                  isErased = _1208_recErased;
                  readIdents = _1209_recIdents;
                }
              } else if (_source44.is_Map) {
                DAST._IType _1210___mcc_h655 = _source44.dtor_key;
                DAST._IType _1211___mcc_h656 = _source44.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1212_recursiveGen;
                  bool _1213_recOwned;
                  bool _1214_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1215_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out725;
                  bool _out726;
                  bool _out727;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out728;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out725, out _out726, out _out727, out _out728);
                  _1212_recursiveGen = _out725;
                  _1213_recOwned = _out726;
                  _1214_recErased = _out727;
                  _1215_recIdents = _out728;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1212_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1213_recOwned;
                  isErased = _1214_recErased;
                  readIdents = _1215_recIdents;
                }
              } else if (_source44.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1216___mcc_h659 = _source44.dtor_args;
                DAST._IType _1217___mcc_h660 = _source44.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1218_recursiveGen;
                  bool _1219_recOwned;
                  bool _1220_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1221_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out729;
                  bool _out730;
                  bool _out731;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out732;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out729, out _out730, out _out731, out _out732);
                  _1218_recursiveGen = _out729;
                  _1219_recOwned = _out730;
                  _1220_recErased = _out731;
                  _1221_recIdents = _out732;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1218_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1219_recOwned;
                  isErased = _1220_recErased;
                  readIdents = _1221_recIdents;
                }
              } else if (_source44.is_Primitive) {
                DAST._IPrimitive _1222___mcc_h663 = _source44.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1223_recursiveGen;
                  bool _1224_recOwned;
                  bool _1225_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1226_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out733;
                  bool _out734;
                  bool _out735;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out733, out _out734, out _out735, out _out736);
                  _1223_recursiveGen = _out733;
                  _1224_recOwned = _out734;
                  _1225_recErased = _out735;
                  _1226_recIdents = _out736;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1223_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1224_recOwned;
                  isErased = _1225_recErased;
                  readIdents = _1226_recIdents;
                }
              } else if (_source44.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1227___mcc_h665 = _source44.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1228_recursiveGen;
                  bool _1229_recOwned;
                  bool _1230_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1231_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out737;
                  bool _out738;
                  bool _out739;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out740;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out737, out _out738, out _out739, out _out740);
                  _1228_recursiveGen = _out737;
                  _1229_recOwned = _out738;
                  _1230_recErased = _out739;
                  _1231_recIdents = _out740;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1228_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1229_recOwned;
                  isErased = _1230_recErased;
                  readIdents = _1231_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1232___mcc_h667 = _source44.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1233_recursiveGen;
                  bool _1234_recOwned;
                  bool _1235_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1236_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out741;
                  bool _out742;
                  bool _out743;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out744;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out741, out _out742, out _out743, out _out744);
                  _1233_recursiveGen = _out741;
                  _1234_recOwned = _out742;
                  _1235_recErased = _out743;
                  _1236_recIdents = _out744;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1233_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1234_recOwned;
                  isErased = _1235_recErased;
                  readIdents = _1236_recIdents;
                }
              }
            } else if (_source26.is_Map) {
              DAST._IType _1237___mcc_h669 = _source26.dtor_key;
              DAST._IType _1238___mcc_h670 = _source26.dtor_value;
              DAST._IType _source46 = _501___mcc_h238;
              if (_source46.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1239___mcc_h677 = _source46.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1240___mcc_h678 = _source46.dtor_typeArgs;
                DAST._IResolvedType _1241___mcc_h679 = _source46.dtor_resolved;
                DAST._IResolvedType _source47 = _1241___mcc_h679;
                if (_source47.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1242___mcc_h683 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1243_recursiveGen;
                    bool _1244_recOwned;
                    bool _1245_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1246_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out745;
                    bool _out746;
                    bool _out747;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out745, out _out746, out _out747, out _out748);
                    _1243_recursiveGen = _out745;
                    _1244_recOwned = _out746;
                    _1245_recErased = _out747;
                    _1246_recIdents = _out748;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1243_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1244_recOwned;
                    isErased = _1245_recErased;
                    readIdents = _1246_recIdents;
                  }
                } else if (_source47.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1247___mcc_h685 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1248_recursiveGen;
                    bool _1249_recOwned;
                    bool _1250_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1251_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out749;
                    bool _out750;
                    bool _out751;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out752;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out749, out _out750, out _out751, out _out752);
                    _1248_recursiveGen = _out749;
                    _1249_recOwned = _out750;
                    _1250_recErased = _out751;
                    _1251_recIdents = _out752;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1248_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1249_recOwned;
                    isErased = _1250_recErased;
                    readIdents = _1251_recIdents;
                  }
                } else {
                  DAST._IType _1252___mcc_h687 = _source47.dtor_Newtype_a0;
                  DAST._IType _1253_b = _1252___mcc_h687;
                  {
                    if (object.Equals(_494_fromTpe, _1253_b)) {
                      Dafny.ISequence<Dafny.Rune> _1254_recursiveGen;
                      bool _1255_recOwned;
                      bool _1256_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1257_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out753;
                      bool _out754;
                      bool _out755;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out756;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out753, out _out754, out _out755, out _out756);
                      _1254_recursiveGen = _out753;
                      _1255_recOwned = _out754;
                      _1256_recErased = _out755;
                      _1257_recIdents = _out756;
                      Dafny.ISequence<Dafny.Rune> _1258_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out757;
                      _out757 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1258_rhsType = _out757;
                      Dafny.ISequence<Dafny.Rune> _1259_uneraseFn;
                      _1259_uneraseFn = ((_1255_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1258_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1259_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1254_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1255_recOwned;
                      isErased = false;
                      readIdents = _1257_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out758;
                      bool _out759;
                      bool _out760;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out761;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1253_b), _1253_b, _493_toTpe), selfIdent, @params, mustOwn, out _out758, out _out759, out _out760, out _out761);
                      s = _out758;
                      isOwned = _out759;
                      isErased = _out760;
                      readIdents = _out761;
                    }
                  }
                }
              } else if (_source46.is_Nullable) {
                DAST._IType _1260___mcc_h689 = _source46.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1261_recursiveGen;
                  bool _1262_recOwned;
                  bool _1263_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1264_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out762;
                  bool _out763;
                  bool _out764;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out762, out _out763, out _out764, out _out765);
                  _1261_recursiveGen = _out762;
                  _1262_recOwned = _out763;
                  _1263_recErased = _out764;
                  _1264_recIdents = _out765;
                  if (!(_1262_recOwned)) {
                    _1261_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1261_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1261_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1263_recErased;
                  readIdents = _1264_recIdents;
                }
              } else if (_source46.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1265___mcc_h691 = _source46.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1266_recursiveGen;
                  bool _1267_recOwned;
                  bool _1268_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1269_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out766;
                  bool _out767;
                  bool _out768;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out766, out _out767, out _out768, out _out769);
                  _1266_recursiveGen = _out766;
                  _1267_recOwned = _out767;
                  _1268_recErased = _out768;
                  _1269_recIdents = _out769;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1266_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1267_recOwned;
                  isErased = _1268_recErased;
                  readIdents = _1269_recIdents;
                }
              } else if (_source46.is_Array) {
                DAST._IType _1270___mcc_h693 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1271_recursiveGen;
                  bool _1272_recOwned;
                  bool _1273_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1274_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out770;
                  bool _out771;
                  bool _out772;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out773;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out770, out _out771, out _out772, out _out773);
                  _1271_recursiveGen = _out770;
                  _1272_recOwned = _out771;
                  _1273_recErased = _out772;
                  _1274_recIdents = _out773;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1271_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1272_recOwned;
                  isErased = _1273_recErased;
                  readIdents = _1274_recIdents;
                }
              } else if (_source46.is_Seq) {
                DAST._IType _1275___mcc_h695 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1276_recursiveGen;
                  bool _1277_recOwned;
                  bool _1278_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1279_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out774;
                  bool _out775;
                  bool _out776;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out777;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out774, out _out775, out _out776, out _out777);
                  _1276_recursiveGen = _out774;
                  _1277_recOwned = _out775;
                  _1278_recErased = _out776;
                  _1279_recIdents = _out777;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1276_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1277_recOwned;
                  isErased = _1278_recErased;
                  readIdents = _1279_recIdents;
                }
              } else if (_source46.is_Set) {
                DAST._IType _1280___mcc_h697 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1281_recursiveGen;
                  bool _1282_recOwned;
                  bool _1283_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1284_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out778;
                  bool _out779;
                  bool _out780;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out778, out _out779, out _out780, out _out781);
                  _1281_recursiveGen = _out778;
                  _1282_recOwned = _out779;
                  _1283_recErased = _out780;
                  _1284_recIdents = _out781;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1281_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1282_recOwned;
                  isErased = _1283_recErased;
                  readIdents = _1284_recIdents;
                }
              } else if (_source46.is_Multiset) {
                DAST._IType _1285___mcc_h699 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1286_recursiveGen;
                  bool _1287_recOwned;
                  bool _1288_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1289_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out782;
                  bool _out783;
                  bool _out784;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out785;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out782, out _out783, out _out784, out _out785);
                  _1286_recursiveGen = _out782;
                  _1287_recOwned = _out783;
                  _1288_recErased = _out784;
                  _1289_recIdents = _out785;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1286_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1287_recOwned;
                  isErased = _1288_recErased;
                  readIdents = _1289_recIdents;
                }
              } else if (_source46.is_Map) {
                DAST._IType _1290___mcc_h701 = _source46.dtor_key;
                DAST._IType _1291___mcc_h702 = _source46.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1292_recursiveGen;
                  bool _1293_recOwned;
                  bool _1294_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1295_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out786;
                  bool _out787;
                  bool _out788;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out789;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out786, out _out787, out _out788, out _out789);
                  _1292_recursiveGen = _out786;
                  _1293_recOwned = _out787;
                  _1294_recErased = _out788;
                  _1295_recIdents = _out789;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1292_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1293_recOwned;
                  isErased = _1294_recErased;
                  readIdents = _1295_recIdents;
                }
              } else if (_source46.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1296___mcc_h705 = _source46.dtor_args;
                DAST._IType _1297___mcc_h706 = _source46.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1298_recursiveGen;
                  bool _1299_recOwned;
                  bool _1300_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1301_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out790;
                  bool _out791;
                  bool _out792;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out790, out _out791, out _out792, out _out793);
                  _1298_recursiveGen = _out790;
                  _1299_recOwned = _out791;
                  _1300_recErased = _out792;
                  _1301_recIdents = _out793;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1298_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1299_recOwned;
                  isErased = _1300_recErased;
                  readIdents = _1301_recIdents;
                }
              } else if (_source46.is_Primitive) {
                DAST._IPrimitive _1302___mcc_h709 = _source46.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1303_recursiveGen;
                  bool _1304_recOwned;
                  bool _1305_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1306_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out794;
                  bool _out795;
                  bool _out796;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out797;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out794, out _out795, out _out796, out _out797);
                  _1303_recursiveGen = _out794;
                  _1304_recOwned = _out795;
                  _1305_recErased = _out796;
                  _1306_recIdents = _out797;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1303_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1304_recOwned;
                  isErased = _1305_recErased;
                  readIdents = _1306_recIdents;
                }
              } else if (_source46.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1307___mcc_h711 = _source46.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1308_recursiveGen;
                  bool _1309_recOwned;
                  bool _1310_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1311_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out798;
                  bool _out799;
                  bool _out800;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out801;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out798, out _out799, out _out800, out _out801);
                  _1308_recursiveGen = _out798;
                  _1309_recOwned = _out799;
                  _1310_recErased = _out800;
                  _1311_recIdents = _out801;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1308_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1309_recOwned;
                  isErased = _1310_recErased;
                  readIdents = _1311_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1312___mcc_h713 = _source46.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1313_recursiveGen;
                  bool _1314_recOwned;
                  bool _1315_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1316_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out802;
                  bool _out803;
                  bool _out804;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out802, out _out803, out _out804, out _out805);
                  _1313_recursiveGen = _out802;
                  _1314_recOwned = _out803;
                  _1315_recErased = _out804;
                  _1316_recIdents = _out805;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1313_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1314_recOwned;
                  isErased = _1315_recErased;
                  readIdents = _1316_recIdents;
                }
              }
            } else if (_source26.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1317___mcc_h715 = _source26.dtor_args;
              DAST._IType _1318___mcc_h716 = _source26.dtor_result;
              DAST._IType _source48 = _501___mcc_h238;
              if (_source48.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1319___mcc_h723 = _source48.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1320___mcc_h724 = _source48.dtor_typeArgs;
                DAST._IResolvedType _1321___mcc_h725 = _source48.dtor_resolved;
                DAST._IResolvedType _source49 = _1321___mcc_h725;
                if (_source49.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1322___mcc_h729 = _source49.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1323_recursiveGen;
                    bool _1324_recOwned;
                    bool _1325_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1326_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out806;
                    bool _out807;
                    bool _out808;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out809;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out806, out _out807, out _out808, out _out809);
                    _1323_recursiveGen = _out806;
                    _1324_recOwned = _out807;
                    _1325_recErased = _out808;
                    _1326_recIdents = _out809;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1323_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1324_recOwned;
                    isErased = _1325_recErased;
                    readIdents = _1326_recIdents;
                  }
                } else if (_source49.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1327___mcc_h731 = _source49.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1328_recursiveGen;
                    bool _1329_recOwned;
                    bool _1330_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1331_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out810;
                    bool _out811;
                    bool _out812;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out813;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out810, out _out811, out _out812, out _out813);
                    _1328_recursiveGen = _out810;
                    _1329_recOwned = _out811;
                    _1330_recErased = _out812;
                    _1331_recIdents = _out813;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1328_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1329_recOwned;
                    isErased = _1330_recErased;
                    readIdents = _1331_recIdents;
                  }
                } else {
                  DAST._IType _1332___mcc_h733 = _source49.dtor_Newtype_a0;
                  DAST._IType _1333_b = _1332___mcc_h733;
                  {
                    if (object.Equals(_494_fromTpe, _1333_b)) {
                      Dafny.ISequence<Dafny.Rune> _1334_recursiveGen;
                      bool _1335_recOwned;
                      bool _1336_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1337_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out814;
                      bool _out815;
                      bool _out816;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out814, out _out815, out _out816, out _out817);
                      _1334_recursiveGen = _out814;
                      _1335_recOwned = _out815;
                      _1336_recErased = _out816;
                      _1337_recIdents = _out817;
                      Dafny.ISequence<Dafny.Rune> _1338_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out818;
                      _out818 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1338_rhsType = _out818;
                      Dafny.ISequence<Dafny.Rune> _1339_uneraseFn;
                      _1339_uneraseFn = ((_1335_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1338_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1339_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1334_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1335_recOwned;
                      isErased = false;
                      readIdents = _1337_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out819;
                      bool _out820;
                      bool _out821;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out822;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1333_b), _1333_b, _493_toTpe), selfIdent, @params, mustOwn, out _out819, out _out820, out _out821, out _out822);
                      s = _out819;
                      isOwned = _out820;
                      isErased = _out821;
                      readIdents = _out822;
                    }
                  }
                }
              } else if (_source48.is_Nullable) {
                DAST._IType _1340___mcc_h735 = _source48.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1341_recursiveGen;
                  bool _1342_recOwned;
                  bool _1343_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1344_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out823;
                  bool _out824;
                  bool _out825;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out823, out _out824, out _out825, out _out826);
                  _1341_recursiveGen = _out823;
                  _1342_recOwned = _out824;
                  _1343_recErased = _out825;
                  _1344_recIdents = _out826;
                  if (!(_1342_recOwned)) {
                    _1341_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1341_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1341_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1343_recErased;
                  readIdents = _1344_recIdents;
                }
              } else if (_source48.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1345___mcc_h737 = _source48.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1346_recursiveGen;
                  bool _1347_recOwned;
                  bool _1348_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1349_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out827;
                  bool _out828;
                  bool _out829;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out830;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out827, out _out828, out _out829, out _out830);
                  _1346_recursiveGen = _out827;
                  _1347_recOwned = _out828;
                  _1348_recErased = _out829;
                  _1349_recIdents = _out830;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1346_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1347_recOwned;
                  isErased = _1348_recErased;
                  readIdents = _1349_recIdents;
                }
              } else if (_source48.is_Array) {
                DAST._IType _1350___mcc_h739 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1351_recursiveGen;
                  bool _1352_recOwned;
                  bool _1353_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1354_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out831;
                  bool _out832;
                  bool _out833;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out834;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out831, out _out832, out _out833, out _out834);
                  _1351_recursiveGen = _out831;
                  _1352_recOwned = _out832;
                  _1353_recErased = _out833;
                  _1354_recIdents = _out834;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1351_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1352_recOwned;
                  isErased = _1353_recErased;
                  readIdents = _1354_recIdents;
                }
              } else if (_source48.is_Seq) {
                DAST._IType _1355___mcc_h741 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1356_recursiveGen;
                  bool _1357_recOwned;
                  bool _1358_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1359_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out835;
                  bool _out836;
                  bool _out837;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out835, out _out836, out _out837, out _out838);
                  _1356_recursiveGen = _out835;
                  _1357_recOwned = _out836;
                  _1358_recErased = _out837;
                  _1359_recIdents = _out838;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1356_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1357_recOwned;
                  isErased = _1358_recErased;
                  readIdents = _1359_recIdents;
                }
              } else if (_source48.is_Set) {
                DAST._IType _1360___mcc_h743 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1361_recursiveGen;
                  bool _1362_recOwned;
                  bool _1363_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1364_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out839;
                  bool _out840;
                  bool _out841;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out842;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out839, out _out840, out _out841, out _out842);
                  _1361_recursiveGen = _out839;
                  _1362_recOwned = _out840;
                  _1363_recErased = _out841;
                  _1364_recIdents = _out842;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1361_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1362_recOwned;
                  isErased = _1363_recErased;
                  readIdents = _1364_recIdents;
                }
              } else if (_source48.is_Multiset) {
                DAST._IType _1365___mcc_h745 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1366_recursiveGen;
                  bool _1367_recOwned;
                  bool _1368_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1369_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out843;
                  bool _out844;
                  bool _out845;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out846;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out843, out _out844, out _out845, out _out846);
                  _1366_recursiveGen = _out843;
                  _1367_recOwned = _out844;
                  _1368_recErased = _out845;
                  _1369_recIdents = _out846;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1366_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1367_recOwned;
                  isErased = _1368_recErased;
                  readIdents = _1369_recIdents;
                }
              } else if (_source48.is_Map) {
                DAST._IType _1370___mcc_h747 = _source48.dtor_key;
                DAST._IType _1371___mcc_h748 = _source48.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1372_recursiveGen;
                  bool _1373_recOwned;
                  bool _1374_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1375_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out847;
                  bool _out848;
                  bool _out849;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out847, out _out848, out _out849, out _out850);
                  _1372_recursiveGen = _out847;
                  _1373_recOwned = _out848;
                  _1374_recErased = _out849;
                  _1375_recIdents = _out850;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1372_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1373_recOwned;
                  isErased = _1374_recErased;
                  readIdents = _1375_recIdents;
                }
              } else if (_source48.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1376___mcc_h751 = _source48.dtor_args;
                DAST._IType _1377___mcc_h752 = _source48.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1378_recursiveGen;
                  bool _1379_recOwned;
                  bool _1380_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1381_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out851;
                  bool _out852;
                  bool _out853;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out854;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out851, out _out852, out _out853, out _out854);
                  _1378_recursiveGen = _out851;
                  _1379_recOwned = _out852;
                  _1380_recErased = _out853;
                  _1381_recIdents = _out854;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1378_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1379_recOwned;
                  isErased = _1380_recErased;
                  readIdents = _1381_recIdents;
                }
              } else if (_source48.is_Primitive) {
                DAST._IPrimitive _1382___mcc_h755 = _source48.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1383_recursiveGen;
                  bool _1384_recOwned;
                  bool _1385_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1386_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out855;
                  bool _out856;
                  bool _out857;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out858;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out855, out _out856, out _out857, out _out858);
                  _1383_recursiveGen = _out855;
                  _1384_recOwned = _out856;
                  _1385_recErased = _out857;
                  _1386_recIdents = _out858;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1383_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1384_recOwned;
                  isErased = _1385_recErased;
                  readIdents = _1386_recIdents;
                }
              } else if (_source48.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1387___mcc_h757 = _source48.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1388_recursiveGen;
                  bool _1389_recOwned;
                  bool _1390_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1391_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out859;
                  bool _out860;
                  bool _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out859, out _out860, out _out861, out _out862);
                  _1388_recursiveGen = _out859;
                  _1389_recOwned = _out860;
                  _1390_recErased = _out861;
                  _1391_recIdents = _out862;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1388_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1389_recOwned;
                  isErased = _1390_recErased;
                  readIdents = _1391_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1392___mcc_h759 = _source48.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1393_recursiveGen;
                  bool _1394_recOwned;
                  bool _1395_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1396_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out863;
                  bool _out864;
                  bool _out865;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out866;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out863, out _out864, out _out865, out _out866);
                  _1393_recursiveGen = _out863;
                  _1394_recOwned = _out864;
                  _1395_recErased = _out865;
                  _1396_recIdents = _out866;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1393_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1394_recOwned;
                  isErased = _1395_recErased;
                  readIdents = _1396_recIdents;
                }
              }
            } else if (_source26.is_Primitive) {
              DAST._IPrimitive _1397___mcc_h761 = _source26.dtor_Primitive_a0;
              DAST._IPrimitive _source50 = _1397___mcc_h761;
              if (_source50.is_Int) {
                DAST._IType _source51 = _501___mcc_h238;
                if (_source51.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1398___mcc_h765 = _source51.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1399___mcc_h766 = _source51.dtor_typeArgs;
                  DAST._IResolvedType _1400___mcc_h767 = _source51.dtor_resolved;
                  DAST._IResolvedType _source52 = _1400___mcc_h767;
                  if (_source52.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1401___mcc_h771 = _source52.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1402_recursiveGen;
                      bool _1403_recOwned;
                      bool _1404_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1405_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out867;
                      bool _out868;
                      bool _out869;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out870;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out867, out _out868, out _out869, out _out870);
                      _1402_recursiveGen = _out867;
                      _1403_recOwned = _out868;
                      _1404_recErased = _out869;
                      _1405_recIdents = _out870;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1402_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1403_recOwned;
                      isErased = _1404_recErased;
                      readIdents = _1405_recIdents;
                    }
                  } else if (_source52.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1406___mcc_h773 = _source52.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1407_recursiveGen;
                      bool _1408_recOwned;
                      bool _1409_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1410_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out871;
                      bool _out872;
                      bool _out873;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out871, out _out872, out _out873, out _out874);
                      _1407_recursiveGen = _out871;
                      _1408_recOwned = _out872;
                      _1409_recErased = _out873;
                      _1410_recIdents = _out874;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1407_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1408_recOwned;
                      isErased = _1409_recErased;
                      readIdents = _1410_recIdents;
                    }
                  } else {
                    DAST._IType _1411___mcc_h775 = _source52.dtor_Newtype_a0;
                    DAST._IType _1412_b = _1411___mcc_h775;
                    {
                      if (object.Equals(_494_fromTpe, _1412_b)) {
                        Dafny.ISequence<Dafny.Rune> _1413_recursiveGen;
                        bool _1414_recOwned;
                        bool _1415_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1416_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out875;
                        bool _out876;
                        bool _out877;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out878;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out875, out _out876, out _out877, out _out878);
                        _1413_recursiveGen = _out875;
                        _1414_recOwned = _out876;
                        _1415_recErased = _out877;
                        _1416_recIdents = _out878;
                        Dafny.ISequence<Dafny.Rune> _1417_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out879;
                        _out879 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _1417_rhsType = _out879;
                        Dafny.ISequence<Dafny.Rune> _1418_uneraseFn;
                        _1418_uneraseFn = ((_1414_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1417_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1418_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1413_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1414_recOwned;
                        isErased = false;
                        readIdents = _1416_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out880;
                        bool _out881;
                        bool _out882;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1412_b), _1412_b, _493_toTpe), selfIdent, @params, mustOwn, out _out880, out _out881, out _out882, out _out883);
                        s = _out880;
                        isOwned = _out881;
                        isErased = _out882;
                        readIdents = _out883;
                      }
                    }
                  }
                } else if (_source51.is_Nullable) {
                  DAST._IType _1419___mcc_h777 = _source51.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1420_recursiveGen;
                    bool _1421_recOwned;
                    bool _1422_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1423_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out884;
                    bool _out885;
                    bool _out886;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out887;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out884, out _out885, out _out886, out _out887);
                    _1420_recursiveGen = _out884;
                    _1421_recOwned = _out885;
                    _1422_recErased = _out886;
                    _1423_recIdents = _out887;
                    if (!(_1421_recOwned)) {
                      _1420_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1420_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1420_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1422_recErased;
                    readIdents = _1423_recIdents;
                  }
                } else if (_source51.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1424___mcc_h779 = _source51.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1425_recursiveGen;
                    bool _1426_recOwned;
                    bool _1427_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1428_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out888;
                    bool _out889;
                    bool _out890;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out891;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out888, out _out889, out _out890, out _out891);
                    _1425_recursiveGen = _out888;
                    _1426_recOwned = _out889;
                    _1427_recErased = _out890;
                    _1428_recIdents = _out891;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1425_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1426_recOwned;
                    isErased = _1427_recErased;
                    readIdents = _1428_recIdents;
                  }
                } else if (_source51.is_Array) {
                  DAST._IType _1429___mcc_h781 = _source51.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1430_recursiveGen;
                    bool _1431_recOwned;
                    bool _1432_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1433_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out892;
                    bool _out893;
                    bool _out894;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out892, out _out893, out _out894, out _out895);
                    _1430_recursiveGen = _out892;
                    _1431_recOwned = _out893;
                    _1432_recErased = _out894;
                    _1433_recIdents = _out895;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1430_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1431_recOwned;
                    isErased = _1432_recErased;
                    readIdents = _1433_recIdents;
                  }
                } else if (_source51.is_Seq) {
                  DAST._IType _1434___mcc_h783 = _source51.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1435_recursiveGen;
                    bool _1436_recOwned;
                    bool _1437_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1438_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out896;
                    bool _out897;
                    bool _out898;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out899;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out896, out _out897, out _out898, out _out899);
                    _1435_recursiveGen = _out896;
                    _1436_recOwned = _out897;
                    _1437_recErased = _out898;
                    _1438_recIdents = _out899;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1435_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1436_recOwned;
                    isErased = _1437_recErased;
                    readIdents = _1438_recIdents;
                  }
                } else if (_source51.is_Set) {
                  DAST._IType _1439___mcc_h785 = _source51.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1440_recursiveGen;
                    bool _1441_recOwned;
                    bool _1442_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1443_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out900;
                    bool _out901;
                    bool _out902;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out903;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out900, out _out901, out _out902, out _out903);
                    _1440_recursiveGen = _out900;
                    _1441_recOwned = _out901;
                    _1442_recErased = _out902;
                    _1443_recIdents = _out903;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1440_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1441_recOwned;
                    isErased = _1442_recErased;
                    readIdents = _1443_recIdents;
                  }
                } else if (_source51.is_Multiset) {
                  DAST._IType _1444___mcc_h787 = _source51.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1445_recursiveGen;
                    bool _1446_recOwned;
                    bool _1447_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1448_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out904;
                    bool _out905;
                    bool _out906;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out904, out _out905, out _out906, out _out907);
                    _1445_recursiveGen = _out904;
                    _1446_recOwned = _out905;
                    _1447_recErased = _out906;
                    _1448_recIdents = _out907;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1445_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1446_recOwned;
                    isErased = _1447_recErased;
                    readIdents = _1448_recIdents;
                  }
                } else if (_source51.is_Map) {
                  DAST._IType _1449___mcc_h789 = _source51.dtor_key;
                  DAST._IType _1450___mcc_h790 = _source51.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1451_recursiveGen;
                    bool _1452_recOwned;
                    bool _1453_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1454_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out908;
                    bool _out909;
                    bool _out910;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out911;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out908, out _out909, out _out910, out _out911);
                    _1451_recursiveGen = _out908;
                    _1452_recOwned = _out909;
                    _1453_recErased = _out910;
                    _1454_recIdents = _out911;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1451_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1452_recOwned;
                    isErased = _1453_recErased;
                    readIdents = _1454_recIdents;
                  }
                } else if (_source51.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1455___mcc_h793 = _source51.dtor_args;
                  DAST._IType _1456___mcc_h794 = _source51.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1457_recursiveGen;
                    bool _1458_recOwned;
                    bool _1459_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1460_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out912;
                    bool _out913;
                    bool _out914;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out915;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out912, out _out913, out _out914, out _out915);
                    _1457_recursiveGen = _out912;
                    _1458_recOwned = _out913;
                    _1459_recErased = _out914;
                    _1460_recIdents = _out915;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1457_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1458_recOwned;
                    isErased = _1459_recErased;
                    readIdents = _1460_recIdents;
                  }
                } else if (_source51.is_Primitive) {
                  DAST._IPrimitive _1461___mcc_h797 = _source51.dtor_Primitive_a0;
                  DAST._IPrimitive _source53 = _1461___mcc_h797;
                  if (_source53.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1462_recursiveGen;
                      bool _1463_recOwned;
                      bool _1464_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1465_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out916;
                      bool _out917;
                      bool _out918;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out916, out _out917, out _out918, out _out919);
                      _1462_recursiveGen = _out916;
                      _1463_recOwned = _out917;
                      _1464_recErased = _out918;
                      _1465_recIdents = _out919;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1462_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1463_recOwned;
                      isErased = _1464_recErased;
                      readIdents = _1465_recIdents;
                    }
                  } else if (_source53.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1466_recursiveGen;
                      bool _1467___v44;
                      bool _1468___v45;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out920;
                      bool _out921;
                      bool _out922;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out923;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, true, out _out920, out _out921, out _out922, out _out923);
                      _1466_recursiveGen = _out920;
                      _1467___v44 = _out921;
                      _1468___v45 = _out922;
                      _1469_recIdents = _out923;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1466_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1469_recIdents;
                    }
                  } else if (_source53.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1470_recursiveGen;
                      bool _1471_recOwned;
                      bool _1472_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1473_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out924;
                      bool _out925;
                      bool _out926;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out927;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out924, out _out925, out _out926, out _out927);
                      _1470_recursiveGen = _out924;
                      _1471_recOwned = _out925;
                      _1472_recErased = _out926;
                      _1473_recIdents = _out927;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1470_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1471_recOwned;
                      isErased = _1472_recErased;
                      readIdents = _1473_recIdents;
                    }
                  } else if (_source53.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1474_recursiveGen;
                      bool _1475_recOwned;
                      bool _1476_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1477_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out928;
                      bool _out929;
                      bool _out930;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out928, out _out929, out _out930, out _out931);
                      _1474_recursiveGen = _out928;
                      _1475_recOwned = _out929;
                      _1476_recErased = _out930;
                      _1477_recIdents = _out931;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1474_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1475_recOwned;
                      isErased = _1476_recErased;
                      readIdents = _1477_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1478_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out932;
                      _out932 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1478_rhsType = _out932;
                      Dafny.ISequence<Dafny.Rune> _1479_recursiveGen;
                      bool _1480___v54;
                      bool _1481___v55;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1482_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out933;
                      bool _out934;
                      bool _out935;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, true, out _out933, out _out934, out _out935, out _out936);
                      _1479_recursiveGen = _out933;
                      _1480___v54 = _out934;
                      _1481___v55 = _out935;
                      _1482_recIdents = _out936;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1479_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1482_recIdents;
                    }
                  }
                } else if (_source51.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1483___mcc_h799 = _source51.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1484_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out937;
                    _out937 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                    _1484_rhsType = _out937;
                    Dafny.ISequence<Dafny.Rune> _1485_recursiveGen;
                    bool _1486___v49;
                    bool _1487___v50;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1488_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out938;
                    bool _out939;
                    bool _out940;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out941;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, true, out _out938, out _out939, out _out940, out _out941);
                    _1485_recursiveGen = _out938;
                    _1486___v49 = _out939;
                    _1487___v50 = _out940;
                    _1488_recIdents = _out941;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1484_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1485_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1488_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1489___mcc_h801 = _source51.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1490_recursiveGen;
                    bool _1491_recOwned;
                    bool _1492_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1493_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out942;
                    bool _out943;
                    bool _out944;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out942, out _out943, out _out944, out _out945);
                    _1490_recursiveGen = _out942;
                    _1491_recOwned = _out943;
                    _1492_recErased = _out944;
                    _1493_recIdents = _out945;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1490_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1491_recOwned;
                    isErased = _1492_recErased;
                    readIdents = _1493_recIdents;
                  }
                }
              } else if (_source50.is_Real) {
                DAST._IType _source54 = _501___mcc_h238;
                if (_source54.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1494___mcc_h803 = _source54.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1495___mcc_h804 = _source54.dtor_typeArgs;
                  DAST._IResolvedType _1496___mcc_h805 = _source54.dtor_resolved;
                  DAST._IResolvedType _source55 = _1496___mcc_h805;
                  if (_source55.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1497___mcc_h809 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1498_recursiveGen;
                      bool _1499_recOwned;
                      bool _1500_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1501_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out946;
                      bool _out947;
                      bool _out948;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out946, out _out947, out _out948, out _out949);
                      _1498_recursiveGen = _out946;
                      _1499_recOwned = _out947;
                      _1500_recErased = _out948;
                      _1501_recIdents = _out949;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1498_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1499_recOwned;
                      isErased = _1500_recErased;
                      readIdents = _1501_recIdents;
                    }
                  } else if (_source55.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1502___mcc_h811 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1503_recursiveGen;
                      bool _1504_recOwned;
                      bool _1505_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1506_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out950;
                      bool _out951;
                      bool _out952;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out953;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out950, out _out951, out _out952, out _out953);
                      _1503_recursiveGen = _out950;
                      _1504_recOwned = _out951;
                      _1505_recErased = _out952;
                      _1506_recIdents = _out953;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1503_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1504_recOwned;
                      isErased = _1505_recErased;
                      readIdents = _1506_recIdents;
                    }
                  } else {
                    DAST._IType _1507___mcc_h813 = _source55.dtor_Newtype_a0;
                    DAST._IType _1508_b = _1507___mcc_h813;
                    {
                      if (object.Equals(_494_fromTpe, _1508_b)) {
                        Dafny.ISequence<Dafny.Rune> _1509_recursiveGen;
                        bool _1510_recOwned;
                        bool _1511_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1512_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out954;
                        bool _out955;
                        bool _out956;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out954, out _out955, out _out956, out _out957);
                        _1509_recursiveGen = _out954;
                        _1510_recOwned = _out955;
                        _1511_recErased = _out956;
                        _1512_recIdents = _out957;
                        Dafny.ISequence<Dafny.Rune> _1513_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out958;
                        _out958 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _1513_rhsType = _out958;
                        Dafny.ISequence<Dafny.Rune> _1514_uneraseFn;
                        _1514_uneraseFn = ((_1510_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1513_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1514_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1509_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1510_recOwned;
                        isErased = false;
                        readIdents = _1512_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out959;
                        bool _out960;
                        bool _out961;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out962;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1508_b), _1508_b, _493_toTpe), selfIdent, @params, mustOwn, out _out959, out _out960, out _out961, out _out962);
                        s = _out959;
                        isOwned = _out960;
                        isErased = _out961;
                        readIdents = _out962;
                      }
                    }
                  }
                } else if (_source54.is_Nullable) {
                  DAST._IType _1515___mcc_h815 = _source54.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1516_recursiveGen;
                    bool _1517_recOwned;
                    bool _1518_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1519_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out963;
                    bool _out964;
                    bool _out965;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out963, out _out964, out _out965, out _out966);
                    _1516_recursiveGen = _out963;
                    _1517_recOwned = _out964;
                    _1518_recErased = _out965;
                    _1519_recIdents = _out966;
                    if (!(_1517_recOwned)) {
                      _1516_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1516_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1516_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1518_recErased;
                    readIdents = _1519_recIdents;
                  }
                } else if (_source54.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1520___mcc_h817 = _source54.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1521_recursiveGen;
                    bool _1522_recOwned;
                    bool _1523_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1524_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out967;
                    bool _out968;
                    bool _out969;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out970;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out967, out _out968, out _out969, out _out970);
                    _1521_recursiveGen = _out967;
                    _1522_recOwned = _out968;
                    _1523_recErased = _out969;
                    _1524_recIdents = _out970;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1521_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1522_recOwned;
                    isErased = _1523_recErased;
                    readIdents = _1524_recIdents;
                  }
                } else if (_source54.is_Array) {
                  DAST._IType _1525___mcc_h819 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1526_recursiveGen;
                    bool _1527_recOwned;
                    bool _1528_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1529_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out971;
                    bool _out972;
                    bool _out973;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out971, out _out972, out _out973, out _out974);
                    _1526_recursiveGen = _out971;
                    _1527_recOwned = _out972;
                    _1528_recErased = _out973;
                    _1529_recIdents = _out974;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1526_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1527_recOwned;
                    isErased = _1528_recErased;
                    readIdents = _1529_recIdents;
                  }
                } else if (_source54.is_Seq) {
                  DAST._IType _1530___mcc_h821 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1531_recursiveGen;
                    bool _1532_recOwned;
                    bool _1533_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1534_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out975;
                    bool _out976;
                    bool _out977;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out978;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out975, out _out976, out _out977, out _out978);
                    _1531_recursiveGen = _out975;
                    _1532_recOwned = _out976;
                    _1533_recErased = _out977;
                    _1534_recIdents = _out978;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1531_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1532_recOwned;
                    isErased = _1533_recErased;
                    readIdents = _1534_recIdents;
                  }
                } else if (_source54.is_Set) {
                  DAST._IType _1535___mcc_h823 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1536_recursiveGen;
                    bool _1537_recOwned;
                    bool _1538_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1539_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out979;
                    bool _out980;
                    bool _out981;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out979, out _out980, out _out981, out _out982);
                    _1536_recursiveGen = _out979;
                    _1537_recOwned = _out980;
                    _1538_recErased = _out981;
                    _1539_recIdents = _out982;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1536_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1537_recOwned;
                    isErased = _1538_recErased;
                    readIdents = _1539_recIdents;
                  }
                } else if (_source54.is_Multiset) {
                  DAST._IType _1540___mcc_h825 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1541_recursiveGen;
                    bool _1542_recOwned;
                    bool _1543_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1544_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out983;
                    bool _out984;
                    bool _out985;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out986;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out983, out _out984, out _out985, out _out986);
                    _1541_recursiveGen = _out983;
                    _1542_recOwned = _out984;
                    _1543_recErased = _out985;
                    _1544_recIdents = _out986;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1541_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1542_recOwned;
                    isErased = _1543_recErased;
                    readIdents = _1544_recIdents;
                  }
                } else if (_source54.is_Map) {
                  DAST._IType _1545___mcc_h827 = _source54.dtor_key;
                  DAST._IType _1546___mcc_h828 = _source54.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1547_recursiveGen;
                    bool _1548_recOwned;
                    bool _1549_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1550_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out987;
                    bool _out988;
                    bool _out989;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out987, out _out988, out _out989, out _out990);
                    _1547_recursiveGen = _out987;
                    _1548_recOwned = _out988;
                    _1549_recErased = _out989;
                    _1550_recIdents = _out990;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1547_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1548_recOwned;
                    isErased = _1549_recErased;
                    readIdents = _1550_recIdents;
                  }
                } else if (_source54.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1551___mcc_h831 = _source54.dtor_args;
                  DAST._IType _1552___mcc_h832 = _source54.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1553_recursiveGen;
                    bool _1554_recOwned;
                    bool _1555_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1556_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out991;
                    bool _out992;
                    bool _out993;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out994;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out991, out _out992, out _out993, out _out994);
                    _1553_recursiveGen = _out991;
                    _1554_recOwned = _out992;
                    _1555_recErased = _out993;
                    _1556_recIdents = _out994;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1553_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1554_recOwned;
                    isErased = _1555_recErased;
                    readIdents = _1556_recIdents;
                  }
                } else if (_source54.is_Primitive) {
                  DAST._IPrimitive _1557___mcc_h835 = _source54.dtor_Primitive_a0;
                  DAST._IPrimitive _source56 = _1557___mcc_h835;
                  if (_source56.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1558_recursiveGen;
                      bool _1559___v46;
                      bool _1560___v47;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1561_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out995;
                      bool _out996;
                      bool _out997;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out998;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, false, out _out995, out _out996, out _out997, out _out998);
                      _1558_recursiveGen = _out995;
                      _1559___v46 = _out996;
                      _1560___v47 = _out997;
                      _1561_recIdents = _out998;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1558_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1561_recIdents;
                    }
                  } else if (_source56.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1562_recursiveGen;
                      bool _1563_recOwned;
                      bool _1564_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1565_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out999;
                      bool _out1000;
                      bool _out1001;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out999, out _out1000, out _out1001, out _out1002);
                      _1562_recursiveGen = _out999;
                      _1563_recOwned = _out1000;
                      _1564_recErased = _out1001;
                      _1565_recIdents = _out1002;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1562_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1563_recOwned;
                      isErased = _1564_recErased;
                      readIdents = _1565_recIdents;
                    }
                  } else if (_source56.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1566_recursiveGen;
                      bool _1567_recOwned;
                      bool _1568_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1003;
                      bool _out1004;
                      bool _out1005;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1006;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1003, out _out1004, out _out1005, out _out1006);
                      _1566_recursiveGen = _out1003;
                      _1567_recOwned = _out1004;
                      _1568_recErased = _out1005;
                      _1569_recIdents = _out1006;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1566_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1567_recOwned;
                      isErased = _1568_recErased;
                      readIdents = _1569_recIdents;
                    }
                  } else if (_source56.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1570_recursiveGen;
                      bool _1571_recOwned;
                      bool _1572_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1573_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1007;
                      bool _out1008;
                      bool _out1009;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1007, out _out1008, out _out1009, out _out1010);
                      _1570_recursiveGen = _out1007;
                      _1571_recOwned = _out1008;
                      _1572_recErased = _out1009;
                      _1573_recIdents = _out1010;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1570_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1571_recOwned;
                      isErased = _1572_recErased;
                      readIdents = _1573_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1574_recursiveGen;
                      bool _1575_recOwned;
                      bool _1576_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1577_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1011;
                      bool _out1012;
                      bool _out1013;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1011, out _out1012, out _out1013, out _out1014);
                      _1574_recursiveGen = _out1011;
                      _1575_recOwned = _out1012;
                      _1576_recErased = _out1013;
                      _1577_recIdents = _out1014;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1575_recOwned;
                      isErased = _1576_recErased;
                      readIdents = _1577_recIdents;
                    }
                  }
                } else if (_source54.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1578___mcc_h837 = _source54.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1579_recursiveGen;
                    bool _1580_recOwned;
                    bool _1581_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1582_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1015;
                    bool _out1016;
                    bool _out1017;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1018;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1015, out _out1016, out _out1017, out _out1018);
                    _1579_recursiveGen = _out1015;
                    _1580_recOwned = _out1016;
                    _1581_recErased = _out1017;
                    _1582_recIdents = _out1018;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1579_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1580_recOwned;
                    isErased = _1581_recErased;
                    readIdents = _1582_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1583___mcc_h839 = _source54.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1584_recursiveGen;
                    bool _1585_recOwned;
                    bool _1586_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1587_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1019;
                    bool _out1020;
                    bool _out1021;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1019, out _out1020, out _out1021, out _out1022);
                    _1584_recursiveGen = _out1019;
                    _1585_recOwned = _out1020;
                    _1586_recErased = _out1021;
                    _1587_recIdents = _out1022;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1584_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1585_recOwned;
                    isErased = _1586_recErased;
                    readIdents = _1587_recIdents;
                  }
                }
              } else if (_source50.is_String) {
                DAST._IType _source57 = _501___mcc_h238;
                if (_source57.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1588___mcc_h841 = _source57.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1589___mcc_h842 = _source57.dtor_typeArgs;
                  DAST._IResolvedType _1590___mcc_h843 = _source57.dtor_resolved;
                  DAST._IResolvedType _source58 = _1590___mcc_h843;
                  if (_source58.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1591___mcc_h847 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1592_recursiveGen;
                      bool _1593_recOwned;
                      bool _1594_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1595_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1023;
                      bool _out1024;
                      bool _out1025;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1023, out _out1024, out _out1025, out _out1026);
                      _1592_recursiveGen = _out1023;
                      _1593_recOwned = _out1024;
                      _1594_recErased = _out1025;
                      _1595_recIdents = _out1026;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1592_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1593_recOwned;
                      isErased = _1594_recErased;
                      readIdents = _1595_recIdents;
                    }
                  } else if (_source58.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1596___mcc_h849 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1597_recursiveGen;
                      bool _1598_recOwned;
                      bool _1599_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1600_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1027;
                      bool _out1028;
                      bool _out1029;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1030;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1027, out _out1028, out _out1029, out _out1030);
                      _1597_recursiveGen = _out1027;
                      _1598_recOwned = _out1028;
                      _1599_recErased = _out1029;
                      _1600_recIdents = _out1030;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1597_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1598_recOwned;
                      isErased = _1599_recErased;
                      readIdents = _1600_recIdents;
                    }
                  } else {
                    DAST._IType _1601___mcc_h851 = _source58.dtor_Newtype_a0;
                    DAST._IType _1602_b = _1601___mcc_h851;
                    {
                      if (object.Equals(_494_fromTpe, _1602_b)) {
                        Dafny.ISequence<Dafny.Rune> _1603_recursiveGen;
                        bool _1604_recOwned;
                        bool _1605_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1606_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1031;
                        bool _out1032;
                        bool _out1033;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1031, out _out1032, out _out1033, out _out1034);
                        _1603_recursiveGen = _out1031;
                        _1604_recOwned = _out1032;
                        _1605_recErased = _out1033;
                        _1606_recIdents = _out1034;
                        Dafny.ISequence<Dafny.Rune> _1607_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1035;
                        _out1035 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _1607_rhsType = _out1035;
                        Dafny.ISequence<Dafny.Rune> _1608_uneraseFn;
                        _1608_uneraseFn = ((_1604_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1607_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1608_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1603_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1604_recOwned;
                        isErased = false;
                        readIdents = _1606_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1036;
                        bool _out1037;
                        bool _out1038;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1039;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1602_b), _1602_b, _493_toTpe), selfIdent, @params, mustOwn, out _out1036, out _out1037, out _out1038, out _out1039);
                        s = _out1036;
                        isOwned = _out1037;
                        isErased = _out1038;
                        readIdents = _out1039;
                      }
                    }
                  }
                } else if (_source57.is_Nullable) {
                  DAST._IType _1609___mcc_h853 = _source57.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1610_recursiveGen;
                    bool _1611_recOwned;
                    bool _1612_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1040;
                    bool _out1041;
                    bool _out1042;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1040, out _out1041, out _out1042, out _out1043);
                    _1610_recursiveGen = _out1040;
                    _1611_recOwned = _out1041;
                    _1612_recErased = _out1042;
                    _1613_recIdents = _out1043;
                    if (!(_1611_recOwned)) {
                      _1610_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1610_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1610_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1612_recErased;
                    readIdents = _1613_recIdents;
                  }
                } else if (_source57.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1614___mcc_h855 = _source57.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1615_recursiveGen;
                    bool _1616_recOwned;
                    bool _1617_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1618_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1044;
                    bool _out1045;
                    bool _out1046;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1047;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1044, out _out1045, out _out1046, out _out1047);
                    _1615_recursiveGen = _out1044;
                    _1616_recOwned = _out1045;
                    _1617_recErased = _out1046;
                    _1618_recIdents = _out1047;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1615_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1616_recOwned;
                    isErased = _1617_recErased;
                    readIdents = _1618_recIdents;
                  }
                } else if (_source57.is_Array) {
                  DAST._IType _1619___mcc_h857 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1620_recursiveGen;
                    bool _1621_recOwned;
                    bool _1622_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1623_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1048;
                    bool _out1049;
                    bool _out1050;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1051;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1048, out _out1049, out _out1050, out _out1051);
                    _1620_recursiveGen = _out1048;
                    _1621_recOwned = _out1049;
                    _1622_recErased = _out1050;
                    _1623_recIdents = _out1051;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1620_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1621_recOwned;
                    isErased = _1622_recErased;
                    readIdents = _1623_recIdents;
                  }
                } else if (_source57.is_Seq) {
                  DAST._IType _1624___mcc_h859 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1625_recursiveGen;
                    bool _1626_recOwned;
                    bool _1627_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1052;
                    bool _out1053;
                    bool _out1054;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1052, out _out1053, out _out1054, out _out1055);
                    _1625_recursiveGen = _out1052;
                    _1626_recOwned = _out1053;
                    _1627_recErased = _out1054;
                    _1628_recIdents = _out1055;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1625_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1626_recOwned;
                    isErased = _1627_recErased;
                    readIdents = _1628_recIdents;
                  }
                } else if (_source57.is_Set) {
                  DAST._IType _1629___mcc_h861 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1630_recursiveGen;
                    bool _1631_recOwned;
                    bool _1632_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1633_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1056;
                    bool _out1057;
                    bool _out1058;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1059;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1056, out _out1057, out _out1058, out _out1059);
                    _1630_recursiveGen = _out1056;
                    _1631_recOwned = _out1057;
                    _1632_recErased = _out1058;
                    _1633_recIdents = _out1059;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1630_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1631_recOwned;
                    isErased = _1632_recErased;
                    readIdents = _1633_recIdents;
                  }
                } else if (_source57.is_Multiset) {
                  DAST._IType _1634___mcc_h863 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1635_recursiveGen;
                    bool _1636_recOwned;
                    bool _1637_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1638_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1060;
                    bool _out1061;
                    bool _out1062;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1063;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1060, out _out1061, out _out1062, out _out1063);
                    _1635_recursiveGen = _out1060;
                    _1636_recOwned = _out1061;
                    _1637_recErased = _out1062;
                    _1638_recIdents = _out1063;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1635_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1636_recOwned;
                    isErased = _1637_recErased;
                    readIdents = _1638_recIdents;
                  }
                } else if (_source57.is_Map) {
                  DAST._IType _1639___mcc_h865 = _source57.dtor_key;
                  DAST._IType _1640___mcc_h866 = _source57.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1641_recursiveGen;
                    bool _1642_recOwned;
                    bool _1643_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1644_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1064;
                    bool _out1065;
                    bool _out1066;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1064, out _out1065, out _out1066, out _out1067);
                    _1641_recursiveGen = _out1064;
                    _1642_recOwned = _out1065;
                    _1643_recErased = _out1066;
                    _1644_recIdents = _out1067;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1641_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1642_recOwned;
                    isErased = _1643_recErased;
                    readIdents = _1644_recIdents;
                  }
                } else if (_source57.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1645___mcc_h869 = _source57.dtor_args;
                  DAST._IType _1646___mcc_h870 = _source57.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1647_recursiveGen;
                    bool _1648_recOwned;
                    bool _1649_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1650_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1068;
                    bool _out1069;
                    bool _out1070;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1071;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1068, out _out1069, out _out1070, out _out1071);
                    _1647_recursiveGen = _out1068;
                    _1648_recOwned = _out1069;
                    _1649_recErased = _out1070;
                    _1650_recIdents = _out1071;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1647_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1648_recOwned;
                    isErased = _1649_recErased;
                    readIdents = _1650_recIdents;
                  }
                } else if (_source57.is_Primitive) {
                  DAST._IPrimitive _1651___mcc_h873 = _source57.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1652_recursiveGen;
                    bool _1653_recOwned;
                    bool _1654_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1655_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1072;
                    bool _out1073;
                    bool _out1074;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1075;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1072, out _out1073, out _out1074, out _out1075);
                    _1652_recursiveGen = _out1072;
                    _1653_recOwned = _out1073;
                    _1654_recErased = _out1074;
                    _1655_recIdents = _out1075;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1652_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1653_recOwned;
                    isErased = _1654_recErased;
                    readIdents = _1655_recIdents;
                  }
                } else if (_source57.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1656___mcc_h875 = _source57.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1657_recursiveGen;
                    bool _1658_recOwned;
                    bool _1659_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1660_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1076;
                    bool _out1077;
                    bool _out1078;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1076, out _out1077, out _out1078, out _out1079);
                    _1657_recursiveGen = _out1076;
                    _1658_recOwned = _out1077;
                    _1659_recErased = _out1078;
                    _1660_recIdents = _out1079;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1657_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1658_recOwned;
                    isErased = _1659_recErased;
                    readIdents = _1660_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1661___mcc_h877 = _source57.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1662_recursiveGen;
                    bool _1663_recOwned;
                    bool _1664_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1665_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1080;
                    bool _out1081;
                    bool _out1082;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1083;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1080, out _out1081, out _out1082, out _out1083);
                    _1662_recursiveGen = _out1080;
                    _1663_recOwned = _out1081;
                    _1664_recErased = _out1082;
                    _1665_recIdents = _out1083;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1662_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1663_recOwned;
                    isErased = _1664_recErased;
                    readIdents = _1665_recIdents;
                  }
                }
              } else if (_source50.is_Bool) {
                DAST._IType _source59 = _501___mcc_h238;
                if (_source59.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1666___mcc_h879 = _source59.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1667___mcc_h880 = _source59.dtor_typeArgs;
                  DAST._IResolvedType _1668___mcc_h881 = _source59.dtor_resolved;
                  DAST._IResolvedType _source60 = _1668___mcc_h881;
                  if (_source60.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1669___mcc_h885 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1670_recursiveGen;
                      bool _1671_recOwned;
                      bool _1672_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1673_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1084;
                      bool _out1085;
                      bool _out1086;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1087;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1084, out _out1085, out _out1086, out _out1087);
                      _1670_recursiveGen = _out1084;
                      _1671_recOwned = _out1085;
                      _1672_recErased = _out1086;
                      _1673_recIdents = _out1087;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1670_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1671_recOwned;
                      isErased = _1672_recErased;
                      readIdents = _1673_recIdents;
                    }
                  } else if (_source60.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1674___mcc_h887 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1675_recursiveGen;
                      bool _1676_recOwned;
                      bool _1677_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1678_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1088;
                      bool _out1089;
                      bool _out1090;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1088, out _out1089, out _out1090, out _out1091);
                      _1675_recursiveGen = _out1088;
                      _1676_recOwned = _out1089;
                      _1677_recErased = _out1090;
                      _1678_recIdents = _out1091;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1675_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1676_recOwned;
                      isErased = _1677_recErased;
                      readIdents = _1678_recIdents;
                    }
                  } else {
                    DAST._IType _1679___mcc_h889 = _source60.dtor_Newtype_a0;
                    DAST._IType _1680_b = _1679___mcc_h889;
                    {
                      if (object.Equals(_494_fromTpe, _1680_b)) {
                        Dafny.ISequence<Dafny.Rune> _1681_recursiveGen;
                        bool _1682_recOwned;
                        bool _1683_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1684_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1092;
                        bool _out1093;
                        bool _out1094;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1095;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1092, out _out1093, out _out1094, out _out1095);
                        _1681_recursiveGen = _out1092;
                        _1682_recOwned = _out1093;
                        _1683_recErased = _out1094;
                        _1684_recIdents = _out1095;
                        Dafny.ISequence<Dafny.Rune> _1685_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1096;
                        _out1096 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _1685_rhsType = _out1096;
                        Dafny.ISequence<Dafny.Rune> _1686_uneraseFn;
                        _1686_uneraseFn = ((_1682_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1685_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1686_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1681_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1682_recOwned;
                        isErased = false;
                        readIdents = _1684_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1097;
                        bool _out1098;
                        bool _out1099;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1680_b), _1680_b, _493_toTpe), selfIdent, @params, mustOwn, out _out1097, out _out1098, out _out1099, out _out1100);
                        s = _out1097;
                        isOwned = _out1098;
                        isErased = _out1099;
                        readIdents = _out1100;
                      }
                    }
                  }
                } else if (_source59.is_Nullable) {
                  DAST._IType _1687___mcc_h891 = _source59.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1688_recursiveGen;
                    bool _1689_recOwned;
                    bool _1690_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1691_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1101;
                    bool _out1102;
                    bool _out1103;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1104;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1101, out _out1102, out _out1103, out _out1104);
                    _1688_recursiveGen = _out1101;
                    _1689_recOwned = _out1102;
                    _1690_recErased = _out1103;
                    _1691_recIdents = _out1104;
                    if (!(_1689_recOwned)) {
                      _1688_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1688_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1688_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1690_recErased;
                    readIdents = _1691_recIdents;
                  }
                } else if (_source59.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1692___mcc_h893 = _source59.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1693_recursiveGen;
                    bool _1694_recOwned;
                    bool _1695_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1105;
                    bool _out1106;
                    bool _out1107;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1108;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1105, out _out1106, out _out1107, out _out1108);
                    _1693_recursiveGen = _out1105;
                    _1694_recOwned = _out1106;
                    _1695_recErased = _out1107;
                    _1696_recIdents = _out1108;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1693_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1694_recOwned;
                    isErased = _1695_recErased;
                    readIdents = _1696_recIdents;
                  }
                } else if (_source59.is_Array) {
                  DAST._IType _1697___mcc_h895 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1698_recursiveGen;
                    bool _1699_recOwned;
                    bool _1700_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1109;
                    bool _out1110;
                    bool _out1111;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1109, out _out1110, out _out1111, out _out1112);
                    _1698_recursiveGen = _out1109;
                    _1699_recOwned = _out1110;
                    _1700_recErased = _out1111;
                    _1701_recIdents = _out1112;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1698_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1699_recOwned;
                    isErased = _1700_recErased;
                    readIdents = _1701_recIdents;
                  }
                } else if (_source59.is_Seq) {
                  DAST._IType _1702___mcc_h897 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1703_recursiveGen;
                    bool _1704_recOwned;
                    bool _1705_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1706_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1113;
                    bool _out1114;
                    bool _out1115;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1116;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1113, out _out1114, out _out1115, out _out1116);
                    _1703_recursiveGen = _out1113;
                    _1704_recOwned = _out1114;
                    _1705_recErased = _out1115;
                    _1706_recIdents = _out1116;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1703_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1704_recOwned;
                    isErased = _1705_recErased;
                    readIdents = _1706_recIdents;
                  }
                } else if (_source59.is_Set) {
                  DAST._IType _1707___mcc_h899 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1708_recursiveGen;
                    bool _1709_recOwned;
                    bool _1710_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1711_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1117;
                    bool _out1118;
                    bool _out1119;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1120;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1117, out _out1118, out _out1119, out _out1120);
                    _1708_recursiveGen = _out1117;
                    _1709_recOwned = _out1118;
                    _1710_recErased = _out1119;
                    _1711_recIdents = _out1120;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1708_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1709_recOwned;
                    isErased = _1710_recErased;
                    readIdents = _1711_recIdents;
                  }
                } else if (_source59.is_Multiset) {
                  DAST._IType _1712___mcc_h901 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1713_recursiveGen;
                    bool _1714_recOwned;
                    bool _1715_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1716_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1121;
                    bool _out1122;
                    bool _out1123;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1121, out _out1122, out _out1123, out _out1124);
                    _1713_recursiveGen = _out1121;
                    _1714_recOwned = _out1122;
                    _1715_recErased = _out1123;
                    _1716_recIdents = _out1124;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1713_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1714_recOwned;
                    isErased = _1715_recErased;
                    readIdents = _1716_recIdents;
                  }
                } else if (_source59.is_Map) {
                  DAST._IType _1717___mcc_h903 = _source59.dtor_key;
                  DAST._IType _1718___mcc_h904 = _source59.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1719_recursiveGen;
                    bool _1720_recOwned;
                    bool _1721_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1722_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1125;
                    bool _out1126;
                    bool _out1127;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1125, out _out1126, out _out1127, out _out1128);
                    _1719_recursiveGen = _out1125;
                    _1720_recOwned = _out1126;
                    _1721_recErased = _out1127;
                    _1722_recIdents = _out1128;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1719_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1720_recOwned;
                    isErased = _1721_recErased;
                    readIdents = _1722_recIdents;
                  }
                } else if (_source59.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1723___mcc_h907 = _source59.dtor_args;
                  DAST._IType _1724___mcc_h908 = _source59.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1725_recursiveGen;
                    bool _1726_recOwned;
                    bool _1727_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1728_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1129;
                    bool _out1130;
                    bool _out1131;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1132;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1129, out _out1130, out _out1131, out _out1132);
                    _1725_recursiveGen = _out1129;
                    _1726_recOwned = _out1130;
                    _1727_recErased = _out1131;
                    _1728_recIdents = _out1132;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1725_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1726_recOwned;
                    isErased = _1727_recErased;
                    readIdents = _1728_recIdents;
                  }
                } else if (_source59.is_Primitive) {
                  DAST._IPrimitive _1729___mcc_h911 = _source59.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1730_recursiveGen;
                    bool _1731_recOwned;
                    bool _1732_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1733_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1133;
                    bool _out1134;
                    bool _out1135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1133, out _out1134, out _out1135, out _out1136);
                    _1730_recursiveGen = _out1133;
                    _1731_recOwned = _out1134;
                    _1732_recErased = _out1135;
                    _1733_recIdents = _out1136;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1730_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1731_recOwned;
                    isErased = _1732_recErased;
                    readIdents = _1733_recIdents;
                  }
                } else if (_source59.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1734___mcc_h913 = _source59.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1735_recursiveGen;
                    bool _1736_recOwned;
                    bool _1737_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1738_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1137;
                    bool _out1138;
                    bool _out1139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1140;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1137, out _out1138, out _out1139, out _out1140);
                    _1735_recursiveGen = _out1137;
                    _1736_recOwned = _out1138;
                    _1737_recErased = _out1139;
                    _1738_recIdents = _out1140;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1735_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1736_recOwned;
                    isErased = _1737_recErased;
                    readIdents = _1738_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1739___mcc_h915 = _source59.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1740_recursiveGen;
                    bool _1741_recOwned;
                    bool _1742_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1743_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1141;
                    bool _out1142;
                    bool _out1143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1144;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1141, out _out1142, out _out1143, out _out1144);
                    _1740_recursiveGen = _out1141;
                    _1741_recOwned = _out1142;
                    _1742_recErased = _out1143;
                    _1743_recIdents = _out1144;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1740_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1741_recOwned;
                    isErased = _1742_recErased;
                    readIdents = _1743_recIdents;
                  }
                }
              } else {
                DAST._IType _source61 = _501___mcc_h238;
                if (_source61.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1744___mcc_h917 = _source61.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1745___mcc_h918 = _source61.dtor_typeArgs;
                  DAST._IResolvedType _1746___mcc_h919 = _source61.dtor_resolved;
                  DAST._IResolvedType _source62 = _1746___mcc_h919;
                  if (_source62.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1747___mcc_h923 = _source62.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1748_recursiveGen;
                      bool _1749_recOwned;
                      bool _1750_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1751_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1145;
                      bool _out1146;
                      bool _out1147;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1145, out _out1146, out _out1147, out _out1148);
                      _1748_recursiveGen = _out1145;
                      _1749_recOwned = _out1146;
                      _1750_recErased = _out1147;
                      _1751_recIdents = _out1148;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1748_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1749_recOwned;
                      isErased = _1750_recErased;
                      readIdents = _1751_recIdents;
                    }
                  } else if (_source62.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1752___mcc_h925 = _source62.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1753_recursiveGen;
                      bool _1754_recOwned;
                      bool _1755_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1756_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1149;
                      bool _out1150;
                      bool _out1151;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1152;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1149, out _out1150, out _out1151, out _out1152);
                      _1753_recursiveGen = _out1149;
                      _1754_recOwned = _out1150;
                      _1755_recErased = _out1151;
                      _1756_recIdents = _out1152;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1753_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1754_recOwned;
                      isErased = _1755_recErased;
                      readIdents = _1756_recIdents;
                    }
                  } else {
                    DAST._IType _1757___mcc_h927 = _source62.dtor_Newtype_a0;
                    DAST._IType _1758_b = _1757___mcc_h927;
                    {
                      if (object.Equals(_494_fromTpe, _1758_b)) {
                        Dafny.ISequence<Dafny.Rune> _1759_recursiveGen;
                        bool _1760_recOwned;
                        bool _1761_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1762_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1153;
                        bool _out1154;
                        bool _out1155;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1156;
                        DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1153, out _out1154, out _out1155, out _out1156);
                        _1759_recursiveGen = _out1153;
                        _1760_recOwned = _out1154;
                        _1761_recErased = _out1155;
                        _1762_recIdents = _out1156;
                        Dafny.ISequence<Dafny.Rune> _1763_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1157;
                        _out1157 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                        _1763_rhsType = _out1157;
                        Dafny.ISequence<Dafny.Rune> _1764_uneraseFn;
                        _1764_uneraseFn = ((_1760_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1763_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1764_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1759_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1760_recOwned;
                        isErased = false;
                        readIdents = _1762_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1158;
                        bool _out1159;
                        bool _out1160;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1161;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1758_b), _1758_b, _493_toTpe), selfIdent, @params, mustOwn, out _out1158, out _out1159, out _out1160, out _out1161);
                        s = _out1158;
                        isOwned = _out1159;
                        isErased = _out1160;
                        readIdents = _out1161;
                      }
                    }
                  }
                } else if (_source61.is_Nullable) {
                  DAST._IType _1765___mcc_h929 = _source61.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1766_recursiveGen;
                    bool _1767_recOwned;
                    bool _1768_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1769_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1162;
                    bool _out1163;
                    bool _out1164;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1165;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1162, out _out1163, out _out1164, out _out1165);
                    _1766_recursiveGen = _out1162;
                    _1767_recOwned = _out1163;
                    _1768_recErased = _out1164;
                    _1769_recIdents = _out1165;
                    if (!(_1767_recOwned)) {
                      _1766_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1766_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1766_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1768_recErased;
                    readIdents = _1769_recIdents;
                  }
                } else if (_source61.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1770___mcc_h931 = _source61.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1771_recursiveGen;
                    bool _1772_recOwned;
                    bool _1773_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1774_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1166;
                    bool _out1167;
                    bool _out1168;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1166, out _out1167, out _out1168, out _out1169);
                    _1771_recursiveGen = _out1166;
                    _1772_recOwned = _out1167;
                    _1773_recErased = _out1168;
                    _1774_recIdents = _out1169;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1771_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1772_recOwned;
                    isErased = _1773_recErased;
                    readIdents = _1774_recIdents;
                  }
                } else if (_source61.is_Array) {
                  DAST._IType _1775___mcc_h933 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1776_recursiveGen;
                    bool _1777_recOwned;
                    bool _1778_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1779_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1170;
                    bool _out1171;
                    bool _out1172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1173;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1170, out _out1171, out _out1172, out _out1173);
                    _1776_recursiveGen = _out1170;
                    _1777_recOwned = _out1171;
                    _1778_recErased = _out1172;
                    _1779_recIdents = _out1173;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1776_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1777_recOwned;
                    isErased = _1778_recErased;
                    readIdents = _1779_recIdents;
                  }
                } else if (_source61.is_Seq) {
                  DAST._IType _1780___mcc_h935 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1781_recursiveGen;
                    bool _1782_recOwned;
                    bool _1783_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1784_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1174;
                    bool _out1175;
                    bool _out1176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1177;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1174, out _out1175, out _out1176, out _out1177);
                    _1781_recursiveGen = _out1174;
                    _1782_recOwned = _out1175;
                    _1783_recErased = _out1176;
                    _1784_recIdents = _out1177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1781_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1782_recOwned;
                    isErased = _1783_recErased;
                    readIdents = _1784_recIdents;
                  }
                } else if (_source61.is_Set) {
                  DAST._IType _1785___mcc_h937 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1786_recursiveGen;
                    bool _1787_recOwned;
                    bool _1788_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1789_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1178;
                    bool _out1179;
                    bool _out1180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1178, out _out1179, out _out1180, out _out1181);
                    _1786_recursiveGen = _out1178;
                    _1787_recOwned = _out1179;
                    _1788_recErased = _out1180;
                    _1789_recIdents = _out1181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1786_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1787_recOwned;
                    isErased = _1788_recErased;
                    readIdents = _1789_recIdents;
                  }
                } else if (_source61.is_Multiset) {
                  DAST._IType _1790___mcc_h939 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1791_recursiveGen;
                    bool _1792_recOwned;
                    bool _1793_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1794_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1182;
                    bool _out1183;
                    bool _out1184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1185;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1182, out _out1183, out _out1184, out _out1185);
                    _1791_recursiveGen = _out1182;
                    _1792_recOwned = _out1183;
                    _1793_recErased = _out1184;
                    _1794_recIdents = _out1185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1791_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1792_recOwned;
                    isErased = _1793_recErased;
                    readIdents = _1794_recIdents;
                  }
                } else if (_source61.is_Map) {
                  DAST._IType _1795___mcc_h941 = _source61.dtor_key;
                  DAST._IType _1796___mcc_h942 = _source61.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1797_recursiveGen;
                    bool _1798_recOwned;
                    bool _1799_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1800_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1186;
                    bool _out1187;
                    bool _out1188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1189;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1186, out _out1187, out _out1188, out _out1189);
                    _1797_recursiveGen = _out1186;
                    _1798_recOwned = _out1187;
                    _1799_recErased = _out1188;
                    _1800_recIdents = _out1189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1797_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1798_recOwned;
                    isErased = _1799_recErased;
                    readIdents = _1800_recIdents;
                  }
                } else if (_source61.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1801___mcc_h945 = _source61.dtor_args;
                  DAST._IType _1802___mcc_h946 = _source61.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1803_recursiveGen;
                    bool _1804_recOwned;
                    bool _1805_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1806_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1190;
                    bool _out1191;
                    bool _out1192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1190, out _out1191, out _out1192, out _out1193);
                    _1803_recursiveGen = _out1190;
                    _1804_recOwned = _out1191;
                    _1805_recErased = _out1192;
                    _1806_recIdents = _out1193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1803_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1804_recOwned;
                    isErased = _1805_recErased;
                    readIdents = _1806_recIdents;
                  }
                } else if (_source61.is_Primitive) {
                  DAST._IPrimitive _1807___mcc_h949 = _source61.dtor_Primitive_a0;
                  DAST._IPrimitive _source63 = _1807___mcc_h949;
                  if (_source63.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1808_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1194;
                      _out1194 = DCOMP.COMP.GenType(_494_fromTpe, true, false);
                      _1808_rhsType = _out1194;
                      Dafny.ISequence<Dafny.Rune> _1809_recursiveGen;
                      bool _1810___v56;
                      bool _1811___v57;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1812_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1195;
                      bool _out1196;
                      bool _out1197;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1198;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, true, out _out1195, out _out1196, out _out1197, out _out1198);
                      _1809_recursiveGen = _out1195;
                      _1810___v56 = _out1196;
                      _1811___v57 = _out1197;
                      _1812_recIdents = _out1198;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1809_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1812_recIdents;
                    }
                  } else if (_source63.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1813_recursiveGen;
                      bool _1814_recOwned;
                      bool _1815_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1816_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1199;
                      bool _out1200;
                      bool _out1201;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1199, out _out1200, out _out1201, out _out1202);
                      _1813_recursiveGen = _out1199;
                      _1814_recOwned = _out1200;
                      _1815_recErased = _out1201;
                      _1816_recIdents = _out1202;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1813_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1814_recOwned;
                      isErased = _1815_recErased;
                      readIdents = _1816_recIdents;
                    }
                  } else if (_source63.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1817_recursiveGen;
                      bool _1818_recOwned;
                      bool _1819_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1203;
                      bool _out1204;
                      bool _out1205;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1206;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1203, out _out1204, out _out1205, out _out1206);
                      _1817_recursiveGen = _out1203;
                      _1818_recOwned = _out1204;
                      _1819_recErased = _out1205;
                      _1820_recIdents = _out1206;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1817_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1818_recOwned;
                      isErased = _1819_recErased;
                      readIdents = _1820_recIdents;
                    }
                  } else if (_source63.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1821_recursiveGen;
                      bool _1822_recOwned;
                      bool _1823_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1824_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1207;
                      bool _out1208;
                      bool _out1209;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1210;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1207, out _out1208, out _out1209, out _out1210);
                      _1821_recursiveGen = _out1207;
                      _1822_recOwned = _out1208;
                      _1823_recErased = _out1209;
                      _1824_recIdents = _out1210;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1821_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1822_recOwned;
                      isErased = _1823_recErased;
                      readIdents = _1824_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1825_recursiveGen;
                      bool _1826_recOwned;
                      bool _1827_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1828_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1211;
                      bool _out1212;
                      bool _out1213;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1211, out _out1212, out _out1213, out _out1214);
                      _1825_recursiveGen = _out1211;
                      _1826_recOwned = _out1212;
                      _1827_recErased = _out1213;
                      _1828_recIdents = _out1214;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1825_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1826_recOwned;
                      isErased = _1827_recErased;
                      readIdents = _1828_recIdents;
                    }
                  }
                } else if (_source61.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1829___mcc_h951 = _source61.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1830_recursiveGen;
                    bool _1831_recOwned;
                    bool _1832_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1833_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1215;
                    bool _out1216;
                    bool _out1217;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1218;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1215, out _out1216, out _out1217, out _out1218);
                    _1830_recursiveGen = _out1215;
                    _1831_recOwned = _out1216;
                    _1832_recErased = _out1217;
                    _1833_recIdents = _out1218;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1830_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1831_recOwned;
                    isErased = _1832_recErased;
                    readIdents = _1833_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1834___mcc_h953 = _source61.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1835_recursiveGen;
                    bool _1836_recOwned;
                    bool _1837_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1838_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1219;
                    bool _out1220;
                    bool _out1221;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1222;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1219, out _out1220, out _out1221, out _out1222);
                    _1835_recursiveGen = _out1219;
                    _1836_recOwned = _out1220;
                    _1837_recErased = _out1221;
                    _1838_recIdents = _out1222;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1835_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1836_recOwned;
                    isErased = _1837_recErased;
                    readIdents = _1838_recIdents;
                  }
                }
              }
            } else if (_source26.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1839___mcc_h955 = _source26.dtor_Passthrough_a0;
              DAST._IType _source64 = _501___mcc_h238;
              if (_source64.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1840___mcc_h959 = _source64.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1841___mcc_h960 = _source64.dtor_typeArgs;
                DAST._IResolvedType _1842___mcc_h961 = _source64.dtor_resolved;
                DAST._IResolvedType _source65 = _1842___mcc_h961;
                if (_source65.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1843___mcc_h965 = _source65.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1844_recursiveGen;
                    bool _1845_recOwned;
                    bool _1846_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1847_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1223;
                    bool _out1224;
                    bool _out1225;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1223, out _out1224, out _out1225, out _out1226);
                    _1844_recursiveGen = _out1223;
                    _1845_recOwned = _out1224;
                    _1846_recErased = _out1225;
                    _1847_recIdents = _out1226;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1844_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1845_recOwned;
                    isErased = _1846_recErased;
                    readIdents = _1847_recIdents;
                  }
                } else if (_source65.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1848___mcc_h967 = _source65.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1849_recursiveGen;
                    bool _1850_recOwned;
                    bool _1851_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1852_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1227;
                    bool _out1228;
                    bool _out1229;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1230;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1227, out _out1228, out _out1229, out _out1230);
                    _1849_recursiveGen = _out1227;
                    _1850_recOwned = _out1228;
                    _1851_recErased = _out1229;
                    _1852_recIdents = _out1230;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1849_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1850_recOwned;
                    isErased = _1851_recErased;
                    readIdents = _1852_recIdents;
                  }
                } else {
                  DAST._IType _1853___mcc_h969 = _source65.dtor_Newtype_a0;
                  DAST._IType _1854_b = _1853___mcc_h969;
                  {
                    if (object.Equals(_494_fromTpe, _1854_b)) {
                      Dafny.ISequence<Dafny.Rune> _1855_recursiveGen;
                      bool _1856_recOwned;
                      bool _1857_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1858_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1231;
                      bool _out1232;
                      bool _out1233;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1234;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1231, out _out1232, out _out1233, out _out1234);
                      _1855_recursiveGen = _out1231;
                      _1856_recOwned = _out1232;
                      _1857_recErased = _out1233;
                      _1858_recIdents = _out1234;
                      Dafny.ISequence<Dafny.Rune> _1859_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1235;
                      _out1235 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1859_rhsType = _out1235;
                      Dafny.ISequence<Dafny.Rune> _1860_uneraseFn;
                      _1860_uneraseFn = ((_1856_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1859_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1860_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1855_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1856_recOwned;
                      isErased = false;
                      readIdents = _1858_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1236;
                      bool _out1237;
                      bool _out1238;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1239;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1854_b), _1854_b, _493_toTpe), selfIdent, @params, mustOwn, out _out1236, out _out1237, out _out1238, out _out1239);
                      s = _out1236;
                      isOwned = _out1237;
                      isErased = _out1238;
                      readIdents = _out1239;
                    }
                  }
                }
              } else if (_source64.is_Nullable) {
                DAST._IType _1861___mcc_h971 = _source64.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1862_recursiveGen;
                  bool _1863_recOwned;
                  bool _1864_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1240;
                  bool _out1241;
                  bool _out1242;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1240, out _out1241, out _out1242, out _out1243);
                  _1862_recursiveGen = _out1240;
                  _1863_recOwned = _out1241;
                  _1864_recErased = _out1242;
                  _1865_recIdents = _out1243;
                  if (!(_1863_recOwned)) {
                    _1862_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1862_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1862_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1864_recErased;
                  readIdents = _1865_recIdents;
                }
              } else if (_source64.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1866___mcc_h973 = _source64.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1867_recursiveGen;
                  bool _1868_recOwned;
                  bool _1869_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1870_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1244;
                  bool _out1245;
                  bool _out1246;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1244, out _out1245, out _out1246, out _out1247);
                  _1867_recursiveGen = _out1244;
                  _1868_recOwned = _out1245;
                  _1869_recErased = _out1246;
                  _1870_recIdents = _out1247;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1867_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1868_recOwned;
                  isErased = _1869_recErased;
                  readIdents = _1870_recIdents;
                }
              } else if (_source64.is_Array) {
                DAST._IType _1871___mcc_h975 = _source64.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1872_recursiveGen;
                  bool _1873_recOwned;
                  bool _1874_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1875_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1248;
                  bool _out1249;
                  bool _out1250;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1248, out _out1249, out _out1250, out _out1251);
                  _1872_recursiveGen = _out1248;
                  _1873_recOwned = _out1249;
                  _1874_recErased = _out1250;
                  _1875_recIdents = _out1251;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1872_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1873_recOwned;
                  isErased = _1874_recErased;
                  readIdents = _1875_recIdents;
                }
              } else if (_source64.is_Seq) {
                DAST._IType _1876___mcc_h977 = _source64.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1877_recursiveGen;
                  bool _1878_recOwned;
                  bool _1879_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1880_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1252;
                  bool _out1253;
                  bool _out1254;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1255;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1252, out _out1253, out _out1254, out _out1255);
                  _1877_recursiveGen = _out1252;
                  _1878_recOwned = _out1253;
                  _1879_recErased = _out1254;
                  _1880_recIdents = _out1255;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1877_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1878_recOwned;
                  isErased = _1879_recErased;
                  readIdents = _1880_recIdents;
                }
              } else if (_source64.is_Set) {
                DAST._IType _1881___mcc_h979 = _source64.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1882_recursiveGen;
                  bool _1883_recOwned;
                  bool _1884_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1885_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1256;
                  bool _out1257;
                  bool _out1258;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1256, out _out1257, out _out1258, out _out1259);
                  _1882_recursiveGen = _out1256;
                  _1883_recOwned = _out1257;
                  _1884_recErased = _out1258;
                  _1885_recIdents = _out1259;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1882_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1883_recOwned;
                  isErased = _1884_recErased;
                  readIdents = _1885_recIdents;
                }
              } else if (_source64.is_Multiset) {
                DAST._IType _1886___mcc_h981 = _source64.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1887_recursiveGen;
                  bool _1888_recOwned;
                  bool _1889_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1890_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1260;
                  bool _out1261;
                  bool _out1262;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1263;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1260, out _out1261, out _out1262, out _out1263);
                  _1887_recursiveGen = _out1260;
                  _1888_recOwned = _out1261;
                  _1889_recErased = _out1262;
                  _1890_recIdents = _out1263;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1887_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1888_recOwned;
                  isErased = _1889_recErased;
                  readIdents = _1890_recIdents;
                }
              } else if (_source64.is_Map) {
                DAST._IType _1891___mcc_h983 = _source64.dtor_key;
                DAST._IType _1892___mcc_h984 = _source64.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1893_recursiveGen;
                  bool _1894_recOwned;
                  bool _1895_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1896_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1264;
                  bool _out1265;
                  bool _out1266;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1267;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1264, out _out1265, out _out1266, out _out1267);
                  _1893_recursiveGen = _out1264;
                  _1894_recOwned = _out1265;
                  _1895_recErased = _out1266;
                  _1896_recIdents = _out1267;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1893_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1894_recOwned;
                  isErased = _1895_recErased;
                  readIdents = _1896_recIdents;
                }
              } else if (_source64.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1897___mcc_h987 = _source64.dtor_args;
                DAST._IType _1898___mcc_h988 = _source64.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1899_recursiveGen;
                  bool _1900_recOwned;
                  bool _1901_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1268;
                  bool _out1269;
                  bool _out1270;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1268, out _out1269, out _out1270, out _out1271);
                  _1899_recursiveGen = _out1268;
                  _1900_recOwned = _out1269;
                  _1901_recErased = _out1270;
                  _1902_recIdents = _out1271;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1899_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1900_recOwned;
                  isErased = _1901_recErased;
                  readIdents = _1902_recIdents;
                }
              } else if (_source64.is_Primitive) {
                DAST._IPrimitive _1903___mcc_h991 = _source64.dtor_Primitive_a0;
                DAST._IPrimitive _source66 = _1903___mcc_h991;
                if (_source66.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1904_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1272;
                    _out1272 = DCOMP.COMP.GenType(_494_fromTpe, true, false);
                    _1904_rhsType = _out1272;
                    Dafny.ISequence<Dafny.Rune> _1905_recursiveGen;
                    bool _1906___v52;
                    bool _1907___v53;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1908_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1273;
                    bool _out1274;
                    bool _out1275;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1276;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, true, out _out1273, out _out1274, out _out1275, out _out1276);
                    _1905_recursiveGen = _out1273;
                    _1906___v52 = _out1274;
                    _1907___v53 = _out1275;
                    _1908_recIdents = _out1276;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1905_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1908_recIdents;
                  }
                } else if (_source66.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1909_recursiveGen;
                    bool _1910_recOwned;
                    bool _1911_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1912_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1277;
                    bool _out1278;
                    bool _out1279;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1277, out _out1278, out _out1279, out _out1280);
                    _1909_recursiveGen = _out1277;
                    _1910_recOwned = _out1278;
                    _1911_recErased = _out1279;
                    _1912_recIdents = _out1280;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1909_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1910_recOwned;
                    isErased = _1911_recErased;
                    readIdents = _1912_recIdents;
                  }
                } else if (_source66.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1913_recursiveGen;
                    bool _1914_recOwned;
                    bool _1915_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1281;
                    bool _out1282;
                    bool _out1283;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1281, out _out1282, out _out1283, out _out1284);
                    _1913_recursiveGen = _out1281;
                    _1914_recOwned = _out1282;
                    _1915_recErased = _out1283;
                    _1916_recIdents = _out1284;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1913_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1914_recOwned;
                    isErased = _1915_recErased;
                    readIdents = _1916_recIdents;
                  }
                } else if (_source66.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1917_recursiveGen;
                    bool _1918_recOwned;
                    bool _1919_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1920_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1285;
                    bool _out1286;
                    bool _out1287;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1288;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1285, out _out1286, out _out1287, out _out1288);
                    _1917_recursiveGen = _out1285;
                    _1918_recOwned = _out1286;
                    _1919_recErased = _out1287;
                    _1920_recIdents = _out1288;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1917_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1918_recOwned;
                    isErased = _1919_recErased;
                    readIdents = _1920_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _1921_recursiveGen;
                    bool _1922_recOwned;
                    bool _1923_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1924_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1289;
                    bool _out1290;
                    bool _out1291;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1289, out _out1290, out _out1291, out _out1292);
                    _1921_recursiveGen = _out1289;
                    _1922_recOwned = _out1290;
                    _1923_recErased = _out1291;
                    _1924_recIdents = _out1292;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1921_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1922_recOwned;
                    isErased = _1923_recErased;
                    readIdents = _1924_recIdents;
                  }
                }
              } else if (_source64.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1925___mcc_h993 = _source64.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1926_recursiveGen;
                  bool _1927___v60;
                  bool _1928___v61;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1929_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1293;
                  bool _out1294;
                  bool _out1295;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1296;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, true, out _out1293, out _out1294, out _out1295, out _out1296);
                  _1926_recursiveGen = _out1293;
                  _1927___v60 = _out1294;
                  _1928___v61 = _out1295;
                  _1929_recIdents = _out1296;
                  Dafny.ISequence<Dafny.Rune> _1930_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1297;
                  _out1297 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                  _1930_toTpeGen = _out1297;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _1926_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _1930_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _1929_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1931___mcc_h995 = _source64.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1932_recursiveGen;
                  bool _1933_recOwned;
                  bool _1934_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1935_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1298;
                  bool _out1299;
                  bool _out1300;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1298, out _out1299, out _out1300, out _out1301);
                  _1932_recursiveGen = _out1298;
                  _1933_recOwned = _out1299;
                  _1934_recErased = _out1300;
                  _1935_recIdents = _out1301;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1932_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1933_recOwned;
                  isErased = _1934_recErased;
                  readIdents = _1935_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _1936___mcc_h997 = _source26.dtor_TypeArg_a0;
              DAST._IType _source67 = _501___mcc_h238;
              if (_source67.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1937___mcc_h1001 = _source67.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1938___mcc_h1002 = _source67.dtor_typeArgs;
                DAST._IResolvedType _1939___mcc_h1003 = _source67.dtor_resolved;
                DAST._IResolvedType _source68 = _1939___mcc_h1003;
                if (_source68.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1940___mcc_h1007 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1941_recursiveGen;
                    bool _1942_recOwned;
                    bool _1943_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1302;
                    bool _out1303;
                    bool _out1304;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1302, out _out1303, out _out1304, out _out1305);
                    _1941_recursiveGen = _out1302;
                    _1942_recOwned = _out1303;
                    _1943_recErased = _out1304;
                    _1944_recIdents = _out1305;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1941_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1942_recOwned;
                    isErased = _1943_recErased;
                    readIdents = _1944_recIdents;
                  }
                } else if (_source68.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1945___mcc_h1009 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1946_recursiveGen;
                    bool _1947_recOwned;
                    bool _1948_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1306;
                    bool _out1307;
                    bool _out1308;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1309;
                    DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1306, out _out1307, out _out1308, out _out1309);
                    _1946_recursiveGen = _out1306;
                    _1947_recOwned = _out1307;
                    _1948_recErased = _out1308;
                    _1949_recIdents = _out1309;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1946_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1947_recOwned;
                    isErased = _1948_recErased;
                    readIdents = _1949_recIdents;
                  }
                } else {
                  DAST._IType _1950___mcc_h1011 = _source68.dtor_Newtype_a0;
                  DAST._IType _1951_b = _1950___mcc_h1011;
                  {
                    if (object.Equals(_494_fromTpe, _1951_b)) {
                      Dafny.ISequence<Dafny.Rune> _1952_recursiveGen;
                      bool _1953_recOwned;
                      bool _1954_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1955_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1310;
                      bool _out1311;
                      bool _out1312;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
                      DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1310, out _out1311, out _out1312, out _out1313);
                      _1952_recursiveGen = _out1310;
                      _1953_recOwned = _out1311;
                      _1954_recErased = _out1312;
                      _1955_recIdents = _out1313;
                      Dafny.ISequence<Dafny.Rune> _1956_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1314;
                      _out1314 = DCOMP.COMP.GenType(_493_toTpe, true, false);
                      _1956_rhsType = _out1314;
                      Dafny.ISequence<Dafny.Rune> _1957_uneraseFn;
                      _1957_uneraseFn = ((_1953_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1956_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1957_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1952_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1953_recOwned;
                      isErased = false;
                      readIdents = _1955_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1315;
                      bool _out1316;
                      bool _out1317;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1318;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_495_expr, _494_fromTpe, _1951_b), _1951_b, _493_toTpe), selfIdent, @params, mustOwn, out _out1315, out _out1316, out _out1317, out _out1318);
                      s = _out1315;
                      isOwned = _out1316;
                      isErased = _out1317;
                      readIdents = _out1318;
                    }
                  }
                }
              } else if (_source67.is_Nullable) {
                DAST._IType _1958___mcc_h1013 = _source67.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1959_recursiveGen;
                  bool _1960_recOwned;
                  bool _1961_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1962_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1319;
                  bool _out1320;
                  bool _out1321;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1319, out _out1320, out _out1321, out _out1322);
                  _1959_recursiveGen = _out1319;
                  _1960_recOwned = _out1320;
                  _1961_recErased = _out1321;
                  _1962_recIdents = _out1322;
                  if (!(_1960_recOwned)) {
                    _1959_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1959_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1959_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1961_recErased;
                  readIdents = _1962_recIdents;
                }
              } else if (_source67.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1963___mcc_h1015 = _source67.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1964_recursiveGen;
                  bool _1965_recOwned;
                  bool _1966_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1967_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1323;
                  bool _out1324;
                  bool _out1325;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1323, out _out1324, out _out1325, out _out1326);
                  _1964_recursiveGen = _out1323;
                  _1965_recOwned = _out1324;
                  _1966_recErased = _out1325;
                  _1967_recIdents = _out1326;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1964_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1965_recOwned;
                  isErased = _1966_recErased;
                  readIdents = _1967_recIdents;
                }
              } else if (_source67.is_Array) {
                DAST._IType _1968___mcc_h1017 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1969_recursiveGen;
                  bool _1970_recOwned;
                  bool _1971_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1327;
                  bool _out1328;
                  bool _out1329;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1330;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1327, out _out1328, out _out1329, out _out1330);
                  _1969_recursiveGen = _out1327;
                  _1970_recOwned = _out1328;
                  _1971_recErased = _out1329;
                  _1972_recIdents = _out1330;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1969_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1970_recOwned;
                  isErased = _1971_recErased;
                  readIdents = _1972_recIdents;
                }
              } else if (_source67.is_Seq) {
                DAST._IType _1973___mcc_h1019 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1974_recursiveGen;
                  bool _1975_recOwned;
                  bool _1976_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1977_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1331;
                  bool _out1332;
                  bool _out1333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1331, out _out1332, out _out1333, out _out1334);
                  _1974_recursiveGen = _out1331;
                  _1975_recOwned = _out1332;
                  _1976_recErased = _out1333;
                  _1977_recIdents = _out1334;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1974_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1975_recOwned;
                  isErased = _1976_recErased;
                  readIdents = _1977_recIdents;
                }
              } else if (_source67.is_Set) {
                DAST._IType _1978___mcc_h1021 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1979_recursiveGen;
                  bool _1980_recOwned;
                  bool _1981_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1982_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1335;
                  bool _out1336;
                  bool _out1337;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1335, out _out1336, out _out1337, out _out1338);
                  _1979_recursiveGen = _out1335;
                  _1980_recOwned = _out1336;
                  _1981_recErased = _out1337;
                  _1982_recIdents = _out1338;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1979_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1980_recOwned;
                  isErased = _1981_recErased;
                  readIdents = _1982_recIdents;
                }
              } else if (_source67.is_Multiset) {
                DAST._IType _1983___mcc_h1023 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1984_recursiveGen;
                  bool _1985_recOwned;
                  bool _1986_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1339;
                  bool _out1340;
                  bool _out1341;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1342;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1339, out _out1340, out _out1341, out _out1342);
                  _1984_recursiveGen = _out1339;
                  _1985_recOwned = _out1340;
                  _1986_recErased = _out1341;
                  _1987_recIdents = _out1342;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1984_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1985_recOwned;
                  isErased = _1986_recErased;
                  readIdents = _1987_recIdents;
                }
              } else if (_source67.is_Map) {
                DAST._IType _1988___mcc_h1025 = _source67.dtor_key;
                DAST._IType _1989___mcc_h1026 = _source67.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1990_recursiveGen;
                  bool _1991_recOwned;
                  bool _1992_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1993_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1343;
                  bool _out1344;
                  bool _out1345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1346;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1343, out _out1344, out _out1345, out _out1346);
                  _1990_recursiveGen = _out1343;
                  _1991_recOwned = _out1344;
                  _1992_recErased = _out1345;
                  _1993_recIdents = _out1346;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1990_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1991_recOwned;
                  isErased = _1992_recErased;
                  readIdents = _1993_recIdents;
                }
              } else if (_source67.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1994___mcc_h1029 = _source67.dtor_args;
                DAST._IType _1995___mcc_h1030 = _source67.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1996_recursiveGen;
                  bool _1997_recOwned;
                  bool _1998_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1999_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1347;
                  bool _out1348;
                  bool _out1349;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1350;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1347, out _out1348, out _out1349, out _out1350);
                  _1996_recursiveGen = _out1347;
                  _1997_recOwned = _out1348;
                  _1998_recErased = _out1349;
                  _1999_recIdents = _out1350;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1996_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1997_recOwned;
                  isErased = _1998_recErased;
                  readIdents = _1999_recIdents;
                }
              } else if (_source67.is_Primitive) {
                DAST._IPrimitive _2000___mcc_h1033 = _source67.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2001_recursiveGen;
                  bool _2002_recOwned;
                  bool _2003_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2004_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1351;
                  bool _out1352;
                  bool _out1353;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1351, out _out1352, out _out1353, out _out1354);
                  _2001_recursiveGen = _out1351;
                  _2002_recOwned = _out1352;
                  _2003_recErased = _out1353;
                  _2004_recIdents = _out1354;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2001_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2002_recOwned;
                  isErased = _2003_recErased;
                  readIdents = _2004_recIdents;
                }
              } else if (_source67.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _2005___mcc_h1035 = _source67.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2006_recursiveGen;
                  bool _2007_recOwned;
                  bool _2008_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1355;
                  bool _out1356;
                  bool _out1357;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1358;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1355, out _out1356, out _out1357, out _out1358);
                  _2006_recursiveGen = _out1355;
                  _2007_recOwned = _out1356;
                  _2008_recErased = _out1357;
                  _2009_recIdents = _out1358;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2006_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2007_recOwned;
                  isErased = _2008_recErased;
                  readIdents = _2009_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _2010___mcc_h1037 = _source67.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2011_recursiveGen;
                  bool _2012_recOwned;
                  bool _2013_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2014_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1359;
                  bool _out1360;
                  bool _out1361;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
                  DCOMP.COMP.GenExpr(_495_expr, selfIdent, @params, mustOwn, out _out1359, out _out1360, out _out1361, out _out1362);
                  _2011_recursiveGen = _out1359;
                  _2012_recOwned = _out1360;
                  _2013_recErased = _out1361;
                  _2014_recIdents = _out1362;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2011_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2012_recOwned;
                  isErased = _2013_recErased;
                  readIdents = _2014_recIdents;
                }
              }
            }
          }
        }
      } else if (_source19.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _2015___mcc_h22 = _source19.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2016_exprs = _2015___mcc_h22;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2017_generatedValues;
          _2017_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2018_i;
          _2018_i = BigInteger.Zero;
          bool _2019_allErased;
          _2019_allErased = true;
          while ((_2018_i) < (new BigInteger((_2016_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2020_recursiveGen;
            bool _2021___v63;
            bool _2022_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2023_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1363;
            bool _out1364;
            bool _out1365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1366;
            DCOMP.COMP.GenExpr((_2016_exprs).Select(_2018_i), selfIdent, @params, true, out _out1363, out _out1364, out _out1365, out _out1366);
            _2020_recursiveGen = _out1363;
            _2021___v63 = _out1364;
            _2022_isErased = _out1365;
            _2023_recIdents = _out1366;
            _2019_allErased = (_2019_allErased) && (_2022_isErased);
            _2017_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2017_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2020_recursiveGen, _2022_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2023_recIdents);
            _2018_i = (_2018_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2018_i = BigInteger.Zero;
          while ((_2018_i) < (new BigInteger((_2017_generatedValues).Count))) {
            if ((_2018_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2024_gen;
            _2024_gen = ((_2017_generatedValues).Select(_2018_i)).dtor__0;
            if ((((_2017_generatedValues).Select(_2018_i)).dtor__1) && (!(_2019_allErased))) {
              _2024_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2024_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2024_gen);
            _2018_i = (_2018_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _2019_allErased;
        }
      } else if (_source19.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _2025___mcc_h23 = _source19.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2026_exprs = _2025___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2027_generatedValues;
          _2027_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2028_i;
          _2028_i = BigInteger.Zero;
          bool _2029_allErased;
          _2029_allErased = true;
          while ((_2028_i) < (new BigInteger((_2026_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2030_recursiveGen;
            bool _2031___v64;
            bool _2032_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2033_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1367;
            bool _out1368;
            bool _out1369;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
            DCOMP.COMP.GenExpr((_2026_exprs).Select(_2028_i), selfIdent, @params, true, out _out1367, out _out1368, out _out1369, out _out1370);
            _2030_recursiveGen = _out1367;
            _2031___v64 = _out1368;
            _2032_isErased = _out1369;
            _2033_recIdents = _out1370;
            _2029_allErased = (_2029_allErased) && (_2032_isErased);
            _2027_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2027_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2030_recursiveGen, _2032_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2033_recIdents);
            _2028_i = (_2028_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2028_i = BigInteger.Zero;
          while ((_2028_i) < (new BigInteger((_2027_generatedValues).Count))) {
            if ((_2028_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2034_gen;
            _2034_gen = ((_2027_generatedValues).Select(_2028_i)).dtor__0;
            if ((((_2027_generatedValues).Select(_2028_i)).dtor__1) && (!(_2029_allErased))) {
              _2034_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2034_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2034_gen);
            _2028_i = (_2028_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashSet<_>>()"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_This) {
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source69 = selfIdent;
          if (_source69.is_Some) {
            Dafny.ISequence<Dafny.Rune> _2035___mcc_h1039 = _source69.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _2036_id = _2035___mcc_h1039;
            {
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(_2036_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                isOwned = true;
              } else {
                if ((_2036_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
                } else {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2036_id);
                }
                isOwned = false;
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2036_id);
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
      } else if (_source19.is_Ite) {
        DAST._IExpression _2037___mcc_h24 = _source19.dtor_cond;
        DAST._IExpression _2038___mcc_h25 = _source19.dtor_thn;
        DAST._IExpression _2039___mcc_h26 = _source19.dtor_els;
        DAST._IExpression _2040_f = _2039___mcc_h26;
        DAST._IExpression _2041_t = _2038___mcc_h25;
        DAST._IExpression _2042_cond = _2037___mcc_h24;
        {
          Dafny.ISequence<Dafny.Rune> _2043_condString;
          bool _2044___v65;
          bool _2045_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2046_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1371;
          bool _out1372;
          bool _out1373;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
          DCOMP.COMP.GenExpr(_2042_cond, selfIdent, @params, true, out _out1371, out _out1372, out _out1373, out _out1374);
          _2043_condString = _out1371;
          _2044___v65 = _out1372;
          _2045_condErased = _out1373;
          _2046_recIdentsCond = _out1374;
          if (!(_2045_condErased)) {
            _2043_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2043_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2047___v66;
          bool _2048_tHasToBeOwned;
          bool _2049___v67;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050___v68;
          Dafny.ISequence<Dafny.Rune> _out1375;
          bool _out1376;
          bool _out1377;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1378;
          DCOMP.COMP.GenExpr(_2041_t, selfIdent, @params, mustOwn, out _out1375, out _out1376, out _out1377, out _out1378);
          _2047___v66 = _out1375;
          _2048_tHasToBeOwned = _out1376;
          _2049___v67 = _out1377;
          _2050___v68 = _out1378;
          Dafny.ISequence<Dafny.Rune> _2051_fString;
          bool _2052_fOwned;
          bool _2053_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2054_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1379;
          bool _out1380;
          bool _out1381;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1382;
          DCOMP.COMP.GenExpr(_2040_f, selfIdent, @params, _2048_tHasToBeOwned, out _out1379, out _out1380, out _out1381, out _out1382);
          _2051_fString = _out1379;
          _2052_fOwned = _out1380;
          _2053_fErased = _out1381;
          _2054_recIdentsF = _out1382;
          Dafny.ISequence<Dafny.Rune> _2055_tString;
          bool _2056___v69;
          bool _2057_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2058_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1383;
          bool _out1384;
          bool _out1385;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1386;
          DCOMP.COMP.GenExpr(_2041_t, selfIdent, @params, _2052_fOwned, out _out1383, out _out1384, out _out1385, out _out1386);
          _2055_tString = _out1383;
          _2056___v69 = _out1384;
          _2057_tErased = _out1385;
          _2058_recIdentsT = _out1386;
          if ((!(_2053_fErased)) || (!(_2057_tErased))) {
            if (_2053_fErased) {
              _2051_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2051_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2057_tErased) {
              _2055_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2055_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _2043_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2055_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _2051_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _2052_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2046_recIdentsCond, _2058_recIdentsT), _2054_recIdentsF);
          isErased = (_2053_fErased) || (_2057_tErased);
        }
      } else if (_source19.is_UnOp) {
        DAST._IUnaryOp _2059___mcc_h27 = _source19.dtor_unOp;
        DAST._IExpression _2060___mcc_h28 = _source19.dtor_expr;
        DAST._IUnaryOp _source70 = _2059___mcc_h27;
        if (_source70.is_Not) {
          DAST._IExpression _2061_e = _2060___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2062_recursiveGen;
            bool _2063___v70;
            bool _2064_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2065_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1387;
            bool _out1388;
            bool _out1389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1390;
            DCOMP.COMP.GenExpr(_2061_e, selfIdent, @params, true, out _out1387, out _out1388, out _out1389, out _out1390);
            _2062_recursiveGen = _out1387;
            _2063___v70 = _out1388;
            _2064_recErased = _out1389;
            _2065_recIdents = _out1390;
            if (!(_2064_recErased)) {
              _2062_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2062_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _2062_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2065_recIdents;
            isErased = true;
          }
        } else if (_source70.is_BitwiseNot) {
          DAST._IExpression _2066_e = _2060___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2067_recursiveGen;
            bool _2068___v71;
            bool _2069_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2070_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1391;
            bool _out1392;
            bool _out1393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
            DCOMP.COMP.GenExpr(_2066_e, selfIdent, @params, true, out _out1391, out _out1392, out _out1393, out _out1394);
            _2067_recursiveGen = _out1391;
            _2068___v71 = _out1392;
            _2069_recErased = _out1393;
            _2070_recIdents = _out1394;
            if (!(_2069_recErased)) {
              _2067_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2067_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _2067_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2070_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _2071_e = _2060___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2072_recursiveGen;
            bool _2073_recOwned;
            bool _2074_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2075_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1395;
            bool _out1396;
            bool _out1397;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1398;
            DCOMP.COMP.GenExpr(_2071_e, selfIdent, @params, false, out _out1395, out _out1396, out _out1397, out _out1398);
            _2072_recursiveGen = _out1395;
            _2073_recOwned = _out1396;
            _2074_recErased = _out1397;
            _2075_recIdents = _out1398;
            if (!(_2074_recErased)) {
              Dafny.ISequence<Dafny.Rune> _2076_eraseFn;
              _2076_eraseFn = ((_2073_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2072_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2076_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2072_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2072_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len())"));
            isOwned = true;
            readIdents = _2075_recIdents;
            isErased = true;
          }
        }
      } else if (_source19.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _2077___mcc_h29 = _source19.dtor_op;
        DAST._IExpression _2078___mcc_h30 = _source19.dtor_left;
        DAST._IExpression _2079___mcc_h31 = _source19.dtor_right;
        DAST._IExpression _2080_r = _2079___mcc_h31;
        DAST._IExpression _2081_l = _2078___mcc_h30;
        Dafny.ISequence<Dafny.Rune> _2082_op = _2077___mcc_h29;
        {
          Dafny.ISequence<Dafny.Rune> _2083_left;
          bool _2084___v72;
          bool _2085_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1399;
          bool _out1400;
          bool _out1401;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
          DCOMP.COMP.GenExpr(_2081_l, selfIdent, @params, true, out _out1399, out _out1400, out _out1401, out _out1402);
          _2083_left = _out1399;
          _2084___v72 = _out1400;
          _2085_leftErased = _out1401;
          _2086_recIdentsL = _out1402;
          Dafny.ISequence<Dafny.Rune> _2087_right;
          bool _2088___v73;
          bool _2089_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2090_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1403;
          bool _out1404;
          bool _out1405;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1406;
          DCOMP.COMP.GenExpr(_2080_r, selfIdent, @params, true, out _out1403, out _out1404, out _out1405, out _out1406);
          _2087_right = _out1403;
          _2088___v73 = _out1404;
          _2089_rightErased = _out1405;
          _2090_recIdentsR = _out1406;
          if (!(_2085_leftErased)) {
            _2083_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2083_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_2089_rightErased)) {
            _2087_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2087_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_2082_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _2083_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2087_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_2082_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _2083_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2087_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2083_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2082_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2087_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2086_recIdentsL, _2090_recIdentsR);
          isErased = true;
        }
      } else if (_source19.is_ArrayLen) {
        DAST._IExpression _2091___mcc_h32 = _source19.dtor_expr;
        DAST._IExpression _2092_expr = _2091___mcc_h32;
        {
          Dafny.ISequence<Dafny.Rune> _2093_recursiveGen;
          bool _2094___v74;
          bool _2095_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2096_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1407;
          bool _out1408;
          bool _out1409;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1410;
          DCOMP.COMP.GenExpr(_2092_expr, selfIdent, @params, true, out _out1407, out _out1408, out _out1409, out _out1410);
          _2093_recursiveGen = _out1407;
          _2094___v74 = _out1408;
          _2095_recErased = _out1409;
          _2096_recIdents = _out1410;
          if (!(_2095_recErased)) {
            _2093_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2093_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2093_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())"));
          isOwned = true;
          readIdents = _2096_recIdents;
          isErased = true;
        }
      } else if (_source19.is_Select) {
        DAST._IExpression _2097___mcc_h33 = _source19.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2098___mcc_h34 = _source19.dtor_field;
        bool _2099___mcc_h35 = _source19.dtor_isConstant;
        bool _2100___mcc_h36 = _source19.dtor_onDatatype;
        DAST._IExpression _source71 = _2097___mcc_h33;
        if (_source71.is_Literal) {
          DAST._ILiteral _2101___mcc_h37 = _source71.dtor_Literal_a0;
          bool _2102_isDatatype = _2100___mcc_h36;
          bool _2103_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2104_field = _2098___mcc_h34;
          DAST._IExpression _2105_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2106_onString;
            bool _2107_onOwned;
            bool _2108_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2109_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1411;
            bool _out1412;
            bool _out1413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1414;
            DCOMP.COMP.GenExpr(_2105_on, selfIdent, @params, false, out _out1411, out _out1412, out _out1413, out _out1414);
            _2106_onString = _out1411;
            _2107_onOwned = _out1412;
            _2108_onErased = _out1413;
            _2109_recIdents = _out1414;
            if (!(_2108_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2110_eraseFn;
              _2110_eraseFn = ((_2107_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2106_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2110_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2106_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2102_isDatatype) || (_2103_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2106_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2104_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2103_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2106_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2104_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2109_recIdents;
          }
        } else if (_source71.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2111___mcc_h39 = _source71.dtor_Ident_a0;
          bool _2112_isDatatype = _2100___mcc_h36;
          bool _2113_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2114_field = _2098___mcc_h34;
          DAST._IExpression _2115_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2116_onString;
            bool _2117_onOwned;
            bool _2118_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2119_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1415;
            bool _out1416;
            bool _out1417;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
            DCOMP.COMP.GenExpr(_2115_on, selfIdent, @params, false, out _out1415, out _out1416, out _out1417, out _out1418);
            _2116_onString = _out1415;
            _2117_onOwned = _out1416;
            _2118_onErased = _out1417;
            _2119_recIdents = _out1418;
            if (!(_2118_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2120_eraseFn;
              _2120_eraseFn = ((_2117_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2116_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2120_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2116_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2112_isDatatype) || (_2113_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2116_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2114_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2113_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2116_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2114_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2119_recIdents;
          }
        } else if (_source71.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2121___mcc_h41 = _source71.dtor_Companion_a0;
          bool _2122_isDatatype = _2100___mcc_h36;
          bool _2123_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2124_field = _2098___mcc_h34;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2125_c = _2121___mcc_h41;
          {
            Dafny.ISequence<Dafny.Rune> _2126_onString;
            bool _2127_onOwned;
            bool _2128_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2129_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1419;
            bool _out1420;
            bool _out1421;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1422;
            DCOMP.COMP.GenExpr(DAST.Expression.create_Companion(_2125_c), selfIdent, @params, false, out _out1419, out _out1420, out _out1421, out _out1422);
            _2126_onString = _out1419;
            _2127_onOwned = _out1420;
            _2128_onErased = _out1421;
            _2129_recIdents = _out1422;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2126_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2124_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            isOwned = true;
            isErased = false;
            readIdents = _2129_recIdents;
          }
        } else if (_source71.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2130___mcc_h43 = _source71.dtor_Tuple_a0;
          bool _2131_isDatatype = _2100___mcc_h36;
          bool _2132_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2133_field = _2098___mcc_h34;
          DAST._IExpression _2134_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2135_onString;
            bool _2136_onOwned;
            bool _2137_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2138_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1423;
            bool _out1424;
            bool _out1425;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1426;
            DCOMP.COMP.GenExpr(_2134_on, selfIdent, @params, false, out _out1423, out _out1424, out _out1425, out _out1426);
            _2135_onString = _out1423;
            _2136_onOwned = _out1424;
            _2137_onErased = _out1425;
            _2138_recIdents = _out1426;
            if (!(_2137_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2139_eraseFn;
              _2139_eraseFn = ((_2136_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2135_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2139_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2135_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2131_isDatatype) || (_2132_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2135_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2133_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2132_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2135_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2133_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2138_recIdents;
          }
        } else if (_source71.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2140___mcc_h45 = _source71.dtor_path;
          Dafny.ISequence<DAST._IExpression> _2141___mcc_h46 = _source71.dtor_args;
          bool _2142_isDatatype = _2100___mcc_h36;
          bool _2143_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2144_field = _2098___mcc_h34;
          DAST._IExpression _2145_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2146_onString;
            bool _2147_onOwned;
            bool _2148_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2149_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1427;
            bool _out1428;
            bool _out1429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1430;
            DCOMP.COMP.GenExpr(_2145_on, selfIdent, @params, false, out _out1427, out _out1428, out _out1429, out _out1430);
            _2146_onString = _out1427;
            _2147_onOwned = _out1428;
            _2148_onErased = _out1429;
            _2149_recIdents = _out1430;
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
        } else if (_source71.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _2151___mcc_h49 = _source71.dtor_dims;
          bool _2152_isDatatype = _2100___mcc_h36;
          bool _2153_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2154_field = _2098___mcc_h34;
          DAST._IExpression _2155_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2156_onString;
            bool _2157_onOwned;
            bool _2158_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2159_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1431;
            bool _out1432;
            bool _out1433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1434;
            DCOMP.COMP.GenExpr(_2155_on, selfIdent, @params, false, out _out1431, out _out1432, out _out1433, out _out1434);
            _2156_onString = _out1431;
            _2157_onOwned = _out1432;
            _2158_onErased = _out1433;
            _2159_recIdents = _out1434;
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
        } else if (_source71.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2161___mcc_h51 = _source71.dtor_path;
          Dafny.ISequence<Dafny.Rune> _2162___mcc_h52 = _source71.dtor_variant;
          bool _2163___mcc_h53 = _source71.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2164___mcc_h54 = _source71.dtor_contents;
          bool _2165_isDatatype = _2100___mcc_h36;
          bool _2166_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2167_field = _2098___mcc_h34;
          DAST._IExpression _2168_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2169_onString;
            bool _2170_onOwned;
            bool _2171_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2172_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1435;
            bool _out1436;
            bool _out1437;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1438;
            DCOMP.COMP.GenExpr(_2168_on, selfIdent, @params, false, out _out1435, out _out1436, out _out1437, out _out1438);
            _2169_onString = _out1435;
            _2170_onOwned = _out1436;
            _2171_onErased = _out1437;
            _2172_recIdents = _out1438;
            if (!(_2171_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2173_eraseFn;
              _2173_eraseFn = ((_2170_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2169_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2173_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2169_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2165_isDatatype) || (_2166_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2169_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2167_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2166_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2169_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2167_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2172_recIdents;
          }
        } else if (_source71.is_Convert) {
          DAST._IExpression _2174___mcc_h59 = _source71.dtor_value;
          DAST._IType _2175___mcc_h60 = _source71.dtor_from;
          DAST._IType _2176___mcc_h61 = _source71.dtor_typ;
          bool _2177_isDatatype = _2100___mcc_h36;
          bool _2178_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2179_field = _2098___mcc_h34;
          DAST._IExpression _2180_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2181_onString;
            bool _2182_onOwned;
            bool _2183_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2184_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1439;
            bool _out1440;
            bool _out1441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
            DCOMP.COMP.GenExpr(_2180_on, selfIdent, @params, false, out _out1439, out _out1440, out _out1441, out _out1442);
            _2181_onString = _out1439;
            _2182_onOwned = _out1440;
            _2183_onErased = _out1441;
            _2184_recIdents = _out1442;
            if (!(_2183_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2185_eraseFn;
              _2185_eraseFn = ((_2182_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2181_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2185_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2181_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2177_isDatatype) || (_2178_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2181_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2179_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2178_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2181_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2179_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2184_recIdents;
          }
        } else if (_source71.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2186___mcc_h65 = _source71.dtor_elements;
          bool _2187_isDatatype = _2100___mcc_h36;
          bool _2188_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2189_field = _2098___mcc_h34;
          DAST._IExpression _2190_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2191_onString;
            bool _2192_onOwned;
            bool _2193_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1443;
            bool _out1444;
            bool _out1445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1446;
            DCOMP.COMP.GenExpr(_2190_on, selfIdent, @params, false, out _out1443, out _out1444, out _out1445, out _out1446);
            _2191_onString = _out1443;
            _2192_onOwned = _out1444;
            _2193_onErased = _out1445;
            _2194_recIdents = _out1446;
            if (!(_2193_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2195_eraseFn;
              _2195_eraseFn = ((_2192_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2191_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2195_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2191_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2187_isDatatype) || (_2188_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2191_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2189_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2188_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2191_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2189_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2194_recIdents;
          }
        } else if (_source71.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2196___mcc_h67 = _source71.dtor_elements;
          bool _2197_isDatatype = _2100___mcc_h36;
          bool _2198_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2199_field = _2098___mcc_h34;
          DAST._IExpression _2200_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2201_onString;
            bool _2202_onOwned;
            bool _2203_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2204_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1447;
            bool _out1448;
            bool _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            DCOMP.COMP.GenExpr(_2200_on, selfIdent, @params, false, out _out1447, out _out1448, out _out1449, out _out1450);
            _2201_onString = _out1447;
            _2202_onOwned = _out1448;
            _2203_onErased = _out1449;
            _2204_recIdents = _out1450;
            if (!(_2203_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2205_eraseFn;
              _2205_eraseFn = ((_2202_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2201_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2205_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2201_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2197_isDatatype) || (_2198_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2201_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2199_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2198_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2201_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2199_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2204_recIdents;
          }
        } else if (_source71.is_This) {
          bool _2206_isDatatype = _2100___mcc_h36;
          bool _2207_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2208_field = _2098___mcc_h34;
          DAST._IExpression _2209_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2210_onString;
            bool _2211_onOwned;
            bool _2212_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2213_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1451;
            bool _out1452;
            bool _out1453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1454;
            DCOMP.COMP.GenExpr(_2209_on, selfIdent, @params, false, out _out1451, out _out1452, out _out1453, out _out1454);
            _2210_onString = _out1451;
            _2211_onOwned = _out1452;
            _2212_onErased = _out1453;
            _2213_recIdents = _out1454;
            if (!(_2212_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2214_eraseFn;
              _2214_eraseFn = ((_2211_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2210_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2214_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2210_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2206_isDatatype) || (_2207_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2210_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2208_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2207_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2210_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2208_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2213_recIdents;
          }
        } else if (_source71.is_Ite) {
          DAST._IExpression _2215___mcc_h69 = _source71.dtor_cond;
          DAST._IExpression _2216___mcc_h70 = _source71.dtor_thn;
          DAST._IExpression _2217___mcc_h71 = _source71.dtor_els;
          bool _2218_isDatatype = _2100___mcc_h36;
          bool _2219_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2220_field = _2098___mcc_h34;
          DAST._IExpression _2221_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2222_onString;
            bool _2223_onOwned;
            bool _2224_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2225_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1455;
            bool _out1456;
            bool _out1457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1458;
            DCOMP.COMP.GenExpr(_2221_on, selfIdent, @params, false, out _out1455, out _out1456, out _out1457, out _out1458);
            _2222_onString = _out1455;
            _2223_onOwned = _out1456;
            _2224_onErased = _out1457;
            _2225_recIdents = _out1458;
            if (!(_2224_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2226_eraseFn;
              _2226_eraseFn = ((_2223_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2222_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2226_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2222_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2218_isDatatype) || (_2219_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2222_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2220_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2219_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2222_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2220_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2225_recIdents;
          }
        } else if (_source71.is_UnOp) {
          DAST._IUnaryOp _2227___mcc_h75 = _source71.dtor_unOp;
          DAST._IExpression _2228___mcc_h76 = _source71.dtor_expr;
          bool _2229_isDatatype = _2100___mcc_h36;
          bool _2230_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2231_field = _2098___mcc_h34;
          DAST._IExpression _2232_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2233_onString;
            bool _2234_onOwned;
            bool _2235_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2236_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1459;
            bool _out1460;
            bool _out1461;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
            DCOMP.COMP.GenExpr(_2232_on, selfIdent, @params, false, out _out1459, out _out1460, out _out1461, out _out1462);
            _2233_onString = _out1459;
            _2234_onOwned = _out1460;
            _2235_onErased = _out1461;
            _2236_recIdents = _out1462;
            if (!(_2235_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2237_eraseFn;
              _2237_eraseFn = ((_2234_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2233_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2237_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2233_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2229_isDatatype) || (_2230_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2233_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2231_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2230_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2233_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2231_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2236_recIdents;
          }
        } else if (_source71.is_BinOp) {
          Dafny.ISequence<Dafny.Rune> _2238___mcc_h79 = _source71.dtor_op;
          DAST._IExpression _2239___mcc_h80 = _source71.dtor_left;
          DAST._IExpression _2240___mcc_h81 = _source71.dtor_right;
          bool _2241_isDatatype = _2100___mcc_h36;
          bool _2242_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2243_field = _2098___mcc_h34;
          DAST._IExpression _2244_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2245_onString;
            bool _2246_onOwned;
            bool _2247_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2248_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1463;
            bool _out1464;
            bool _out1465;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1466;
            DCOMP.COMP.GenExpr(_2244_on, selfIdent, @params, false, out _out1463, out _out1464, out _out1465, out _out1466);
            _2245_onString = _out1463;
            _2246_onOwned = _out1464;
            _2247_onErased = _out1465;
            _2248_recIdents = _out1466;
            if (!(_2247_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2249_eraseFn;
              _2249_eraseFn = ((_2246_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2245_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2249_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2245_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2241_isDatatype) || (_2242_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2245_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2243_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2242_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2245_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2243_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2248_recIdents;
          }
        } else if (_source71.is_ArrayLen) {
          DAST._IExpression _2250___mcc_h85 = _source71.dtor_expr;
          bool _2251_isDatatype = _2100___mcc_h36;
          bool _2252_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2253_field = _2098___mcc_h34;
          DAST._IExpression _2254_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2255_onString;
            bool _2256_onOwned;
            bool _2257_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2258_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1467;
            bool _out1468;
            bool _out1469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
            DCOMP.COMP.GenExpr(_2254_on, selfIdent, @params, false, out _out1467, out _out1468, out _out1469, out _out1470);
            _2255_onString = _out1467;
            _2256_onOwned = _out1468;
            _2257_onErased = _out1469;
            _2258_recIdents = _out1470;
            if (!(_2257_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2259_eraseFn;
              _2259_eraseFn = ((_2256_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2255_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2259_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2255_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2251_isDatatype) || (_2252_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2255_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2253_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2252_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2255_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2253_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2258_recIdents;
          }
        } else if (_source71.is_Select) {
          DAST._IExpression _2260___mcc_h87 = _source71.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2261___mcc_h88 = _source71.dtor_field;
          bool _2262___mcc_h89 = _source71.dtor_isConstant;
          bool _2263___mcc_h90 = _source71.dtor_onDatatype;
          bool _2264_isDatatype = _2100___mcc_h36;
          bool _2265_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2266_field = _2098___mcc_h34;
          DAST._IExpression _2267_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2268_onString;
            bool _2269_onOwned;
            bool _2270_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2271_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1471;
            bool _out1472;
            bool _out1473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1474;
            DCOMP.COMP.GenExpr(_2267_on, selfIdent, @params, false, out _out1471, out _out1472, out _out1473, out _out1474);
            _2268_onString = _out1471;
            _2269_onOwned = _out1472;
            _2270_onErased = _out1473;
            _2271_recIdents = _out1474;
            if (!(_2270_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2272_eraseFn;
              _2272_eraseFn = ((_2269_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2268_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2272_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2268_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2264_isDatatype) || (_2265_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2268_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2266_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2265_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2268_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2266_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2271_recIdents;
          }
        } else if (_source71.is_SelectFn) {
          DAST._IExpression _2273___mcc_h95 = _source71.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2274___mcc_h96 = _source71.dtor_field;
          bool _2275___mcc_h97 = _source71.dtor_onDatatype;
          bool _2276___mcc_h98 = _source71.dtor_isStatic;
          BigInteger _2277___mcc_h99 = _source71.dtor_arity;
          bool _2278_isDatatype = _2100___mcc_h36;
          bool _2279_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2280_field = _2098___mcc_h34;
          DAST._IExpression _2281_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2282_onString;
            bool _2283_onOwned;
            bool _2284_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2285_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1475;
            bool _out1476;
            bool _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            DCOMP.COMP.GenExpr(_2281_on, selfIdent, @params, false, out _out1475, out _out1476, out _out1477, out _out1478);
            _2282_onString = _out1475;
            _2283_onOwned = _out1476;
            _2284_onErased = _out1477;
            _2285_recIdents = _out1478;
            if (!(_2284_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2286_eraseFn;
              _2286_eraseFn = ((_2283_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2282_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2286_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2282_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2278_isDatatype) || (_2279_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2282_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2280_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2279_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2282_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2280_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2285_recIdents;
          }
        } else if (_source71.is_Index) {
          DAST._IExpression _2287___mcc_h105 = _source71.dtor_expr;
          DAST._IExpression _2288___mcc_h106 = _source71.dtor_idx;
          bool _2289_isDatatype = _2100___mcc_h36;
          bool _2290_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2291_field = _2098___mcc_h34;
          DAST._IExpression _2292_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2293_onString;
            bool _2294_onOwned;
            bool _2295_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2296_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1479;
            bool _out1480;
            bool _out1481;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1482;
            DCOMP.COMP.GenExpr(_2292_on, selfIdent, @params, false, out _out1479, out _out1480, out _out1481, out _out1482);
            _2293_onString = _out1479;
            _2294_onOwned = _out1480;
            _2295_onErased = _out1481;
            _2296_recIdents = _out1482;
            if (!(_2295_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2297_eraseFn;
              _2297_eraseFn = ((_2294_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2293_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2297_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2293_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2289_isDatatype) || (_2290_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2293_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2291_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2290_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2293_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2291_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2296_recIdents;
          }
        } else if (_source71.is_TupleSelect) {
          DAST._IExpression _2298___mcc_h109 = _source71.dtor_expr;
          BigInteger _2299___mcc_h110 = _source71.dtor_index;
          bool _2300_isDatatype = _2100___mcc_h36;
          bool _2301_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2302_field = _2098___mcc_h34;
          DAST._IExpression _2303_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2304_onString;
            bool _2305_onOwned;
            bool _2306_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2307_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1483;
            bool _out1484;
            bool _out1485;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
            DCOMP.COMP.GenExpr(_2303_on, selfIdent, @params, false, out _out1483, out _out1484, out _out1485, out _out1486);
            _2304_onString = _out1483;
            _2305_onOwned = _out1484;
            _2306_onErased = _out1485;
            _2307_recIdents = _out1486;
            if (!(_2306_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2308_eraseFn;
              _2308_eraseFn = ((_2305_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2304_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2308_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2304_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2300_isDatatype) || (_2301_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2304_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2302_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2301_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2304_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2302_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2307_recIdents;
          }
        } else if (_source71.is_Call) {
          DAST._IExpression _2309___mcc_h113 = _source71.dtor_on;
          Dafny.ISequence<Dafny.Rune> _2310___mcc_h114 = _source71.dtor_name;
          Dafny.ISequence<DAST._IType> _2311___mcc_h115 = _source71.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2312___mcc_h116 = _source71.dtor_args;
          bool _2313_isDatatype = _2100___mcc_h36;
          bool _2314_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2315_field = _2098___mcc_h34;
          DAST._IExpression _2316_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2317_onString;
            bool _2318_onOwned;
            bool _2319_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2320_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1487;
            bool _out1488;
            bool _out1489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1490;
            DCOMP.COMP.GenExpr(_2316_on, selfIdent, @params, false, out _out1487, out _out1488, out _out1489, out _out1490);
            _2317_onString = _out1487;
            _2318_onOwned = _out1488;
            _2319_onErased = _out1489;
            _2320_recIdents = _out1490;
            if (!(_2319_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2321_eraseFn;
              _2321_eraseFn = ((_2318_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2317_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2321_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2317_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2313_isDatatype) || (_2314_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2317_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2315_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2314_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2317_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2315_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2320_recIdents;
          }
        } else if (_source71.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2322___mcc_h121 = _source71.dtor_params;
          DAST._IType _2323___mcc_h122 = _source71.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2324___mcc_h123 = _source71.dtor_body;
          bool _2325_isDatatype = _2100___mcc_h36;
          bool _2326_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2327_field = _2098___mcc_h34;
          DAST._IExpression _2328_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2329_onString;
            bool _2330_onOwned;
            bool _2331_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2332_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1491;
            bool _out1492;
            bool _out1493;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1494;
            DCOMP.COMP.GenExpr(_2328_on, selfIdent, @params, false, out _out1491, out _out1492, out _out1493, out _out1494);
            _2329_onString = _out1491;
            _2330_onOwned = _out1492;
            _2331_onErased = _out1493;
            _2332_recIdents = _out1494;
            if (!(_2331_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2333_eraseFn;
              _2333_eraseFn = ((_2330_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2329_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2333_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2329_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2325_isDatatype) || (_2326_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2329_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2327_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2326_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2329_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2327_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2332_recIdents;
          }
        } else if (_source71.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2334___mcc_h127 = _source71.dtor_name;
          DAST._IType _2335___mcc_h128 = _source71.dtor_typ;
          DAST._IExpression _2336___mcc_h129 = _source71.dtor_value;
          DAST._IExpression _2337___mcc_h130 = _source71.dtor_iifeBody;
          bool _2338_isDatatype = _2100___mcc_h36;
          bool _2339_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2340_field = _2098___mcc_h34;
          DAST._IExpression _2341_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2342_onString;
            bool _2343_onOwned;
            bool _2344_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2345_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1495;
            bool _out1496;
            bool _out1497;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1498;
            DCOMP.COMP.GenExpr(_2341_on, selfIdent, @params, false, out _out1495, out _out1496, out _out1497, out _out1498);
            _2342_onString = _out1495;
            _2343_onOwned = _out1496;
            _2344_onErased = _out1497;
            _2345_recIdents = _out1498;
            if (!(_2344_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2346_eraseFn;
              _2346_eraseFn = ((_2343_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2342_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2346_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2342_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2338_isDatatype) || (_2339_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2342_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2340_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2339_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2342_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2340_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2345_recIdents;
          }
        } else if (_source71.is_Apply) {
          DAST._IExpression _2347___mcc_h135 = _source71.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2348___mcc_h136 = _source71.dtor_args;
          bool _2349_isDatatype = _2100___mcc_h36;
          bool _2350_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2351_field = _2098___mcc_h34;
          DAST._IExpression _2352_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2353_onString;
            bool _2354_onOwned;
            bool _2355_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2356_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1499;
            bool _out1500;
            bool _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            DCOMP.COMP.GenExpr(_2352_on, selfIdent, @params, false, out _out1499, out _out1500, out _out1501, out _out1502);
            _2353_onString = _out1499;
            _2354_onOwned = _out1500;
            _2355_onErased = _out1501;
            _2356_recIdents = _out1502;
            if (!(_2355_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2357_eraseFn;
              _2357_eraseFn = ((_2354_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2353_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2357_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2353_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2349_isDatatype) || (_2350_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2353_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2351_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2350_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2353_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2351_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2356_recIdents;
          }
        } else if (_source71.is_TypeTest) {
          DAST._IExpression _2358___mcc_h139 = _source71.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2359___mcc_h140 = _source71.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2360___mcc_h141 = _source71.dtor_variant;
          bool _2361_isDatatype = _2100___mcc_h36;
          bool _2362_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2363_field = _2098___mcc_h34;
          DAST._IExpression _2364_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2365_onString;
            bool _2366_onOwned;
            bool _2367_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2368_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1503;
            bool _out1504;
            bool _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            DCOMP.COMP.GenExpr(_2364_on, selfIdent, @params, false, out _out1503, out _out1504, out _out1505, out _out1506);
            _2365_onString = _out1503;
            _2366_onOwned = _out1504;
            _2367_onErased = _out1505;
            _2368_recIdents = _out1506;
            if (!(_2367_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2369_eraseFn;
              _2369_eraseFn = ((_2366_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2365_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2369_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2365_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2361_isDatatype) || (_2362_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2365_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2363_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2362_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2365_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2363_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2368_recIdents;
          }
        } else {
          DAST._IType _2370___mcc_h145 = _source71.dtor_typ;
          bool _2371_isDatatype = _2100___mcc_h36;
          bool _2372_isConstant = _2099___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2373_field = _2098___mcc_h34;
          DAST._IExpression _2374_on = _2097___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2375_onString;
            bool _2376_onOwned;
            bool _2377_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2378_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1507;
            bool _out1508;
            bool _out1509;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1510;
            DCOMP.COMP.GenExpr(_2374_on, selfIdent, @params, false, out _out1507, out _out1508, out _out1509, out _out1510);
            _2375_onString = _out1507;
            _2376_onOwned = _out1508;
            _2377_onErased = _out1509;
            _2378_recIdents = _out1510;
            if (!(_2377_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2379_eraseFn;
              _2379_eraseFn = ((_2376_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2375_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2379_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2375_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2371_isDatatype) || (_2372_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2375_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2373_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2372_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2375_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2373_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2378_recIdents;
          }
        }
      } else if (_source19.is_SelectFn) {
        DAST._IExpression _2380___mcc_h147 = _source19.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2381___mcc_h148 = _source19.dtor_field;
        bool _2382___mcc_h149 = _source19.dtor_onDatatype;
        bool _2383___mcc_h150 = _source19.dtor_isStatic;
        BigInteger _2384___mcc_h151 = _source19.dtor_arity;
        BigInteger _2385_arity = _2384___mcc_h151;
        bool _2386_isStatic = _2383___mcc_h150;
        bool _2387_isDatatype = _2382___mcc_h149;
        Dafny.ISequence<Dafny.Rune> _2388_field = _2381___mcc_h148;
        DAST._IExpression _2389_on = _2380___mcc_h147;
        {
          Dafny.ISequence<Dafny.Rune> _2390_onString;
          bool _2391_onOwned;
          bool _2392___v75;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2393_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1511;
          bool _out1512;
          bool _out1513;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1514;
          DCOMP.COMP.GenExpr(_2389_on, selfIdent, @params, false, out _out1511, out _out1512, out _out1513, out _out1514);
          _2390_onString = _out1511;
          _2391_onOwned = _out1512;
          _2392___v75 = _out1513;
          _2393_recIdents = _out1514;
          if (_2386_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2390_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2388_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2390_onString), ((_2391_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _2394_args;
            _2394_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _2395_i;
            _2395_i = BigInteger.Zero;
            while ((_2395_i) < (_2385_arity)) {
              if ((_2395_i).Sign == 1) {
                _2394_args = Dafny.Sequence<Dafny.Rune>.Concat(_2394_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2394_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2394_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_2395_i));
              _2395_i = (_2395_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2394_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _2388_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2394_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = true;
          readIdents = _2393_recIdents;
        }
      } else if (_source19.is_Index) {
        DAST._IExpression _2396___mcc_h152 = _source19.dtor_expr;
        DAST._IExpression _2397___mcc_h153 = _source19.dtor_idx;
        DAST._IExpression _2398_idx = _2397___mcc_h153;
        DAST._IExpression _2399_on = _2396___mcc_h152;
        {
          Dafny.ISequence<Dafny.Rune> _2400_onString;
          bool _2401_onOwned;
          bool _2402_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2403_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1515;
          bool _out1516;
          bool _out1517;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
          DCOMP.COMP.GenExpr(_2399_on, selfIdent, @params, false, out _out1515, out _out1516, out _out1517, out _out1518);
          _2400_onString = _out1515;
          _2401_onOwned = _out1516;
          _2402_onErased = _out1517;
          _2403_recIdents = _out1518;
          if (!(_2402_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2404_eraseFn;
            _2404_eraseFn = ((_2401_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2400_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2404_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2400_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2405_idxString;
          bool _2406___v76;
          bool _2407_idxErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2408_recIdentsIdx;
          Dafny.ISequence<Dafny.Rune> _out1519;
          bool _out1520;
          bool _out1521;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1522;
          DCOMP.COMP.GenExpr(_2398_idx, selfIdent, @params, true, out _out1519, out _out1520, out _out1521, out _out1522);
          _2405_idxString = _out1519;
          _2406___v76 = _out1520;
          _2407_idxErased = _out1521;
          _2408_recIdentsIdx = _out1522;
          if (!(_2407_idxErased)) {
            _2405_idxString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2405_idxString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2400_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[<usize as ::dafny_runtime::NumCast>::from(")), _2405_idxString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = false;
          }
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2403_recIdents, _2408_recIdentsIdx);
        }
      } else if (_source19.is_TupleSelect) {
        DAST._IExpression _2409___mcc_h154 = _source19.dtor_expr;
        BigInteger _2410___mcc_h155 = _source19.dtor_index;
        BigInteger _2411_idx = _2410___mcc_h155;
        DAST._IExpression _2412_on = _2409___mcc_h154;
        {
          Dafny.ISequence<Dafny.Rune> _2413_onString;
          bool _2414___v77;
          bool _2415_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2416_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1523;
          bool _out1524;
          bool _out1525;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1526;
          DCOMP.COMP.GenExpr(_2412_on, selfIdent, @params, false, out _out1523, out _out1524, out _out1525, out _out1526);
          _2413_onString = _out1523;
          _2414___v77 = _out1524;
          _2415_tupErased = _out1525;
          _2416_recIdents = _out1526;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2413_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_2411_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _2415_tupErased;
          readIdents = _2416_recIdents;
        }
      } else if (_source19.is_Call) {
        DAST._IExpression _2417___mcc_h156 = _source19.dtor_on;
        Dafny.ISequence<Dafny.Rune> _2418___mcc_h157 = _source19.dtor_name;
        Dafny.ISequence<DAST._IType> _2419___mcc_h158 = _source19.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2420___mcc_h159 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2421_args = _2420___mcc_h159;
        Dafny.ISequence<DAST._IType> _2422_typeArgs = _2419___mcc_h158;
        Dafny.ISequence<Dafny.Rune> _2423_name = _2418___mcc_h157;
        DAST._IExpression _2424_on = _2417___mcc_h156;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2425_typeArgString;
          _2425_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2422_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2426_typeI;
            _2426_typeI = BigInteger.Zero;
            _2425_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_2426_typeI) < (new BigInteger((_2422_typeArgs).Count))) {
              if ((_2426_typeI).Sign == 1) {
                _2425_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2425_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _2427_typeString;
              Dafny.ISequence<Dafny.Rune> _out1527;
              _out1527 = DCOMP.COMP.GenType((_2422_typeArgs).Select(_2426_typeI), false, false);
              _2427_typeString = _out1527;
              _2425_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2425_typeArgString, _2427_typeString);
              _2426_typeI = (_2426_typeI) + (BigInteger.One);
            }
            _2425_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2425_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _2428_argString;
          _2428_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2429_i;
          _2429_i = BigInteger.Zero;
          while ((_2429_i) < (new BigInteger((_2421_args).Count))) {
            if ((_2429_i).Sign == 1) {
              _2428_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2428_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2430_argExpr;
            bool _2431_isOwned;
            bool _2432_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2433_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1528;
            bool _out1529;
            bool _out1530;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1531;
            DCOMP.COMP.GenExpr((_2421_args).Select(_2429_i), selfIdent, @params, false, out _out1528, out _out1529, out _out1530, out _out1531);
            _2430_argExpr = _out1528;
            _2431_isOwned = _out1529;
            _2432_argErased = _out1530;
            _2433_argIdents = _out1531;
            if (_2431_isOwned) {
              _2430_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2430_argExpr);
            }
            _2428_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2428_argString, _2430_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2433_argIdents);
            _2429_i = (_2429_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2434_enclosingString;
          bool _2435___v78;
          bool _2436___v79;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2437_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1532;
          bool _out1533;
          bool _out1534;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1535;
          DCOMP.COMP.GenExpr(_2424_on, selfIdent, @params, false, out _out1532, out _out1533, out _out1534, out _out1535);
          _2434_enclosingString = _out1532;
          _2435___v78 = _out1533;
          _2436___v79 = _out1534;
          _2437_recIdents = _out1535;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2437_recIdents);
          DAST._IExpression _source72 = _2424_on;
          if (_source72.is_Literal) {
            DAST._ILiteral _2438___mcc_h1040 = _source72.dtor_Literal_a0;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2439___mcc_h1042 = _source72.dtor_Ident_a0;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2440___mcc_h1044 = _source72.dtor_Companion_a0;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_2434_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source72.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2441___mcc_h1046 = _source72.dtor_Tuple_a0;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2442___mcc_h1048 = _source72.dtor_path;
            Dafny.ISequence<DAST._IExpression> _2443___mcc_h1049 = _source72.dtor_args;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2444___mcc_h1052 = _source72.dtor_dims;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2445___mcc_h1054 = _source72.dtor_path;
            Dafny.ISequence<Dafny.Rune> _2446___mcc_h1055 = _source72.dtor_variant;
            bool _2447___mcc_h1056 = _source72.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2448___mcc_h1057 = _source72.dtor_contents;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Convert) {
            DAST._IExpression _2449___mcc_h1062 = _source72.dtor_value;
            DAST._IType _2450___mcc_h1063 = _source72.dtor_from;
            DAST._IType _2451___mcc_h1064 = _source72.dtor_typ;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2452___mcc_h1068 = _source72.dtor_elements;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2453___mcc_h1070 = _source72.dtor_elements;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_This) {
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Ite) {
            DAST._IExpression _2454___mcc_h1072 = _source72.dtor_cond;
            DAST._IExpression _2455___mcc_h1073 = _source72.dtor_thn;
            DAST._IExpression _2456___mcc_h1074 = _source72.dtor_els;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_UnOp) {
            DAST._IUnaryOp _2457___mcc_h1078 = _source72.dtor_unOp;
            DAST._IExpression _2458___mcc_h1079 = _source72.dtor_expr;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _2459___mcc_h1082 = _source72.dtor_op;
            DAST._IExpression _2460___mcc_h1083 = _source72.dtor_left;
            DAST._IExpression _2461___mcc_h1084 = _source72.dtor_right;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_ArrayLen) {
            DAST._IExpression _2462___mcc_h1088 = _source72.dtor_expr;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Select) {
            DAST._IExpression _2463___mcc_h1090 = _source72.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2464___mcc_h1091 = _source72.dtor_field;
            bool _2465___mcc_h1092 = _source72.dtor_isConstant;
            bool _2466___mcc_h1093 = _source72.dtor_onDatatype;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_SelectFn) {
            DAST._IExpression _2467___mcc_h1098 = _source72.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2468___mcc_h1099 = _source72.dtor_field;
            bool _2469___mcc_h1100 = _source72.dtor_onDatatype;
            bool _2470___mcc_h1101 = _source72.dtor_isStatic;
            BigInteger _2471___mcc_h1102 = _source72.dtor_arity;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Index) {
            DAST._IExpression _2472___mcc_h1108 = _source72.dtor_expr;
            DAST._IExpression _2473___mcc_h1109 = _source72.dtor_idx;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_TupleSelect) {
            DAST._IExpression _2474___mcc_h1112 = _source72.dtor_expr;
            BigInteger _2475___mcc_h1113 = _source72.dtor_index;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Call) {
            DAST._IExpression _2476___mcc_h1116 = _source72.dtor_on;
            Dafny.ISequence<Dafny.Rune> _2477___mcc_h1117 = _source72.dtor_name;
            Dafny.ISequence<DAST._IType> _2478___mcc_h1118 = _source72.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2479___mcc_h1119 = _source72.dtor_args;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2480___mcc_h1124 = _source72.dtor_params;
            DAST._IType _2481___mcc_h1125 = _source72.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2482___mcc_h1126 = _source72.dtor_body;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2483___mcc_h1130 = _source72.dtor_name;
            DAST._IType _2484___mcc_h1131 = _source72.dtor_typ;
            DAST._IExpression _2485___mcc_h1132 = _source72.dtor_value;
            DAST._IExpression _2486___mcc_h1133 = _source72.dtor_iifeBody;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_Apply) {
            DAST._IExpression _2487___mcc_h1138 = _source72.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2488___mcc_h1139 = _source72.dtor_args;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source72.is_TypeTest) {
            DAST._IExpression _2489___mcc_h1142 = _source72.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2490___mcc_h1143 = _source72.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2491___mcc_h1144 = _source72.dtor_variant;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _2492___mcc_h1148 = _source72.dtor_typ;
            {
              _2434_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2434_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_2423_name)), _2425_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2428_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source19.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2493___mcc_h160 = _source19.dtor_params;
        DAST._IType _2494___mcc_h161 = _source19.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2495___mcc_h162 = _source19.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2496_body = _2495___mcc_h162;
        DAST._IType _2497_retType = _2494___mcc_h161;
        Dafny.ISequence<DAST._IFormal> _2498_params = _2493___mcc_h160;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2499_paramNames;
          _2499_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2500_i;
          _2500_i = BigInteger.Zero;
          while ((_2500_i) < (new BigInteger((_2498_params).Count))) {
            _2499_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2499_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2498_params).Select(_2500_i)).dtor_name));
            _2500_i = (_2500_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2501_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2502_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1536;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1537;
          DCOMP.COMP.GenStmts(_2496_body, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), _2499_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1536, out _out1537);
          _2501_recursiveGen = _out1536;
          _2502_recIdents = _out1537;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2503_allReadCloned;
          _2503_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2502_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2504_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2502_recIdents).Elements) {
              _2504_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2502_recIdents).Contains(_2504_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1643)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2499_paramNames).Contains(_2504_next))) {
              _2503_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2503_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2504_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2504_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2504_next));
            }
            _2502_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2502_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2504_next));
          }
          Dafny.ISequence<Dafny.Rune> _2505_paramsString;
          _2505_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2500_i = BigInteger.Zero;
          while ((_2500_i) < (new BigInteger((_2498_params).Count))) {
            if ((_2500_i).Sign == 1) {
              _2505_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2505_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2506_typStr;
            Dafny.ISequence<Dafny.Rune> _out1538;
            _out1538 = DCOMP.COMP.GenType(((_2498_params).Select(_2500_i)).dtor_typ, false, true);
            _2506_typStr = _out1538;
            _2505_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2505_paramsString, ((_2498_params).Select(_2500_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2506_typStr);
            _2500_i = (_2500_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2507_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1539;
          _out1539 = DCOMP.COMP.GenType(_2497_retType, false, true);
          _2507_retTypeGen = _out1539;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper({\n"), _2503_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::boxed::Box::new(move |")), _2505_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2507_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2501_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source19.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2508___mcc_h163 = _source19.dtor_name;
        DAST._IType _2509___mcc_h164 = _source19.dtor_typ;
        DAST._IExpression _2510___mcc_h165 = _source19.dtor_value;
        DAST._IExpression _2511___mcc_h166 = _source19.dtor_iifeBody;
        DAST._IExpression _2512_iifeBody = _2511___mcc_h166;
        DAST._IExpression _2513_value = _2510___mcc_h165;
        DAST._IType _2514_tpe = _2509___mcc_h164;
        Dafny.ISequence<Dafny.Rune> _2515_name = _2508___mcc_h163;
        {
          Dafny.ISequence<Dafny.Rune> _2516_valueGen;
          bool _2517_valueOwned;
          bool _2518_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2519_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1540;
          bool _out1541;
          bool _out1542;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1543;
          DCOMP.COMP.GenExpr(_2513_value, selfIdent, @params, false, out _out1540, out _out1541, out _out1542, out _out1543);
          _2516_valueGen = _out1540;
          _2517_valueOwned = _out1541;
          _2518_valueErased = _out1542;
          _2519_recIdents = _out1543;
          if (_2518_valueErased) {
            Dafny.ISequence<Dafny.Rune> _2520_eraseFn;
            _2520_eraseFn = ((_2517_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
            _2516_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::"), _2520_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2516_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2519_recIdents;
          Dafny.ISequence<Dafny.Rune> _2521_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1544;
          _out1544 = DCOMP.COMP.GenType(_2514_tpe, false, true);
          _2521_valueTypeGen = _out1544;
          Dafny.ISequence<Dafny.Rune> _2522_bodyGen;
          bool _2523_bodyOwned;
          bool _2524_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2525_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1545;
          bool _out1546;
          bool _out1547;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1548;
          DCOMP.COMP.GenExpr(_2512_iifeBody, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, ((_2517_valueOwned) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2515_name))))), mustOwn, out _out1545, out _out1546, out _out1547, out _out1548);
          _2522_bodyGen = _out1545;
          _2523_bodyOwned = _out1546;
          _2524_bodyErased = _out1547;
          _2525_bodyIdents = _out1548;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2525_bodyIdents);
          Dafny.ISequence<Dafny.Rune> _2526_eraseFn;
          _2526_eraseFn = ((_2517_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2515_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((_2517_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")))), _2521_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2516_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2522_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2523_bodyOwned;
          isErased = _2524_bodyErased;
        }
      } else if (_source19.is_Apply) {
        DAST._IExpression _2527___mcc_h167 = _source19.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2528___mcc_h168 = _source19.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2529_args = _2528___mcc_h168;
        DAST._IExpression _2530_func = _2527___mcc_h167;
        {
          Dafny.ISequence<Dafny.Rune> _2531_funcString;
          bool _2532___v82;
          bool _2533_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2534_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1549;
          bool _out1550;
          bool _out1551;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1552;
          DCOMP.COMP.GenExpr(_2530_func, selfIdent, @params, false, out _out1549, out _out1550, out _out1551, out _out1552);
          _2531_funcString = _out1549;
          _2532___v82 = _out1550;
          _2533_funcErased = _out1551;
          _2534_recIdents = _out1552;
          readIdents = _2534_recIdents;
          Dafny.ISequence<Dafny.Rune> _2535_argString;
          _2535_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2536_i;
          _2536_i = BigInteger.Zero;
          while ((_2536_i) < (new BigInteger((_2529_args).Count))) {
            if ((_2536_i).Sign == 1) {
              _2535_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2535_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2537_argExpr;
            bool _2538_isOwned;
            bool _2539_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2540_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1553;
            bool _out1554;
            bool _out1555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1556;
            DCOMP.COMP.GenExpr((_2529_args).Select(_2536_i), selfIdent, @params, false, out _out1553, out _out1554, out _out1555, out _out1556);
            _2537_argExpr = _out1553;
            _2538_isOwned = _out1554;
            _2539_argErased = _out1555;
            _2540_argIdents = _out1556;
            if (_2538_isOwned) {
              _2537_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2537_argExpr);
            }
            _2535_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2535_argString, _2537_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2540_argIdents);
            _2536_i = (_2536_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2531_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2535_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source19.is_TypeTest) {
        DAST._IExpression _2541___mcc_h169 = _source19.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2542___mcc_h170 = _source19.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2543___mcc_h171 = _source19.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2544_variant = _2543___mcc_h171;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2545_dType = _2542___mcc_h170;
        DAST._IExpression _2546_on = _2541___mcc_h169;
        {
          Dafny.ISequence<Dafny.Rune> _2547_exprGen;
          bool _2548___v83;
          bool _2549_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2550_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1557;
          bool _out1558;
          bool _out1559;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1560;
          DCOMP.COMP.GenExpr(_2546_on, selfIdent, @params, false, out _out1557, out _out1558, out _out1559, out _out1560);
          _2547_exprGen = _out1557;
          _2548___v83 = _out1558;
          _2549_exprErased = _out1559;
          _2550_recIdents = _out1560;
          Dafny.ISequence<Dafny.Rune> _2551_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1561;
          _out1561 = DCOMP.COMP.GenPath(_2545_dType);
          _2551_dTypePath = _out1561;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2547_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2551_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2544_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2550_recIdents;
        }
      } else {
        DAST._IType _2552___mcc_h172 = _source19.dtor_typ;
        DAST._IType _2553_typ = _2552___mcc_h172;
        {
          Dafny.ISequence<Dafny.Rune> _2554_typString;
          Dafny.ISequence<Dafny.Rune> _out1562;
          _out1562 = DCOMP.COMP.GenType(_2553_typ, false, false);
          _2554_typString = _out1562;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2554_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
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
      BigInteger _2555_i;
      _2555_i = BigInteger.Zero;
      while ((_2555_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2556_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1563;
        _out1563 = DCOMP.COMP.GenModule((p).Select(_2555_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2556_generated = _out1563;
        if ((_2555_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2556_generated);
        _2555_i = (_2555_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2557_i;
      _2557_i = BigInteger.Zero;
      while ((_2557_i) < (new BigInteger((fullName).Count))) {
        if ((_2557_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2557_i));
        _2557_i = (_2557_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

