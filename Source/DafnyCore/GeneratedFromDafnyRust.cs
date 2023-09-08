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
      return (int)hash;
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
      return (int)hash;
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
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.CollKind.Map";
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
    bool is_MapValue { get; }
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
    Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> dtor_mapElems { get; }
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
    DAST._ICollKind dtor_collKind { get; }
    Dafny.ISequence<DAST._IExpression> dtor_indices { get; }
    bool dtor_isArray { get; }
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
    public static _IExpression create_MapValue(Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> mapElems) {
      return new Expression_MapValue(mapElems);
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
    public static _IExpression create_Index(DAST._IExpression expr, DAST._ICollKind collKind, Dafny.ISequence<DAST._IExpression> indices) {
      return new Expression_Index(expr, collKind, indices);
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
    public bool is_MapValue { get { return this is Expression_MapValue; } }
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
    public Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> dtor_mapElems {
      get {
        var d = this;
        return ((Expression_MapValue)d)._mapElems;
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
    public DAST._ICollKind dtor_collKind {
      get {
        var d = this;
        return ((Expression_Index)d)._collKind;
      }
    }
    public Dafny.ISequence<DAST._IExpression> dtor_indices {
      get {
        var d = this;
        return ((Expression_Index)d)._indices;
      }
    }
    public bool dtor_isArray {
      get {
        var d = this;
        return ((Expression_IndexRange)d)._isArray;
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
  public class Expression_MapValue : Expression {
    public readonly Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _mapElems;
    public Expression_MapValue(Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> mapElems) : base() {
      this._mapElems = mapElems;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_MapValue(_mapElems);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_MapValue;
      return oth != null && object.Equals(this._mapElems, oth._mapElems);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._mapElems));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.MapValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._mapElems);
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
      hash = ((hash << 5) + hash) + 11;
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
      hash = ((hash << 5) + hash) + 12;
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
      hash = ((hash << 5) + hash) + 13;
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
      hash = ((hash << 5) + hash) + 14;
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
      hash = ((hash << 5) + hash) + 15;
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
      hash = ((hash << 5) + hash) + 16;
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
      hash = ((hash << 5) + hash) + 17;
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
    public readonly DAST._ICollKind _collKind;
    public readonly Dafny.ISequence<DAST._IExpression> _indices;
    public Expression_Index(DAST._IExpression expr, DAST._ICollKind collKind, Dafny.ISequence<DAST._IExpression> indices) : base() {
      this._expr = expr;
      this._collKind = collKind;
      this._indices = indices;
    }
    public override _IExpression DowncastClone() {
      if (this is _IExpression dt) { return dt; }
      return new Expression_Index(_expr, _collKind, _indices);
    }
    public override bool Equals(object other) {
      var oth = other as DAST.Expression_Index;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._collKind, oth._collKind) && object.Equals(this._indices, oth._indices);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._collKind));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indices));
      return (int)hash;
    }
    public override string ToString() {
      string s = "DAST.Expression.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._collKind);
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
      hash = ((hash << 5) + hash) + 19;
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
      hash = ((hash << 5) + hash) + 20;
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
      hash = ((hash << 5) + hash) + 21;
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
      hash = ((hash << 5) + hash) + 22;
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
      hash = ((hash << 5) + hash) + 23;
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
      hash = ((hash << 5) + hash) + 24;
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
      hash = ((hash << 5) + hash) + 25;
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
      hash = ((hash << 5) + hash) + 26;
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
      hash = ((hash << 5) + hash) + 27;
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
          } else if (_source19.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _353___mcc_h54 = _source19.dtor_mapElems;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_This) {
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Ite) {
            DAST._IExpression _354___mcc_h56 = _source19.dtor_cond;
            DAST._IExpression _355___mcc_h57 = _source19.dtor_thn;
            DAST._IExpression _356___mcc_h58 = _source19.dtor_els;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_UnOp) {
            DAST._IUnaryOp _357___mcc_h62 = _source19.dtor_unOp;
            DAST._IExpression _358___mcc_h63 = _source19.dtor_expr;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _359___mcc_h66 = _source19.dtor_op;
            DAST._IExpression _360___mcc_h67 = _source19.dtor_left;
            DAST._IExpression _361___mcc_h68 = _source19.dtor_right;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_ArrayLen) {
            DAST._IExpression _362___mcc_h72 = _source19.dtor_expr;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Select) {
            DAST._IExpression _363___mcc_h74 = _source19.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _364___mcc_h75 = _source19.dtor_field;
            bool _365___mcc_h76 = _source19.dtor_isConstant;
            bool _366___mcc_h77 = _source19.dtor_onDatatype;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_SelectFn) {
            DAST._IExpression _367___mcc_h82 = _source19.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _368___mcc_h83 = _source19.dtor_field;
            bool _369___mcc_h84 = _source19.dtor_onDatatype;
            bool _370___mcc_h85 = _source19.dtor_isStatic;
            BigInteger _371___mcc_h86 = _source19.dtor_arity;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Index) {
            DAST._IExpression _372___mcc_h92 = _source19.dtor_expr;
            DAST._ICollKind _373___mcc_h93 = _source19.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _374___mcc_h94 = _source19.dtor_indices;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_IndexRange) {
            DAST._IExpression _375___mcc_h98 = _source19.dtor_expr;
            bool _376___mcc_h99 = _source19.dtor_isArray;
            DAST._IOptional<DAST._IExpression> _377___mcc_h100 = _source19.dtor_low;
            DAST._IOptional<DAST._IExpression> _378___mcc_h101 = _source19.dtor_high;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_TupleSelect) {
            DAST._IExpression _379___mcc_h106 = _source19.dtor_expr;
            BigInteger _380___mcc_h107 = _source19.dtor_index;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Call) {
            DAST._IExpression _381___mcc_h110 = _source19.dtor_on;
            Dafny.ISequence<Dafny.Rune> _382___mcc_h111 = _source19.dtor_name;
            Dafny.ISequence<DAST._IType> _383___mcc_h112 = _source19.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _384___mcc_h113 = _source19.dtor_args;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _385___mcc_h118 = _source19.dtor_params;
            DAST._IType _386___mcc_h119 = _source19.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _387___mcc_h120 = _source19.dtor_body;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _388___mcc_h124 = _source19.dtor_values;
            DAST._IType _389___mcc_h125 = _source19.dtor_retType;
            DAST._IExpression _390___mcc_h126 = _source19.dtor_expr;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _391___mcc_h130 = _source19.dtor_name;
            DAST._IType _392___mcc_h131 = _source19.dtor_typ;
            DAST._IExpression _393___mcc_h132 = _source19.dtor_value;
            DAST._IExpression _394___mcc_h133 = _source19.dtor_iifeBody;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Apply) {
            DAST._IExpression _395___mcc_h138 = _source19.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _396___mcc_h139 = _source19.dtor_args;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_TypeTest) {
            DAST._IExpression _397___mcc_h142 = _source19.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _398___mcc_h143 = _source19.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _399___mcc_h144 = _source19.dtor_variant;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _400___mcc_h148 = _source19.dtor_typ;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _401_receiver;
          _401_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source20 = _319_maybeOutVars;
          if (_source20.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _402___mcc_h150 = _source20.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _403_outVars = _402___mcc_h150;
            {
              if ((new BigInteger((_403_outVars).Count)) > (BigInteger.One)) {
                _401_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _404_outI;
              _404_outI = BigInteger.Zero;
              while ((_404_outI) < (new BigInteger((_403_outVars).Count))) {
                if ((_404_outI).Sign == 1) {
                  _401_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_401_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _405_outVar;
                _405_outVar = (_403_outVars).Select(_404_outI);
                _401_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_401_receiver, (_405_outVar));
                _404_outI = (_404_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_403_outVars).Count)) > (BigInteger.One)) {
                _401_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_401_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_401_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_401_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _322_name), _324_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _327_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source16.is_Return) {
        DAST._IExpression _406___mcc_h17 = _source16.dtor_expr;
        DAST._IExpression _407_expr = _406___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _408_exprString;
          bool _409___v25;
          bool _410_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _411_recIdents;
          Dafny.ISequence<Dafny.Rune> _out112;
          bool _out113;
          bool _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          DCOMP.COMP.GenExpr(_407_expr, selfIdent, @params, true, out _out112, out _out113, out _out114, out _out115);
          _408_exprString = _out112;
          _409___v25 = _out113;
          _410_recErased = _out114;
          _411_recIdents = _out115;
          _408_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _408_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _411_recIdents;
          if (isLast) {
            generated = _408_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _408_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source16.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_Break) {
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _412___mcc_h18 = _source16.dtor_toLabel;
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _413_toLabel = _412___mcc_h18;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source21 = _413_toLabel;
          if (_source21.is_Some) {
            Dafny.ISequence<Dafny.Rune> _414___mcc_h151 = _source21.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _415_lbl = _414___mcc_h151;
            {
              generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break 'label_"), _415_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          } else {
            {
              generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _416___mcc_h19 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _417_body = _416___mcc_h19;
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if (!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#_this = self.clone();\n"));
          }
          BigInteger _418_paramI;
          _418_paramI = BigInteger.Zero;
          while ((_418_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _419_param;
            _419_param = (@params).Select(_418_paramI);
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#")), _419_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _419_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
            _418_paramI = (_418_paramI) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _420_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _421_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
          DCOMP.COMP.GenStmts(_417_body, ((!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out116, out _out117);
          _420_bodyString = _out116;
          _421_bodyIdents = _out117;
          readIdents = _421_bodyIdents;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'TAIL_CALL_START: loop {\n")), _420_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
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
        DAST._IExpression _422___mcc_h20 = _source16.dtor_Print_a0;
        DAST._IExpression _423_e = _422___mcc_h20;
        {
          Dafny.ISequence<Dafny.Rune> _424_printedExpr;
          bool _425_isOwned;
          bool _426___v26;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _427_recIdents;
          Dafny.ISequence<Dafny.Rune> _out118;
          bool _out119;
          bool _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          DCOMP.COMP.GenExpr(_423_e, selfIdent, @params, false, out _out118, out _out119, out _out120, out _out121);
          _424_printedExpr = _out118;
          _425_isOwned = _out119;
          _426___v26 = _out120;
          _427_recIdents = _out121;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_425_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _424_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _427_recIdents;
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
        DAST._ILiteral _428___mcc_h0 = _source22.dtor_Literal_a0;
        DAST._ILiteral _source23 = _428___mcc_h0;
        if (_source23.is_BoolLiteral) {
          bool _429___mcc_h1 = _source23.dtor_BoolLiteral_a0;
          if ((_429___mcc_h1) == (false)) {
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
          Dafny.ISequence<Dafny.Rune> _430___mcc_h2 = _source23.dtor_IntLiteral_a0;
          DAST._IType _431___mcc_h3 = _source23.dtor_IntLiteral_a1;
          DAST._IType _432_t = _431___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _433_i = _430___mcc_h2;
          {
            DAST._IType _source24 = _432_t;
            if (_source24.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _434___mcc_h200 = _source24.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _435___mcc_h201 = _source24.dtor_typeArgs;
              DAST._IResolvedType _436___mcc_h202 = _source24.dtor_resolved;
              {
                s = _433_i;
              }
            } else if (_source24.is_Nullable) {
              DAST._IType _437___mcc_h206 = _source24.dtor_Nullable_a0;
              {
                s = _433_i;
              }
            } else if (_source24.is_Tuple) {
              Dafny.ISequence<DAST._IType> _438___mcc_h208 = _source24.dtor_Tuple_a0;
              {
                s = _433_i;
              }
            } else if (_source24.is_Array) {
              DAST._IType _439___mcc_h210 = _source24.dtor_element;
              {
                s = _433_i;
              }
            } else if (_source24.is_Seq) {
              DAST._IType _440___mcc_h212 = _source24.dtor_element;
              {
                s = _433_i;
              }
            } else if (_source24.is_Set) {
              DAST._IType _441___mcc_h214 = _source24.dtor_element;
              {
                s = _433_i;
              }
            } else if (_source24.is_Multiset) {
              DAST._IType _442___mcc_h216 = _source24.dtor_element;
              {
                s = _433_i;
              }
            } else if (_source24.is_Map) {
              DAST._IType _443___mcc_h218 = _source24.dtor_key;
              DAST._IType _444___mcc_h219 = _source24.dtor_value;
              {
                s = _433_i;
              }
            } else if (_source24.is_Arrow) {
              Dafny.ISequence<DAST._IType> _445___mcc_h222 = _source24.dtor_args;
              DAST._IType _446___mcc_h223 = _source24.dtor_result;
              {
                s = _433_i;
              }
            } else if (_source24.is_Primitive) {
              DAST._IPrimitive _447___mcc_h226 = _source24.dtor_Primitive_a0;
              DAST._IPrimitive _source25 = _447___mcc_h226;
              if (_source25.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _433_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source25.is_Real) {
                {
                  s = _433_i;
                }
              } else if (_source25.is_String) {
                {
                  s = _433_i;
                }
              } else if (_source25.is_Bool) {
                {
                  s = _433_i;
                }
              } else {
                {
                  s = _433_i;
                }
              }
            } else if (_source24.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _448___mcc_h228 = _source24.dtor_Passthrough_a0;
              {
                s = _433_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _449___mcc_h230 = _source24.dtor_TypeArg_a0;
              {
                s = _433_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _450___mcc_h4 = _source23.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _451___mcc_h5 = _source23.dtor_DecLiteral_a1;
          DAST._IType _452___mcc_h6 = _source23.dtor_DecLiteral_a2;
          DAST._IType _453_t = _452___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _454_d = _451___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _455_n = _450___mcc_h4;
          {
            DAST._IType _source26 = _453_t;
            if (_source26.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _456___mcc_h232 = _source26.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _457___mcc_h233 = _source26.dtor_typeArgs;
              DAST._IResolvedType _458___mcc_h234 = _source26.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Nullable) {
              DAST._IType _459___mcc_h238 = _source26.dtor_Nullable_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Tuple) {
              Dafny.ISequence<DAST._IType> _460___mcc_h240 = _source26.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Array) {
              DAST._IType _461___mcc_h242 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Seq) {
              DAST._IType _462___mcc_h244 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Set) {
              DAST._IType _463___mcc_h246 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Multiset) {
              DAST._IType _464___mcc_h248 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Map) {
              DAST._IType _465___mcc_h250 = _source26.dtor_key;
              DAST._IType _466___mcc_h251 = _source26.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Arrow) {
              Dafny.ISequence<DAST._IType> _467___mcc_h254 = _source26.dtor_args;
              DAST._IType _468___mcc_h255 = _source26.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Primitive) {
              DAST._IPrimitive _469___mcc_h258 = _source26.dtor_Primitive_a0;
              DAST._IPrimitive _source27 = _469___mcc_h258;
              if (_source27.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source27.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _455_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source27.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source27.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source26.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _470___mcc_h260 = _source26.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _471___mcc_h262 = _source26.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_455_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _454_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _472___mcc_h7 = _source23.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _473_l = _472___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _473_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_CharLiteral) {
          Dafny.Rune _474___mcc_h8 = _source23.dtor_CharLiteral_a0;
          Dafny.Rune _475_c = _474___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_475_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
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
        Dafny.ISequence<Dafny.Rune> _476___mcc_h9 = _source22.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _477_name = _476___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _477_name);
          if (!((@params).Contains(_477_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_477_name);
        }
      } else if (_source22.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _478___mcc_h10 = _source22.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _479_path = _478___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out122;
          _out122 = DCOMP.COMP.GenPath(_479_path);
          s = _out122;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source22.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _480___mcc_h11 = _source22.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _481_values = _480___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _482_i;
          _482_i = BigInteger.Zero;
          bool _483_allErased;
          _483_allErased = true;
          while ((_482_i) < (new BigInteger((_481_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _484___v29;
            bool _485___v30;
            bool _486_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _487___v31;
            Dafny.ISequence<Dafny.Rune> _out123;
            bool _out124;
            bool _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            DCOMP.COMP.GenExpr((_481_values).Select(_482_i), selfIdent, @params, true, out _out123, out _out124, out _out125, out _out126);
            _484___v29 = _out123;
            _485___v30 = _out124;
            _486_isErased = _out125;
            _487___v31 = _out126;
            _483_allErased = (_483_allErased) && (_486_isErased);
            _482_i = (_482_i) + (BigInteger.One);
          }
          _482_i = BigInteger.Zero;
          while ((_482_i) < (new BigInteger((_481_values).Count))) {
            if ((_482_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _488_recursiveGen;
            bool _489___v32;
            bool _490_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _491_recIdents;
            Dafny.ISequence<Dafny.Rune> _out127;
            bool _out128;
            bool _out129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
            DCOMP.COMP.GenExpr((_481_values).Select(_482_i), selfIdent, @params, true, out _out127, out _out128, out _out129, out _out130);
            _488_recursiveGen = _out127;
            _489___v32 = _out128;
            _490_isErased = _out129;
            _491_recIdents = _out130;
            if ((_490_isErased) && (!(_483_allErased))) {
              _488_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _488_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _488_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _491_recIdents);
            _482_i = (_482_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _483_allErased;
        }
      } else if (_source22.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _492___mcc_h12 = _source22.dtor_path;
        Dafny.ISequence<DAST._IExpression> _493___mcc_h13 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _494_args = _493___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _495_path = _492___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _496_path;
          Dafny.ISequence<Dafny.Rune> _out131;
          _out131 = DCOMP.COMP.GenPath(_495_path);
          _496_path = _out131;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _496_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _497_i;
          _497_i = BigInteger.Zero;
          while ((_497_i) < (new BigInteger((_494_args).Count))) {
            if ((_497_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _498_recursiveGen;
            bool _499___v33;
            bool _500_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _501_recIdents;
            Dafny.ISequence<Dafny.Rune> _out132;
            bool _out133;
            bool _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            DCOMP.COMP.GenExpr((_494_args).Select(_497_i), selfIdent, @params, true, out _out132, out _out133, out _out134, out _out135);
            _498_recursiveGen = _out132;
            _499___v33 = _out133;
            _500_isErased = _out134;
            _501_recIdents = _out135;
            if (_500_isErased) {
              _498_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _498_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _498_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _501_recIdents);
            _497_i = (_497_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _502___mcc_h14 = _source22.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _503_dims = _502___mcc_h14;
        {
          BigInteger _504_i;
          _504_i = (new BigInteger((_503_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_504_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _505_recursiveGen;
            bool _506___v34;
            bool _507_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _508_recIdents;
            Dafny.ISequence<Dafny.Rune> _out136;
            bool _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP.COMP.GenExpr((_503_dims).Select(_504_i), selfIdent, @params, true, out _out136, out _out137, out _out138, out _out139);
            _505_recursiveGen = _out136;
            _506___v34 = _out137;
            _507_isErased = _out138;
            _508_recIdents = _out139;
            if (!(_507_isErased)) {
              _505_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _505_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _505_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _508_recIdents);
            _504_i = (_504_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _509___mcc_h15 = _source22.dtor_path;
        Dafny.ISequence<Dafny.Rune> _510___mcc_h16 = _source22.dtor_variant;
        bool _511___mcc_h17 = _source22.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _512___mcc_h18 = _source22.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _513_values = _512___mcc_h18;
        bool _514_isCo = _511___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _515_variant = _510___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _516_path = _509___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _517_path;
          Dafny.ISequence<Dafny.Rune> _out140;
          _out140 = DCOMP.COMP.GenPath(_516_path);
          _517_path = _out140;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _517_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _515_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _518_i;
          _518_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_518_i) < (new BigInteger((_513_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_513_values).Select(_518_i);
            Dafny.ISequence<Dafny.Rune> _519_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _520_value = _let_tmp_rhs0.dtor__1;
            if ((_518_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_514_isCo) {
              Dafny.ISequence<Dafny.Rune> _521_recursiveGen;
              bool _522___v35;
              bool _523_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _524_recIdents;
              Dafny.ISequence<Dafny.Rune> _out141;
              bool _out142;
              bool _out143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
              DCOMP.COMP.GenExpr(_520_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out141, out _out142, out _out143, out _out144);
              _521_recursiveGen = _out141;
              _522___v35 = _out142;
              _523_isErased = _out143;
              _524_recIdents = _out144;
              if (!(_523_isErased)) {
                _521_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _521_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _521_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _521_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _524_recIdents);
              Dafny.ISequence<Dafny.Rune> _525_allReadCloned;
              _525_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_524_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _526_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_524_recIdents).Elements) {
                  _526_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_524_recIdents).Contains(_526_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1182)");
              after__ASSIGN_SUCH_THAT_0:;
                _525_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_525_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _526_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _526_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _524_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_524_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_526_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _519_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _525_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _521_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _527_recursiveGen;
              bool _528___v36;
              bool _529_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _530_recIdents;
              Dafny.ISequence<Dafny.Rune> _out145;
              bool _out146;
              bool _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              DCOMP.COMP.GenExpr(_520_value, selfIdent, @params, true, out _out145, out _out146, out _out147, out _out148);
              _527_recursiveGen = _out145;
              _528___v36 = _out146;
              _529_isErased = _out147;
              _530_recIdents = _out148;
              if (!(_529_isErased)) {
                _527_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _527_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _527_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _527_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _519_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _527_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _530_recIdents);
            }
            _518_i = (_518_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_Convert) {
        DAST._IExpression _531___mcc_h19 = _source22.dtor_value;
        DAST._IType _532___mcc_h20 = _source22.dtor_from;
        DAST._IType _533___mcc_h21 = _source22.dtor_typ;
        DAST._IType _534_toTpe = _533___mcc_h21;
        DAST._IType _535_fromTpe = _532___mcc_h20;
        DAST._IExpression _536_expr = _531___mcc_h19;
        {
          if (object.Equals(_535_fromTpe, _534_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _537_recursiveGen;
            bool _538_recOwned;
            bool _539_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _540_recIdents;
            Dafny.ISequence<Dafny.Rune> _out149;
            bool _out150;
            bool _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out149, out _out150, out _out151, out _out152);
            _537_recursiveGen = _out149;
            _538_recOwned = _out150;
            _539_recErased = _out151;
            _540_recIdents = _out152;
            s = _537_recursiveGen;
            isOwned = _538_recOwned;
            isErased = _539_recErased;
            readIdents = _540_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source28 = _System.Tuple2<DAST._IType, DAST._IType>.create(_535_fromTpe, _534_toTpe);
            DAST._IType _541___mcc_h264 = _source28.dtor__0;
            DAST._IType _542___mcc_h265 = _source28.dtor__1;
            DAST._IType _source29 = _541___mcc_h264;
            if (_source29.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _543___mcc_h268 = _source29.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _544___mcc_h269 = _source29.dtor_typeArgs;
              DAST._IResolvedType _545___mcc_h270 = _source29.dtor_resolved;
              DAST._IResolvedType _source30 = _545___mcc_h270;
              if (_source30.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _546___mcc_h280 = _source30.dtor_path;
                DAST._IType _source31 = _542___mcc_h265;
                if (_source31.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _547___mcc_h284 = _source31.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _548___mcc_h285 = _source31.dtor_typeArgs;
                  DAST._IResolvedType _549___mcc_h286 = _source31.dtor_resolved;
                  DAST._IResolvedType _source32 = _549___mcc_h286;
                  if (_source32.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _550___mcc_h290 = _source32.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _551_recursiveGen;
                      bool _552_recOwned;
                      bool _553_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _554_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out153;
                      bool _out154;
                      bool _out155;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out153, out _out154, out _out155, out _out156);
                      _551_recursiveGen = _out153;
                      _552_recOwned = _out154;
                      _553_recErased = _out155;
                      _554_recIdents = _out156;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _551_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _552_recOwned;
                      isErased = _553_recErased;
                      readIdents = _554_recIdents;
                    }
                  } else if (_source32.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _555___mcc_h292 = _source32.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _556_recursiveGen;
                      bool _557_recOwned;
                      bool _558_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _559_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out157;
                      bool _out158;
                      bool _out159;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out157, out _out158, out _out159, out _out160);
                      _556_recursiveGen = _out157;
                      _557_recOwned = _out158;
                      _558_recErased = _out159;
                      _559_recIdents = _out160;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _556_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _557_recOwned;
                      isErased = _558_recErased;
                      readIdents = _559_recIdents;
                    }
                  } else {
                    DAST._IType _560___mcc_h294 = _source32.dtor_Newtype_a0;
                    DAST._IType _561_b = _560___mcc_h294;
                    {
                      if (object.Equals(_535_fromTpe, _561_b)) {
                        Dafny.ISequence<Dafny.Rune> _562_recursiveGen;
                        bool _563_recOwned;
                        bool _564_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _565_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out161;
                        bool _out162;
                        bool _out163;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out161, out _out162, out _out163, out _out164);
                        _562_recursiveGen = _out161;
                        _563_recOwned = _out162;
                        _564_recErased = _out163;
                        _565_recIdents = _out164;
                        Dafny.ISequence<Dafny.Rune> _566_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out165;
                        _out165 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _566_rhsType = _out165;
                        Dafny.ISequence<Dafny.Rune> _567_uneraseFn;
                        _567_uneraseFn = ((_563_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _566_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _567_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _562_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _563_recOwned;
                        isErased = false;
                        readIdents = _565_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out166;
                        bool _out167;
                        bool _out168;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _561_b), _561_b, _534_toTpe), selfIdent, @params, mustOwn, out _out166, out _out167, out _out168, out _out169);
                        s = _out166;
                        isOwned = _out167;
                        isErased = _out168;
                        readIdents = _out169;
                      }
                    }
                  }
                } else if (_source31.is_Nullable) {
                  DAST._IType _568___mcc_h296 = _source31.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _569_recursiveGen;
                    bool _570_recOwned;
                    bool _571_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _572_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out170;
                    bool _out171;
                    bool _out172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out170, out _out171, out _out172, out _out173);
                    _569_recursiveGen = _out170;
                    _570_recOwned = _out171;
                    _571_recErased = _out172;
                    _572_recIdents = _out173;
                    if (!(_570_recOwned)) {
                      _569_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_569_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _569_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _571_recErased;
                    readIdents = _572_recIdents;
                  }
                } else if (_source31.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _573___mcc_h298 = _source31.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _574_recursiveGen;
                    bool _575_recOwned;
                    bool _576_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _577_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out174;
                    bool _out175;
                    bool _out176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out174, out _out175, out _out176, out _out177);
                    _574_recursiveGen = _out174;
                    _575_recOwned = _out175;
                    _576_recErased = _out176;
                    _577_recIdents = _out177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _575_recOwned;
                    isErased = _576_recErased;
                    readIdents = _577_recIdents;
                  }
                } else if (_source31.is_Array) {
                  DAST._IType _578___mcc_h300 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _579_recursiveGen;
                    bool _580_recOwned;
                    bool _581_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _582_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out178;
                    bool _out179;
                    bool _out180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out178, out _out179, out _out180, out _out181);
                    _579_recursiveGen = _out178;
                    _580_recOwned = _out179;
                    _581_recErased = _out180;
                    _582_recIdents = _out181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _579_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _580_recOwned;
                    isErased = _581_recErased;
                    readIdents = _582_recIdents;
                  }
                } else if (_source31.is_Seq) {
                  DAST._IType _583___mcc_h302 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _584_recursiveGen;
                    bool _585_recOwned;
                    bool _586_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _587_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out182;
                    bool _out183;
                    bool _out184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out182, out _out183, out _out184, out _out185);
                    _584_recursiveGen = _out182;
                    _585_recOwned = _out183;
                    _586_recErased = _out184;
                    _587_recIdents = _out185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _584_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _585_recOwned;
                    isErased = _586_recErased;
                    readIdents = _587_recIdents;
                  }
                } else if (_source31.is_Set) {
                  DAST._IType _588___mcc_h304 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _589_recursiveGen;
                    bool _590_recOwned;
                    bool _591_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _592_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out186;
                    bool _out187;
                    bool _out188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out186, out _out187, out _out188, out _out189);
                    _589_recursiveGen = _out186;
                    _590_recOwned = _out187;
                    _591_recErased = _out188;
                    _592_recIdents = _out189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _589_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _590_recOwned;
                    isErased = _591_recErased;
                    readIdents = _592_recIdents;
                  }
                } else if (_source31.is_Multiset) {
                  DAST._IType _593___mcc_h306 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _594_recursiveGen;
                    bool _595_recOwned;
                    bool _596_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _597_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out190;
                    bool _out191;
                    bool _out192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out190, out _out191, out _out192, out _out193);
                    _594_recursiveGen = _out190;
                    _595_recOwned = _out191;
                    _596_recErased = _out192;
                    _597_recIdents = _out193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _594_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _595_recOwned;
                    isErased = _596_recErased;
                    readIdents = _597_recIdents;
                  }
                } else if (_source31.is_Map) {
                  DAST._IType _598___mcc_h308 = _source31.dtor_key;
                  DAST._IType _599___mcc_h309 = _source31.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _600_recursiveGen;
                    bool _601_recOwned;
                    bool _602_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _603_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out194;
                    bool _out195;
                    bool _out196;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out194, out _out195, out _out196, out _out197);
                    _600_recursiveGen = _out194;
                    _601_recOwned = _out195;
                    _602_recErased = _out196;
                    _603_recIdents = _out197;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _600_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _601_recOwned;
                    isErased = _602_recErased;
                    readIdents = _603_recIdents;
                  }
                } else if (_source31.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _604___mcc_h312 = _source31.dtor_args;
                  DAST._IType _605___mcc_h313 = _source31.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _606_recursiveGen;
                    bool _607_recOwned;
                    bool _608_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _609_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out198;
                    bool _out199;
                    bool _out200;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out198, out _out199, out _out200, out _out201);
                    _606_recursiveGen = _out198;
                    _607_recOwned = _out199;
                    _608_recErased = _out200;
                    _609_recIdents = _out201;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _606_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _607_recOwned;
                    isErased = _608_recErased;
                    readIdents = _609_recIdents;
                  }
                } else if (_source31.is_Primitive) {
                  DAST._IPrimitive _610___mcc_h316 = _source31.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _611_recursiveGen;
                    bool _612_recOwned;
                    bool _613_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _614_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out202;
                    bool _out203;
                    bool _out204;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out205;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out202, out _out203, out _out204, out _out205);
                    _611_recursiveGen = _out202;
                    _612_recOwned = _out203;
                    _613_recErased = _out204;
                    _614_recIdents = _out205;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _611_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _612_recOwned;
                    isErased = _613_recErased;
                    readIdents = _614_recIdents;
                  }
                } else if (_source31.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _615___mcc_h318 = _source31.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _616_recursiveGen;
                    bool _617_recOwned;
                    bool _618_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _619_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out206;
                    bool _out207;
                    bool _out208;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out206, out _out207, out _out208, out _out209);
                    _616_recursiveGen = _out206;
                    _617_recOwned = _out207;
                    _618_recErased = _out208;
                    _619_recIdents = _out209;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _616_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _617_recOwned;
                    isErased = _618_recErased;
                    readIdents = _619_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _620___mcc_h320 = _source31.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _621_recursiveGen;
                    bool _622_recOwned;
                    bool _623_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _624_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out210;
                    bool _out211;
                    bool _out212;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out210, out _out211, out _out212, out _out213);
                    _621_recursiveGen = _out210;
                    _622_recOwned = _out211;
                    _623_recErased = _out212;
                    _624_recIdents = _out213;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _621_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _622_recOwned;
                    isErased = _623_recErased;
                    readIdents = _624_recIdents;
                  }
                }
              } else if (_source30.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _625___mcc_h322 = _source30.dtor_path;
                DAST._IType _source33 = _542___mcc_h265;
                if (_source33.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _626___mcc_h326 = _source33.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _627___mcc_h327 = _source33.dtor_typeArgs;
                  DAST._IResolvedType _628___mcc_h328 = _source33.dtor_resolved;
                  DAST._IResolvedType _source34 = _628___mcc_h328;
                  if (_source34.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _629___mcc_h332 = _source34.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _630_recursiveGen;
                      bool _631_recOwned;
                      bool _632_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _633_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out214;
                      bool _out215;
                      bool _out216;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out214, out _out215, out _out216, out _out217);
                      _630_recursiveGen = _out214;
                      _631_recOwned = _out215;
                      _632_recErased = _out216;
                      _633_recIdents = _out217;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _630_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _631_recOwned;
                      isErased = _632_recErased;
                      readIdents = _633_recIdents;
                    }
                  } else if (_source34.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _634___mcc_h334 = _source34.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _635_recursiveGen;
                      bool _636_recOwned;
                      bool _637_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _638_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out218;
                      bool _out219;
                      bool _out220;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out221;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out218, out _out219, out _out220, out _out221);
                      _635_recursiveGen = _out218;
                      _636_recOwned = _out219;
                      _637_recErased = _out220;
                      _638_recIdents = _out221;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _635_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _636_recOwned;
                      isErased = _637_recErased;
                      readIdents = _638_recIdents;
                    }
                  } else {
                    DAST._IType _639___mcc_h336 = _source34.dtor_Newtype_a0;
                    DAST._IType _640_b = _639___mcc_h336;
                    {
                      if (object.Equals(_535_fromTpe, _640_b)) {
                        Dafny.ISequence<Dafny.Rune> _641_recursiveGen;
                        bool _642_recOwned;
                        bool _643_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _644_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out222;
                        bool _out223;
                        bool _out224;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out222, out _out223, out _out224, out _out225);
                        _641_recursiveGen = _out222;
                        _642_recOwned = _out223;
                        _643_recErased = _out224;
                        _644_recIdents = _out225;
                        Dafny.ISequence<Dafny.Rune> _645_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out226;
                        _out226 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _645_rhsType = _out226;
                        Dafny.ISequence<Dafny.Rune> _646_uneraseFn;
                        _646_uneraseFn = ((_642_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _645_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _646_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _641_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _642_recOwned;
                        isErased = false;
                        readIdents = _644_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out227;
                        bool _out228;
                        bool _out229;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _640_b), _640_b, _534_toTpe), selfIdent, @params, mustOwn, out _out227, out _out228, out _out229, out _out230);
                        s = _out227;
                        isOwned = _out228;
                        isErased = _out229;
                        readIdents = _out230;
                      }
                    }
                  }
                } else if (_source33.is_Nullable) {
                  DAST._IType _647___mcc_h338 = _source33.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _648_recursiveGen;
                    bool _649_recOwned;
                    bool _650_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _651_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out231;
                    bool _out232;
                    bool _out233;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out231, out _out232, out _out233, out _out234);
                    _648_recursiveGen = _out231;
                    _649_recOwned = _out232;
                    _650_recErased = _out233;
                    _651_recIdents = _out234;
                    if (!(_649_recOwned)) {
                      _648_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_648_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _648_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _650_recErased;
                    readIdents = _651_recIdents;
                  }
                } else if (_source33.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _652___mcc_h340 = _source33.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _653_recursiveGen;
                    bool _654_recOwned;
                    bool _655_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _656_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out235;
                    bool _out236;
                    bool _out237;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out235, out _out236, out _out237, out _out238);
                    _653_recursiveGen = _out235;
                    _654_recOwned = _out236;
                    _655_recErased = _out237;
                    _656_recIdents = _out238;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _653_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _654_recOwned;
                    isErased = _655_recErased;
                    readIdents = _656_recIdents;
                  }
                } else if (_source33.is_Array) {
                  DAST._IType _657___mcc_h342 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _658_recursiveGen;
                    bool _659_recOwned;
                    bool _660_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _661_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out239;
                    bool _out240;
                    bool _out241;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out242;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out239, out _out240, out _out241, out _out242);
                    _658_recursiveGen = _out239;
                    _659_recOwned = _out240;
                    _660_recErased = _out241;
                    _661_recIdents = _out242;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _658_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _659_recOwned;
                    isErased = _660_recErased;
                    readIdents = _661_recIdents;
                  }
                } else if (_source33.is_Seq) {
                  DAST._IType _662___mcc_h344 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _663_recursiveGen;
                    bool _664_recOwned;
                    bool _665_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _666_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out243;
                    bool _out244;
                    bool _out245;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out243, out _out244, out _out245, out _out246);
                    _663_recursiveGen = _out243;
                    _664_recOwned = _out244;
                    _665_recErased = _out245;
                    _666_recIdents = _out246;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _663_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _664_recOwned;
                    isErased = _665_recErased;
                    readIdents = _666_recIdents;
                  }
                } else if (_source33.is_Set) {
                  DAST._IType _667___mcc_h346 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _668_recursiveGen;
                    bool _669_recOwned;
                    bool _670_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _671_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out247;
                    bool _out248;
                    bool _out249;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out247, out _out248, out _out249, out _out250);
                    _668_recursiveGen = _out247;
                    _669_recOwned = _out248;
                    _670_recErased = _out249;
                    _671_recIdents = _out250;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _668_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _669_recOwned;
                    isErased = _670_recErased;
                    readIdents = _671_recIdents;
                  }
                } else if (_source33.is_Multiset) {
                  DAST._IType _672___mcc_h348 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _673_recursiveGen;
                    bool _674_recOwned;
                    bool _675_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _676_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out251;
                    bool _out252;
                    bool _out253;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out251, out _out252, out _out253, out _out254);
                    _673_recursiveGen = _out251;
                    _674_recOwned = _out252;
                    _675_recErased = _out253;
                    _676_recIdents = _out254;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _673_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _674_recOwned;
                    isErased = _675_recErased;
                    readIdents = _676_recIdents;
                  }
                } else if (_source33.is_Map) {
                  DAST._IType _677___mcc_h350 = _source33.dtor_key;
                  DAST._IType _678___mcc_h351 = _source33.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _679_recursiveGen;
                    bool _680_recOwned;
                    bool _681_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _682_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out255;
                    bool _out256;
                    bool _out257;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out255, out _out256, out _out257, out _out258);
                    _679_recursiveGen = _out255;
                    _680_recOwned = _out256;
                    _681_recErased = _out257;
                    _682_recIdents = _out258;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _679_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _680_recOwned;
                    isErased = _681_recErased;
                    readIdents = _682_recIdents;
                  }
                } else if (_source33.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _683___mcc_h354 = _source33.dtor_args;
                  DAST._IType _684___mcc_h355 = _source33.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _685_recursiveGen;
                    bool _686_recOwned;
                    bool _687_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _688_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out259;
                    bool _out260;
                    bool _out261;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out259, out _out260, out _out261, out _out262);
                    _685_recursiveGen = _out259;
                    _686_recOwned = _out260;
                    _687_recErased = _out261;
                    _688_recIdents = _out262;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _685_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _686_recOwned;
                    isErased = _687_recErased;
                    readIdents = _688_recIdents;
                  }
                } else if (_source33.is_Primitive) {
                  DAST._IPrimitive _689___mcc_h358 = _source33.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _690_recursiveGen;
                    bool _691_recOwned;
                    bool _692_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _693_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out263;
                    bool _out264;
                    bool _out265;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out263, out _out264, out _out265, out _out266);
                    _690_recursiveGen = _out263;
                    _691_recOwned = _out264;
                    _692_recErased = _out265;
                    _693_recIdents = _out266;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _690_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _691_recOwned;
                    isErased = _692_recErased;
                    readIdents = _693_recIdents;
                  }
                } else if (_source33.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _694___mcc_h360 = _source33.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _695_recursiveGen;
                    bool _696_recOwned;
                    bool _697_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _698_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out267;
                    bool _out268;
                    bool _out269;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out267, out _out268, out _out269, out _out270);
                    _695_recursiveGen = _out267;
                    _696_recOwned = _out268;
                    _697_recErased = _out269;
                    _698_recIdents = _out270;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _695_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _696_recOwned;
                    isErased = _697_recErased;
                    readIdents = _698_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _699___mcc_h362 = _source33.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _700_recursiveGen;
                    bool _701_recOwned;
                    bool _702_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _703_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out271;
                    bool _out272;
                    bool _out273;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out271, out _out272, out _out273, out _out274);
                    _700_recursiveGen = _out271;
                    _701_recOwned = _out272;
                    _702_recErased = _out273;
                    _703_recIdents = _out274;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _700_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _701_recOwned;
                    isErased = _702_recErased;
                    readIdents = _703_recIdents;
                  }
                }
              } else {
                DAST._IType _704___mcc_h364 = _source30.dtor_Newtype_a0;
                DAST._IType _source35 = _542___mcc_h265;
                if (_source35.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _705___mcc_h368 = _source35.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _706___mcc_h369 = _source35.dtor_typeArgs;
                  DAST._IResolvedType _707___mcc_h370 = _source35.dtor_resolved;
                  DAST._IResolvedType _source36 = _707___mcc_h370;
                  if (_source36.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _708___mcc_h377 = _source36.dtor_path;
                    DAST._IType _709_b = _704___mcc_h364;
                    {
                      if (object.Equals(_709_b, _534_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _710_recursiveGen;
                        bool _711_recOwned;
                        bool _712_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _713_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out275;
                        bool _out276;
                        bool _out277;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out275, out _out276, out _out277, out _out278);
                        _710_recursiveGen = _out275;
                        _711_recOwned = _out276;
                        _712_recErased = _out277;
                        _713_recIdents = _out278;
                        Dafny.ISequence<Dafny.Rune> _714_uneraseFn;
                        _714_uneraseFn = ((_711_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _714_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _710_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _711_recOwned;
                        isErased = true;
                        readIdents = _713_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out279;
                        bool _out280;
                        bool _out281;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _709_b), _709_b, _534_toTpe), selfIdent, @params, mustOwn, out _out279, out _out280, out _out281, out _out282);
                        s = _out279;
                        isOwned = _out280;
                        isErased = _out281;
                        readIdents = _out282;
                      }
                    }
                  } else if (_source36.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _715___mcc_h380 = _source36.dtor_path;
                    DAST._IType _716_b = _704___mcc_h364;
                    {
                      if (object.Equals(_716_b, _534_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _717_recursiveGen;
                        bool _718_recOwned;
                        bool _719_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _720_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out283;
                        bool _out284;
                        bool _out285;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out283, out _out284, out _out285, out _out286);
                        _717_recursiveGen = _out283;
                        _718_recOwned = _out284;
                        _719_recErased = _out285;
                        _720_recIdents = _out286;
                        Dafny.ISequence<Dafny.Rune> _721_uneraseFn;
                        _721_uneraseFn = ((_718_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _721_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _717_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _718_recOwned;
                        isErased = true;
                        readIdents = _720_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out287;
                        bool _out288;
                        bool _out289;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _716_b), _716_b, _534_toTpe), selfIdent, @params, mustOwn, out _out287, out _out288, out _out289, out _out290);
                        s = _out287;
                        isOwned = _out288;
                        isErased = _out289;
                        readIdents = _out290;
                      }
                    }
                  } else {
                    DAST._IType _722___mcc_h383 = _source36.dtor_Newtype_a0;
                    DAST._IType _723_b = _722___mcc_h383;
                    {
                      if (object.Equals(_535_fromTpe, _723_b)) {
                        Dafny.ISequence<Dafny.Rune> _724_recursiveGen;
                        bool _725_recOwned;
                        bool _726_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _727_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out291;
                        bool _out292;
                        bool _out293;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out291, out _out292, out _out293, out _out294);
                        _724_recursiveGen = _out291;
                        _725_recOwned = _out292;
                        _726_recErased = _out293;
                        _727_recIdents = _out294;
                        Dafny.ISequence<Dafny.Rune> _728_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out295;
                        _out295 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _728_rhsType = _out295;
                        Dafny.ISequence<Dafny.Rune> _729_uneraseFn;
                        _729_uneraseFn = ((_725_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _728_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _729_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _724_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _725_recOwned;
                        isErased = false;
                        readIdents = _727_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out296;
                        bool _out297;
                        bool _out298;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _723_b), _723_b, _534_toTpe), selfIdent, @params, mustOwn, out _out296, out _out297, out _out298, out _out299);
                        s = _out296;
                        isOwned = _out297;
                        isErased = _out298;
                        readIdents = _out299;
                      }
                    }
                  }
                } else if (_source35.is_Nullable) {
                  DAST._IType _730___mcc_h386 = _source35.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _731_recursiveGen;
                    bool _732_recOwned;
                    bool _733_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _734_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out300;
                    bool _out301;
                    bool _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out300, out _out301, out _out302, out _out303);
                    _731_recursiveGen = _out300;
                    _732_recOwned = _out301;
                    _733_recErased = _out302;
                    _734_recIdents = _out303;
                    if (!(_732_recOwned)) {
                      _731_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_731_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _731_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _733_recErased;
                    readIdents = _734_recIdents;
                  }
                } else if (_source35.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _735___mcc_h389 = _source35.dtor_Tuple_a0;
                  DAST._IType _736_b = _704___mcc_h364;
                  {
                    if (object.Equals(_736_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _737_recursiveGen;
                      bool _738_recOwned;
                      bool _739_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _740_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out304;
                      bool _out305;
                      bool _out306;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out304, out _out305, out _out306, out _out307);
                      _737_recursiveGen = _out304;
                      _738_recOwned = _out305;
                      _739_recErased = _out306;
                      _740_recIdents = _out307;
                      Dafny.ISequence<Dafny.Rune> _741_uneraseFn;
                      _741_uneraseFn = ((_738_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _741_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _737_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _738_recOwned;
                      isErased = true;
                      readIdents = _740_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out308;
                      bool _out309;
                      bool _out310;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _736_b), _736_b, _534_toTpe), selfIdent, @params, mustOwn, out _out308, out _out309, out _out310, out _out311);
                      s = _out308;
                      isOwned = _out309;
                      isErased = _out310;
                      readIdents = _out311;
                    }
                  }
                } else if (_source35.is_Array) {
                  DAST._IType _742___mcc_h392 = _source35.dtor_element;
                  DAST._IType _743_b = _704___mcc_h364;
                  {
                    if (object.Equals(_743_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _744_recursiveGen;
                      bool _745_recOwned;
                      bool _746_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _747_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out312;
                      bool _out313;
                      bool _out314;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out312, out _out313, out _out314, out _out315);
                      _744_recursiveGen = _out312;
                      _745_recOwned = _out313;
                      _746_recErased = _out314;
                      _747_recIdents = _out315;
                      Dafny.ISequence<Dafny.Rune> _748_uneraseFn;
                      _748_uneraseFn = ((_745_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _748_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _744_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _745_recOwned;
                      isErased = true;
                      readIdents = _747_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out316;
                      bool _out317;
                      bool _out318;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _743_b), _743_b, _534_toTpe), selfIdent, @params, mustOwn, out _out316, out _out317, out _out318, out _out319);
                      s = _out316;
                      isOwned = _out317;
                      isErased = _out318;
                      readIdents = _out319;
                    }
                  }
                } else if (_source35.is_Seq) {
                  DAST._IType _749___mcc_h395 = _source35.dtor_element;
                  DAST._IType _750_b = _704___mcc_h364;
                  {
                    if (object.Equals(_750_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _751_recursiveGen;
                      bool _752_recOwned;
                      bool _753_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _754_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out320;
                      bool _out321;
                      bool _out322;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out320, out _out321, out _out322, out _out323);
                      _751_recursiveGen = _out320;
                      _752_recOwned = _out321;
                      _753_recErased = _out322;
                      _754_recIdents = _out323;
                      Dafny.ISequence<Dafny.Rune> _755_uneraseFn;
                      _755_uneraseFn = ((_752_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _755_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _751_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _752_recOwned;
                      isErased = true;
                      readIdents = _754_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out324;
                      bool _out325;
                      bool _out326;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _750_b), _750_b, _534_toTpe), selfIdent, @params, mustOwn, out _out324, out _out325, out _out326, out _out327);
                      s = _out324;
                      isOwned = _out325;
                      isErased = _out326;
                      readIdents = _out327;
                    }
                  }
                } else if (_source35.is_Set) {
                  DAST._IType _756___mcc_h398 = _source35.dtor_element;
                  DAST._IType _757_b = _704___mcc_h364;
                  {
                    if (object.Equals(_757_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _758_recursiveGen;
                      bool _759_recOwned;
                      bool _760_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _761_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out328;
                      bool _out329;
                      bool _out330;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out328, out _out329, out _out330, out _out331);
                      _758_recursiveGen = _out328;
                      _759_recOwned = _out329;
                      _760_recErased = _out330;
                      _761_recIdents = _out331;
                      Dafny.ISequence<Dafny.Rune> _762_uneraseFn;
                      _762_uneraseFn = ((_759_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _762_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _758_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _759_recOwned;
                      isErased = true;
                      readIdents = _761_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out332;
                      bool _out333;
                      bool _out334;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _757_b), _757_b, _534_toTpe), selfIdent, @params, mustOwn, out _out332, out _out333, out _out334, out _out335);
                      s = _out332;
                      isOwned = _out333;
                      isErased = _out334;
                      readIdents = _out335;
                    }
                  }
                } else if (_source35.is_Multiset) {
                  DAST._IType _763___mcc_h401 = _source35.dtor_element;
                  DAST._IType _764_b = _704___mcc_h364;
                  {
                    if (object.Equals(_764_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _765_recursiveGen;
                      bool _766_recOwned;
                      bool _767_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _768_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out336;
                      bool _out337;
                      bool _out338;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out336, out _out337, out _out338, out _out339);
                      _765_recursiveGen = _out336;
                      _766_recOwned = _out337;
                      _767_recErased = _out338;
                      _768_recIdents = _out339;
                      Dafny.ISequence<Dafny.Rune> _769_uneraseFn;
                      _769_uneraseFn = ((_766_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _769_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _765_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _766_recOwned;
                      isErased = true;
                      readIdents = _768_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out340;
                      bool _out341;
                      bool _out342;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _764_b), _764_b, _534_toTpe), selfIdent, @params, mustOwn, out _out340, out _out341, out _out342, out _out343);
                      s = _out340;
                      isOwned = _out341;
                      isErased = _out342;
                      readIdents = _out343;
                    }
                  }
                } else if (_source35.is_Map) {
                  DAST._IType _770___mcc_h404 = _source35.dtor_key;
                  DAST._IType _771___mcc_h405 = _source35.dtor_value;
                  DAST._IType _772_b = _704___mcc_h364;
                  {
                    if (object.Equals(_772_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _773_recursiveGen;
                      bool _774_recOwned;
                      bool _775_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _776_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out344;
                      bool _out345;
                      bool _out346;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out347;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out344, out _out345, out _out346, out _out347);
                      _773_recursiveGen = _out344;
                      _774_recOwned = _out345;
                      _775_recErased = _out346;
                      _776_recIdents = _out347;
                      Dafny.ISequence<Dafny.Rune> _777_uneraseFn;
                      _777_uneraseFn = ((_774_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _777_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _773_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _774_recOwned;
                      isErased = true;
                      readIdents = _776_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out348;
                      bool _out349;
                      bool _out350;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _772_b), _772_b, _534_toTpe), selfIdent, @params, mustOwn, out _out348, out _out349, out _out350, out _out351);
                      s = _out348;
                      isOwned = _out349;
                      isErased = _out350;
                      readIdents = _out351;
                    }
                  }
                } else if (_source35.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _778___mcc_h410 = _source35.dtor_args;
                  DAST._IType _779___mcc_h411 = _source35.dtor_result;
                  DAST._IType _780_b = _704___mcc_h364;
                  {
                    if (object.Equals(_780_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _781_recursiveGen;
                      bool _782_recOwned;
                      bool _783_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _784_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out352;
                      bool _out353;
                      bool _out354;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out352, out _out353, out _out354, out _out355);
                      _781_recursiveGen = _out352;
                      _782_recOwned = _out353;
                      _783_recErased = _out354;
                      _784_recIdents = _out355;
                      Dafny.ISequence<Dafny.Rune> _785_uneraseFn;
                      _785_uneraseFn = ((_782_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _785_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _781_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _782_recOwned;
                      isErased = true;
                      readIdents = _784_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out356;
                      bool _out357;
                      bool _out358;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out359;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _780_b), _780_b, _534_toTpe), selfIdent, @params, mustOwn, out _out356, out _out357, out _out358, out _out359);
                      s = _out356;
                      isOwned = _out357;
                      isErased = _out358;
                      readIdents = _out359;
                    }
                  }
                } else if (_source35.is_Primitive) {
                  DAST._IPrimitive _786___mcc_h416 = _source35.dtor_Primitive_a0;
                  DAST._IType _787_b = _704___mcc_h364;
                  {
                    if (object.Equals(_787_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _788_recursiveGen;
                      bool _789_recOwned;
                      bool _790_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _791_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out360;
                      bool _out361;
                      bool _out362;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out360, out _out361, out _out362, out _out363);
                      _788_recursiveGen = _out360;
                      _789_recOwned = _out361;
                      _790_recErased = _out362;
                      _791_recIdents = _out363;
                      Dafny.ISequence<Dafny.Rune> _792_uneraseFn;
                      _792_uneraseFn = ((_789_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _792_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _788_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _789_recOwned;
                      isErased = true;
                      readIdents = _791_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out364;
                      bool _out365;
                      bool _out366;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _787_b), _787_b, _534_toTpe), selfIdent, @params, mustOwn, out _out364, out _out365, out _out366, out _out367);
                      s = _out364;
                      isOwned = _out365;
                      isErased = _out366;
                      readIdents = _out367;
                    }
                  }
                } else if (_source35.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _793___mcc_h419 = _source35.dtor_Passthrough_a0;
                  DAST._IType _794_b = _704___mcc_h364;
                  {
                    if (object.Equals(_794_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _795_recursiveGen;
                      bool _796_recOwned;
                      bool _797_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _798_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out368;
                      bool _out369;
                      bool _out370;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out368, out _out369, out _out370, out _out371);
                      _795_recursiveGen = _out368;
                      _796_recOwned = _out369;
                      _797_recErased = _out370;
                      _798_recIdents = _out371;
                      Dafny.ISequence<Dafny.Rune> _799_uneraseFn;
                      _799_uneraseFn = ((_796_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _799_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _795_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _796_recOwned;
                      isErased = true;
                      readIdents = _798_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out372;
                      bool _out373;
                      bool _out374;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _794_b), _794_b, _534_toTpe), selfIdent, @params, mustOwn, out _out372, out _out373, out _out374, out _out375);
                      s = _out372;
                      isOwned = _out373;
                      isErased = _out374;
                      readIdents = _out375;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _800___mcc_h422 = _source35.dtor_TypeArg_a0;
                  DAST._IType _801_b = _704___mcc_h364;
                  {
                    if (object.Equals(_801_b, _534_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _802_recursiveGen;
                      bool _803_recOwned;
                      bool _804_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _805_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out376;
                      bool _out377;
                      bool _out378;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out376, out _out377, out _out378, out _out379);
                      _802_recursiveGen = _out376;
                      _803_recOwned = _out377;
                      _804_recErased = _out378;
                      _805_recIdents = _out379;
                      Dafny.ISequence<Dafny.Rune> _806_uneraseFn;
                      _806_uneraseFn = ((_803_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _806_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _802_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _803_recOwned;
                      isErased = true;
                      readIdents = _805_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out380;
                      bool _out381;
                      bool _out382;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _801_b), _801_b, _534_toTpe), selfIdent, @params, mustOwn, out _out380, out _out381, out _out382, out _out383);
                      s = _out380;
                      isOwned = _out381;
                      isErased = _out382;
                      readIdents = _out383;
                    }
                  }
                }
              }
            } else if (_source29.is_Nullable) {
              DAST._IType _807___mcc_h425 = _source29.dtor_Nullable_a0;
              DAST._IType _source37 = _542___mcc_h265;
              if (_source37.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _808___mcc_h429 = _source37.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _809___mcc_h430 = _source37.dtor_typeArgs;
                DAST._IResolvedType _810___mcc_h431 = _source37.dtor_resolved;
                DAST._IResolvedType _source38 = _810___mcc_h431;
                if (_source38.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _811___mcc_h438 = _source38.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _812_recursiveGen;
                    bool _813_recOwned;
                    bool _814_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _815_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out384;
                    bool _out385;
                    bool _out386;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out384, out _out385, out _out386, out _out387);
                    _812_recursiveGen = _out384;
                    _813_recOwned = _out385;
                    _814_recErased = _out386;
                    _815_recIdents = _out387;
                    if (!(_813_recOwned)) {
                      _812_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_812_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_812_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _813_recOwned;
                    isErased = _814_recErased;
                    readIdents = _815_recIdents;
                  }
                } else if (_source38.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _816___mcc_h441 = _source38.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _817_recursiveGen;
                    bool _818_recOwned;
                    bool _819_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _820_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out388;
                    bool _out389;
                    bool _out390;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out388, out _out389, out _out390, out _out391);
                    _817_recursiveGen = _out388;
                    _818_recOwned = _out389;
                    _819_recErased = _out390;
                    _820_recIdents = _out391;
                    if (!(_818_recOwned)) {
                      _817_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_817_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_817_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _818_recOwned;
                    isErased = _819_recErased;
                    readIdents = _820_recIdents;
                  }
                } else {
                  DAST._IType _821___mcc_h444 = _source38.dtor_Newtype_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _822_recursiveGen;
                    bool _823_recOwned;
                    bool _824_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _825_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out392;
                    bool _out393;
                    bool _out394;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out392, out _out393, out _out394, out _out395);
                    _822_recursiveGen = _out392;
                    _823_recOwned = _out393;
                    _824_recErased = _out394;
                    _825_recIdents = _out395;
                    if (!(_823_recOwned)) {
                      _822_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_822_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_822_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _823_recOwned;
                    isErased = _824_recErased;
                    readIdents = _825_recIdents;
                  }
                }
              } else if (_source37.is_Nullable) {
                DAST._IType _826___mcc_h447 = _source37.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _827_recursiveGen;
                  bool _828_recOwned;
                  bool _829_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _830_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out396;
                  bool _out397;
                  bool _out398;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out396, out _out397, out _out398, out _out399);
                  _827_recursiveGen = _out396;
                  _828_recOwned = _out397;
                  _829_recErased = _out398;
                  _830_recIdents = _out399;
                  if (!(_828_recOwned)) {
                    _827_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_827_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_827_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _828_recOwned;
                  isErased = _829_recErased;
                  readIdents = _830_recIdents;
                }
              } else if (_source37.is_Tuple) {
                Dafny.ISequence<DAST._IType> _831___mcc_h450 = _source37.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _832_recursiveGen;
                  bool _833_recOwned;
                  bool _834_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _835_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out400;
                  bool _out401;
                  bool _out402;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out400, out _out401, out _out402, out _out403);
                  _832_recursiveGen = _out400;
                  _833_recOwned = _out401;
                  _834_recErased = _out402;
                  _835_recIdents = _out403;
                  if (!(_833_recOwned)) {
                    _832_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_832_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_832_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _833_recOwned;
                  isErased = _834_recErased;
                  readIdents = _835_recIdents;
                }
              } else if (_source37.is_Array) {
                DAST._IType _836___mcc_h453 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _837_recursiveGen;
                  bool _838_recOwned;
                  bool _839_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _840_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out404;
                  bool _out405;
                  bool _out406;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out404, out _out405, out _out406, out _out407);
                  _837_recursiveGen = _out404;
                  _838_recOwned = _out405;
                  _839_recErased = _out406;
                  _840_recIdents = _out407;
                  if (!(_838_recOwned)) {
                    _837_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_837_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_837_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _838_recOwned;
                  isErased = _839_recErased;
                  readIdents = _840_recIdents;
                }
              } else if (_source37.is_Seq) {
                DAST._IType _841___mcc_h456 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _842_recursiveGen;
                  bool _843_recOwned;
                  bool _844_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _845_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out408;
                  bool _out409;
                  bool _out410;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out408, out _out409, out _out410, out _out411);
                  _842_recursiveGen = _out408;
                  _843_recOwned = _out409;
                  _844_recErased = _out410;
                  _845_recIdents = _out411;
                  if (!(_843_recOwned)) {
                    _842_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_842_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_842_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _843_recOwned;
                  isErased = _844_recErased;
                  readIdents = _845_recIdents;
                }
              } else if (_source37.is_Set) {
                DAST._IType _846___mcc_h459 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _847_recursiveGen;
                  bool _848_recOwned;
                  bool _849_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _850_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out412;
                  bool _out413;
                  bool _out414;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out412, out _out413, out _out414, out _out415);
                  _847_recursiveGen = _out412;
                  _848_recOwned = _out413;
                  _849_recErased = _out414;
                  _850_recIdents = _out415;
                  if (!(_848_recOwned)) {
                    _847_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_847_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_847_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _848_recOwned;
                  isErased = _849_recErased;
                  readIdents = _850_recIdents;
                }
              } else if (_source37.is_Multiset) {
                DAST._IType _851___mcc_h462 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _852_recursiveGen;
                  bool _853_recOwned;
                  bool _854_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _855_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out416;
                  bool _out417;
                  bool _out418;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out416, out _out417, out _out418, out _out419);
                  _852_recursiveGen = _out416;
                  _853_recOwned = _out417;
                  _854_recErased = _out418;
                  _855_recIdents = _out419;
                  if (!(_853_recOwned)) {
                    _852_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_852_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_852_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _853_recOwned;
                  isErased = _854_recErased;
                  readIdents = _855_recIdents;
                }
              } else if (_source37.is_Map) {
                DAST._IType _856___mcc_h465 = _source37.dtor_key;
                DAST._IType _857___mcc_h466 = _source37.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _858_recursiveGen;
                  bool _859_recOwned;
                  bool _860_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _861_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out420;
                  bool _out421;
                  bool _out422;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out420, out _out421, out _out422, out _out423);
                  _858_recursiveGen = _out420;
                  _859_recOwned = _out421;
                  _860_recErased = _out422;
                  _861_recIdents = _out423;
                  if (!(_859_recOwned)) {
                    _858_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_858_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_858_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _859_recOwned;
                  isErased = _860_recErased;
                  readIdents = _861_recIdents;
                }
              } else if (_source37.is_Arrow) {
                Dafny.ISequence<DAST._IType> _862___mcc_h471 = _source37.dtor_args;
                DAST._IType _863___mcc_h472 = _source37.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _864_recursiveGen;
                  bool _865_recOwned;
                  bool _866_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _867_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out424;
                  bool _out425;
                  bool _out426;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out424, out _out425, out _out426, out _out427);
                  _864_recursiveGen = _out424;
                  _865_recOwned = _out425;
                  _866_recErased = _out426;
                  _867_recIdents = _out427;
                  if (!(_865_recOwned)) {
                    _864_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_864_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_864_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _865_recOwned;
                  isErased = _866_recErased;
                  readIdents = _867_recIdents;
                }
              } else if (_source37.is_Primitive) {
                DAST._IPrimitive _868___mcc_h477 = _source37.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _869_recursiveGen;
                  bool _870_recOwned;
                  bool _871_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _872_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out428;
                  bool _out429;
                  bool _out430;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out428, out _out429, out _out430, out _out431);
                  _869_recursiveGen = _out428;
                  _870_recOwned = _out429;
                  _871_recErased = _out430;
                  _872_recIdents = _out431;
                  if (!(_870_recOwned)) {
                    _869_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_869_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_869_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _870_recOwned;
                  isErased = _871_recErased;
                  readIdents = _872_recIdents;
                }
              } else if (_source37.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _873___mcc_h480 = _source37.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _874_recursiveGen;
                  bool _875_recOwned;
                  bool _876_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _877_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out432;
                  bool _out433;
                  bool _out434;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out432, out _out433, out _out434, out _out435);
                  _874_recursiveGen = _out432;
                  _875_recOwned = _out433;
                  _876_recErased = _out434;
                  _877_recIdents = _out435;
                  if (!(_875_recOwned)) {
                    _874_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_874_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_874_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _875_recOwned;
                  isErased = _876_recErased;
                  readIdents = _877_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _878___mcc_h483 = _source37.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _879_recursiveGen;
                  bool _880_recOwned;
                  bool _881_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _882_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out436;
                  bool _out437;
                  bool _out438;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out436, out _out437, out _out438, out _out439);
                  _879_recursiveGen = _out436;
                  _880_recOwned = _out437;
                  _881_recErased = _out438;
                  _882_recIdents = _out439;
                  if (!(_880_recOwned)) {
                    _879_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_879_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_879_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _880_recOwned;
                  isErased = _881_recErased;
                  readIdents = _882_recIdents;
                }
              }
            } else if (_source29.is_Tuple) {
              Dafny.ISequence<DAST._IType> _883___mcc_h486 = _source29.dtor_Tuple_a0;
              DAST._IType _source39 = _542___mcc_h265;
              if (_source39.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _884___mcc_h490 = _source39.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _885___mcc_h491 = _source39.dtor_typeArgs;
                DAST._IResolvedType _886___mcc_h492 = _source39.dtor_resolved;
                DAST._IResolvedType _source40 = _886___mcc_h492;
                if (_source40.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _887___mcc_h496 = _source40.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _888_recursiveGen;
                    bool _889_recOwned;
                    bool _890_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _891_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out440;
                    bool _out441;
                    bool _out442;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out440, out _out441, out _out442, out _out443);
                    _888_recursiveGen = _out440;
                    _889_recOwned = _out441;
                    _890_recErased = _out442;
                    _891_recIdents = _out443;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _888_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _889_recOwned;
                    isErased = _890_recErased;
                    readIdents = _891_recIdents;
                  }
                } else if (_source40.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _892___mcc_h498 = _source40.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _893_recursiveGen;
                    bool _894_recOwned;
                    bool _895_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _896_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out444;
                    bool _out445;
                    bool _out446;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out444, out _out445, out _out446, out _out447);
                    _893_recursiveGen = _out444;
                    _894_recOwned = _out445;
                    _895_recErased = _out446;
                    _896_recIdents = _out447;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _893_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _894_recOwned;
                    isErased = _895_recErased;
                    readIdents = _896_recIdents;
                  }
                } else {
                  DAST._IType _897___mcc_h500 = _source40.dtor_Newtype_a0;
                  DAST._IType _898_b = _897___mcc_h500;
                  {
                    if (object.Equals(_535_fromTpe, _898_b)) {
                      Dafny.ISequence<Dafny.Rune> _899_recursiveGen;
                      bool _900_recOwned;
                      bool _901_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _902_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out448;
                      bool _out449;
                      bool _out450;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out448, out _out449, out _out450, out _out451);
                      _899_recursiveGen = _out448;
                      _900_recOwned = _out449;
                      _901_recErased = _out450;
                      _902_recIdents = _out451;
                      Dafny.ISequence<Dafny.Rune> _903_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out452;
                      _out452 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _903_rhsType = _out452;
                      Dafny.ISequence<Dafny.Rune> _904_uneraseFn;
                      _904_uneraseFn = ((_900_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _903_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _904_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _899_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _900_recOwned;
                      isErased = false;
                      readIdents = _902_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out453;
                      bool _out454;
                      bool _out455;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _898_b), _898_b, _534_toTpe), selfIdent, @params, mustOwn, out _out453, out _out454, out _out455, out _out456);
                      s = _out453;
                      isOwned = _out454;
                      isErased = _out455;
                      readIdents = _out456;
                    }
                  }
                }
              } else if (_source39.is_Nullable) {
                DAST._IType _905___mcc_h502 = _source39.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _906_recursiveGen;
                  bool _907_recOwned;
                  bool _908_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _909_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out457;
                  bool _out458;
                  bool _out459;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out457, out _out458, out _out459, out _out460);
                  _906_recursiveGen = _out457;
                  _907_recOwned = _out458;
                  _908_recErased = _out459;
                  _909_recIdents = _out460;
                  if (!(_907_recOwned)) {
                    _906_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_906_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _906_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _908_recErased;
                  readIdents = _909_recIdents;
                }
              } else if (_source39.is_Tuple) {
                Dafny.ISequence<DAST._IType> _910___mcc_h504 = _source39.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _911_recursiveGen;
                  bool _912_recOwned;
                  bool _913_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _914_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out461;
                  bool _out462;
                  bool _out463;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out461, out _out462, out _out463, out _out464);
                  _911_recursiveGen = _out461;
                  _912_recOwned = _out462;
                  _913_recErased = _out463;
                  _914_recIdents = _out464;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _911_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _912_recOwned;
                  isErased = _913_recErased;
                  readIdents = _914_recIdents;
                }
              } else if (_source39.is_Array) {
                DAST._IType _915___mcc_h506 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _916_recursiveGen;
                  bool _917_recOwned;
                  bool _918_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _919_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out465;
                  bool _out466;
                  bool _out467;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out465, out _out466, out _out467, out _out468);
                  _916_recursiveGen = _out465;
                  _917_recOwned = _out466;
                  _918_recErased = _out467;
                  _919_recIdents = _out468;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _916_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _917_recOwned;
                  isErased = _918_recErased;
                  readIdents = _919_recIdents;
                }
              } else if (_source39.is_Seq) {
                DAST._IType _920___mcc_h508 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _921_recursiveGen;
                  bool _922_recOwned;
                  bool _923_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _924_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out469;
                  bool _out470;
                  bool _out471;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out469, out _out470, out _out471, out _out472);
                  _921_recursiveGen = _out469;
                  _922_recOwned = _out470;
                  _923_recErased = _out471;
                  _924_recIdents = _out472;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _921_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _922_recOwned;
                  isErased = _923_recErased;
                  readIdents = _924_recIdents;
                }
              } else if (_source39.is_Set) {
                DAST._IType _925___mcc_h510 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _926_recursiveGen;
                  bool _927_recOwned;
                  bool _928_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _929_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out473;
                  bool _out474;
                  bool _out475;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out473, out _out474, out _out475, out _out476);
                  _926_recursiveGen = _out473;
                  _927_recOwned = _out474;
                  _928_recErased = _out475;
                  _929_recIdents = _out476;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _926_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _927_recOwned;
                  isErased = _928_recErased;
                  readIdents = _929_recIdents;
                }
              } else if (_source39.is_Multiset) {
                DAST._IType _930___mcc_h512 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _931_recursiveGen;
                  bool _932_recOwned;
                  bool _933_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _934_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out477;
                  bool _out478;
                  bool _out479;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out477, out _out478, out _out479, out _out480);
                  _931_recursiveGen = _out477;
                  _932_recOwned = _out478;
                  _933_recErased = _out479;
                  _934_recIdents = _out480;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _931_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _932_recOwned;
                  isErased = _933_recErased;
                  readIdents = _934_recIdents;
                }
              } else if (_source39.is_Map) {
                DAST._IType _935___mcc_h514 = _source39.dtor_key;
                DAST._IType _936___mcc_h515 = _source39.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _937_recursiveGen;
                  bool _938_recOwned;
                  bool _939_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _940_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out481;
                  bool _out482;
                  bool _out483;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out481, out _out482, out _out483, out _out484);
                  _937_recursiveGen = _out481;
                  _938_recOwned = _out482;
                  _939_recErased = _out483;
                  _940_recIdents = _out484;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _937_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _938_recOwned;
                  isErased = _939_recErased;
                  readIdents = _940_recIdents;
                }
              } else if (_source39.is_Arrow) {
                Dafny.ISequence<DAST._IType> _941___mcc_h518 = _source39.dtor_args;
                DAST._IType _942___mcc_h519 = _source39.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _943_recursiveGen;
                  bool _944_recOwned;
                  bool _945_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _946_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out485;
                  bool _out486;
                  bool _out487;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out488;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out485, out _out486, out _out487, out _out488);
                  _943_recursiveGen = _out485;
                  _944_recOwned = _out486;
                  _945_recErased = _out487;
                  _946_recIdents = _out488;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _943_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _944_recOwned;
                  isErased = _945_recErased;
                  readIdents = _946_recIdents;
                }
              } else if (_source39.is_Primitive) {
                DAST._IPrimitive _947___mcc_h522 = _source39.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _948_recursiveGen;
                  bool _949_recOwned;
                  bool _950_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _951_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out489;
                  bool _out490;
                  bool _out491;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out489, out _out490, out _out491, out _out492);
                  _948_recursiveGen = _out489;
                  _949_recOwned = _out490;
                  _950_recErased = _out491;
                  _951_recIdents = _out492;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _948_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _949_recOwned;
                  isErased = _950_recErased;
                  readIdents = _951_recIdents;
                }
              } else if (_source39.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _952___mcc_h524 = _source39.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _953_recursiveGen;
                  bool _954_recOwned;
                  bool _955_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _956_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out493;
                  bool _out494;
                  bool _out495;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out493, out _out494, out _out495, out _out496);
                  _953_recursiveGen = _out493;
                  _954_recOwned = _out494;
                  _955_recErased = _out495;
                  _956_recIdents = _out496;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _953_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _954_recOwned;
                  isErased = _955_recErased;
                  readIdents = _956_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _957___mcc_h526 = _source39.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _958_recursiveGen;
                  bool _959_recOwned;
                  bool _960_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _961_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out497;
                  bool _out498;
                  bool _out499;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out497, out _out498, out _out499, out _out500);
                  _958_recursiveGen = _out497;
                  _959_recOwned = _out498;
                  _960_recErased = _out499;
                  _961_recIdents = _out500;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _958_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _959_recOwned;
                  isErased = _960_recErased;
                  readIdents = _961_recIdents;
                }
              }
            } else if (_source29.is_Array) {
              DAST._IType _962___mcc_h528 = _source29.dtor_element;
              DAST._IType _source41 = _542___mcc_h265;
              if (_source41.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _963___mcc_h532 = _source41.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _964___mcc_h533 = _source41.dtor_typeArgs;
                DAST._IResolvedType _965___mcc_h534 = _source41.dtor_resolved;
                DAST._IResolvedType _source42 = _965___mcc_h534;
                if (_source42.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _966___mcc_h538 = _source42.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _967_recursiveGen;
                    bool _968_recOwned;
                    bool _969_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _970_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out501;
                    bool _out502;
                    bool _out503;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out501, out _out502, out _out503, out _out504);
                    _967_recursiveGen = _out501;
                    _968_recOwned = _out502;
                    _969_recErased = _out503;
                    _970_recIdents = _out504;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _967_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _968_recOwned;
                    isErased = _969_recErased;
                    readIdents = _970_recIdents;
                  }
                } else if (_source42.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _971___mcc_h540 = _source42.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _972_recursiveGen;
                    bool _973_recOwned;
                    bool _974_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _975_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out505;
                    bool _out506;
                    bool _out507;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out505, out _out506, out _out507, out _out508);
                    _972_recursiveGen = _out505;
                    _973_recOwned = _out506;
                    _974_recErased = _out507;
                    _975_recIdents = _out508;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _972_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _973_recOwned;
                    isErased = _974_recErased;
                    readIdents = _975_recIdents;
                  }
                } else {
                  DAST._IType _976___mcc_h542 = _source42.dtor_Newtype_a0;
                  DAST._IType _977_b = _976___mcc_h542;
                  {
                    if (object.Equals(_535_fromTpe, _977_b)) {
                      Dafny.ISequence<Dafny.Rune> _978_recursiveGen;
                      bool _979_recOwned;
                      bool _980_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _981_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out509;
                      bool _out510;
                      bool _out511;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out509, out _out510, out _out511, out _out512);
                      _978_recursiveGen = _out509;
                      _979_recOwned = _out510;
                      _980_recErased = _out511;
                      _981_recIdents = _out512;
                      Dafny.ISequence<Dafny.Rune> _982_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out513;
                      _out513 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _982_rhsType = _out513;
                      Dafny.ISequence<Dafny.Rune> _983_uneraseFn;
                      _983_uneraseFn = ((_979_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _982_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _983_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _978_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _979_recOwned;
                      isErased = false;
                      readIdents = _981_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out514;
                      bool _out515;
                      bool _out516;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _977_b), _977_b, _534_toTpe), selfIdent, @params, mustOwn, out _out514, out _out515, out _out516, out _out517);
                      s = _out514;
                      isOwned = _out515;
                      isErased = _out516;
                      readIdents = _out517;
                    }
                  }
                }
              } else if (_source41.is_Nullable) {
                DAST._IType _984___mcc_h544 = _source41.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _985_recursiveGen;
                  bool _986_recOwned;
                  bool _987_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _988_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out518;
                  bool _out519;
                  bool _out520;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out518, out _out519, out _out520, out _out521);
                  _985_recursiveGen = _out518;
                  _986_recOwned = _out519;
                  _987_recErased = _out520;
                  _988_recIdents = _out521;
                  if (!(_986_recOwned)) {
                    _985_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_985_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _985_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _987_recErased;
                  readIdents = _988_recIdents;
                }
              } else if (_source41.is_Tuple) {
                Dafny.ISequence<DAST._IType> _989___mcc_h546 = _source41.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _990_recursiveGen;
                  bool _991_recOwned;
                  bool _992_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _993_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out522;
                  bool _out523;
                  bool _out524;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out522, out _out523, out _out524, out _out525);
                  _990_recursiveGen = _out522;
                  _991_recOwned = _out523;
                  _992_recErased = _out524;
                  _993_recIdents = _out525;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _990_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _991_recOwned;
                  isErased = _992_recErased;
                  readIdents = _993_recIdents;
                }
              } else if (_source41.is_Array) {
                DAST._IType _994___mcc_h548 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _995_recursiveGen;
                  bool _996_recOwned;
                  bool _997_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _998_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out526;
                  bool _out527;
                  bool _out528;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out526, out _out527, out _out528, out _out529);
                  _995_recursiveGen = _out526;
                  _996_recOwned = _out527;
                  _997_recErased = _out528;
                  _998_recIdents = _out529;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _995_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _996_recOwned;
                  isErased = _997_recErased;
                  readIdents = _998_recIdents;
                }
              } else if (_source41.is_Seq) {
                DAST._IType _999___mcc_h550 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1000_recursiveGen;
                  bool _1001_recOwned;
                  bool _1002_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1003_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out530;
                  bool _out531;
                  bool _out532;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out530, out _out531, out _out532, out _out533);
                  _1000_recursiveGen = _out530;
                  _1001_recOwned = _out531;
                  _1002_recErased = _out532;
                  _1003_recIdents = _out533;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1000_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1001_recOwned;
                  isErased = _1002_recErased;
                  readIdents = _1003_recIdents;
                }
              } else if (_source41.is_Set) {
                DAST._IType _1004___mcc_h552 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1005_recursiveGen;
                  bool _1006_recOwned;
                  bool _1007_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1008_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out534;
                  bool _out535;
                  bool _out536;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out537;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out534, out _out535, out _out536, out _out537);
                  _1005_recursiveGen = _out534;
                  _1006_recOwned = _out535;
                  _1007_recErased = _out536;
                  _1008_recIdents = _out537;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1005_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1006_recOwned;
                  isErased = _1007_recErased;
                  readIdents = _1008_recIdents;
                }
              } else if (_source41.is_Multiset) {
                DAST._IType _1009___mcc_h554 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1010_recursiveGen;
                  bool _1011_recOwned;
                  bool _1012_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1013_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out538;
                  bool _out539;
                  bool _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out538, out _out539, out _out540, out _out541);
                  _1010_recursiveGen = _out538;
                  _1011_recOwned = _out539;
                  _1012_recErased = _out540;
                  _1013_recIdents = _out541;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1010_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1011_recOwned;
                  isErased = _1012_recErased;
                  readIdents = _1013_recIdents;
                }
              } else if (_source41.is_Map) {
                DAST._IType _1014___mcc_h556 = _source41.dtor_key;
                DAST._IType _1015___mcc_h557 = _source41.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1016_recursiveGen;
                  bool _1017_recOwned;
                  bool _1018_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1019_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out542;
                  bool _out543;
                  bool _out544;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out542, out _out543, out _out544, out _out545);
                  _1016_recursiveGen = _out542;
                  _1017_recOwned = _out543;
                  _1018_recErased = _out544;
                  _1019_recIdents = _out545;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1016_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1017_recOwned;
                  isErased = _1018_recErased;
                  readIdents = _1019_recIdents;
                }
              } else if (_source41.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1020___mcc_h560 = _source41.dtor_args;
                DAST._IType _1021___mcc_h561 = _source41.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1022_recursiveGen;
                  bool _1023_recOwned;
                  bool _1024_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1025_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out546;
                  bool _out547;
                  bool _out548;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out546, out _out547, out _out548, out _out549);
                  _1022_recursiveGen = _out546;
                  _1023_recOwned = _out547;
                  _1024_recErased = _out548;
                  _1025_recIdents = _out549;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1022_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1023_recOwned;
                  isErased = _1024_recErased;
                  readIdents = _1025_recIdents;
                }
              } else if (_source41.is_Primitive) {
                DAST._IPrimitive _1026___mcc_h564 = _source41.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1027_recursiveGen;
                  bool _1028_recOwned;
                  bool _1029_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1030_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out550;
                  bool _out551;
                  bool _out552;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out550, out _out551, out _out552, out _out553);
                  _1027_recursiveGen = _out550;
                  _1028_recOwned = _out551;
                  _1029_recErased = _out552;
                  _1030_recIdents = _out553;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1027_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1028_recOwned;
                  isErased = _1029_recErased;
                  readIdents = _1030_recIdents;
                }
              } else if (_source41.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1031___mcc_h566 = _source41.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1032_recursiveGen;
                  bool _1033_recOwned;
                  bool _1034_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1035_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out554;
                  bool _out555;
                  bool _out556;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out554, out _out555, out _out556, out _out557);
                  _1032_recursiveGen = _out554;
                  _1033_recOwned = _out555;
                  _1034_recErased = _out556;
                  _1035_recIdents = _out557;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1032_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1033_recOwned;
                  isErased = _1034_recErased;
                  readIdents = _1035_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1036___mcc_h568 = _source41.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1037_recursiveGen;
                  bool _1038_recOwned;
                  bool _1039_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1040_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out558;
                  bool _out559;
                  bool _out560;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out561;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out558, out _out559, out _out560, out _out561);
                  _1037_recursiveGen = _out558;
                  _1038_recOwned = _out559;
                  _1039_recErased = _out560;
                  _1040_recIdents = _out561;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1037_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1038_recOwned;
                  isErased = _1039_recErased;
                  readIdents = _1040_recIdents;
                }
              }
            } else if (_source29.is_Seq) {
              DAST._IType _1041___mcc_h570 = _source29.dtor_element;
              DAST._IType _source43 = _542___mcc_h265;
              if (_source43.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1042___mcc_h574 = _source43.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1043___mcc_h575 = _source43.dtor_typeArgs;
                DAST._IResolvedType _1044___mcc_h576 = _source43.dtor_resolved;
                DAST._IResolvedType _source44 = _1044___mcc_h576;
                if (_source44.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1045___mcc_h580 = _source44.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1046_recursiveGen;
                    bool _1047_recOwned;
                    bool _1048_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1049_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out562;
                    bool _out563;
                    bool _out564;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out562, out _out563, out _out564, out _out565);
                    _1046_recursiveGen = _out562;
                    _1047_recOwned = _out563;
                    _1048_recErased = _out564;
                    _1049_recIdents = _out565;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1046_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1047_recOwned;
                    isErased = _1048_recErased;
                    readIdents = _1049_recIdents;
                  }
                } else if (_source44.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1050___mcc_h582 = _source44.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1051_recursiveGen;
                    bool _1052_recOwned;
                    bool _1053_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1054_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out566;
                    bool _out567;
                    bool _out568;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out566, out _out567, out _out568, out _out569);
                    _1051_recursiveGen = _out566;
                    _1052_recOwned = _out567;
                    _1053_recErased = _out568;
                    _1054_recIdents = _out569;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1051_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1052_recOwned;
                    isErased = _1053_recErased;
                    readIdents = _1054_recIdents;
                  }
                } else {
                  DAST._IType _1055___mcc_h584 = _source44.dtor_Newtype_a0;
                  DAST._IType _1056_b = _1055___mcc_h584;
                  {
                    if (object.Equals(_535_fromTpe, _1056_b)) {
                      Dafny.ISequence<Dafny.Rune> _1057_recursiveGen;
                      bool _1058_recOwned;
                      bool _1059_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1060_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out570;
                      bool _out571;
                      bool _out572;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out573;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out570, out _out571, out _out572, out _out573);
                      _1057_recursiveGen = _out570;
                      _1058_recOwned = _out571;
                      _1059_recErased = _out572;
                      _1060_recIdents = _out573;
                      Dafny.ISequence<Dafny.Rune> _1061_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out574;
                      _out574 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1061_rhsType = _out574;
                      Dafny.ISequence<Dafny.Rune> _1062_uneraseFn;
                      _1062_uneraseFn = ((_1058_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1061_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1062_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1057_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1058_recOwned;
                      isErased = false;
                      readIdents = _1060_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out575;
                      bool _out576;
                      bool _out577;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1056_b), _1056_b, _534_toTpe), selfIdent, @params, mustOwn, out _out575, out _out576, out _out577, out _out578);
                      s = _out575;
                      isOwned = _out576;
                      isErased = _out577;
                      readIdents = _out578;
                    }
                  }
                }
              } else if (_source43.is_Nullable) {
                DAST._IType _1063___mcc_h586 = _source43.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1064_recursiveGen;
                  bool _1065_recOwned;
                  bool _1066_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1067_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out579;
                  bool _out580;
                  bool _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out579, out _out580, out _out581, out _out582);
                  _1064_recursiveGen = _out579;
                  _1065_recOwned = _out580;
                  _1066_recErased = _out581;
                  _1067_recIdents = _out582;
                  if (!(_1065_recOwned)) {
                    _1064_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1064_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1064_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1066_recErased;
                  readIdents = _1067_recIdents;
                }
              } else if (_source43.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1068___mcc_h588 = _source43.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1069_recursiveGen;
                  bool _1070_recOwned;
                  bool _1071_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1072_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out583;
                  bool _out584;
                  bool _out585;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out583, out _out584, out _out585, out _out586);
                  _1069_recursiveGen = _out583;
                  _1070_recOwned = _out584;
                  _1071_recErased = _out585;
                  _1072_recIdents = _out586;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1069_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1070_recOwned;
                  isErased = _1071_recErased;
                  readIdents = _1072_recIdents;
                }
              } else if (_source43.is_Array) {
                DAST._IType _1073___mcc_h590 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1074_recursiveGen;
                  bool _1075_recOwned;
                  bool _1076_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1077_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out587;
                  bool _out588;
                  bool _out589;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out587, out _out588, out _out589, out _out590);
                  _1074_recursiveGen = _out587;
                  _1075_recOwned = _out588;
                  _1076_recErased = _out589;
                  _1077_recIdents = _out590;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1074_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1075_recOwned;
                  isErased = _1076_recErased;
                  readIdents = _1077_recIdents;
                }
              } else if (_source43.is_Seq) {
                DAST._IType _1078___mcc_h592 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1079_recursiveGen;
                  bool _1080_recOwned;
                  bool _1081_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1082_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out591;
                  bool _out592;
                  bool _out593;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out591, out _out592, out _out593, out _out594);
                  _1079_recursiveGen = _out591;
                  _1080_recOwned = _out592;
                  _1081_recErased = _out593;
                  _1082_recIdents = _out594;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1079_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1080_recOwned;
                  isErased = _1081_recErased;
                  readIdents = _1082_recIdents;
                }
              } else if (_source43.is_Set) {
                DAST._IType _1083___mcc_h594 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1084_recursiveGen;
                  bool _1085_recOwned;
                  bool _1086_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1087_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out595;
                  bool _out596;
                  bool _out597;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out595, out _out596, out _out597, out _out598);
                  _1084_recursiveGen = _out595;
                  _1085_recOwned = _out596;
                  _1086_recErased = _out597;
                  _1087_recIdents = _out598;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1084_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1085_recOwned;
                  isErased = _1086_recErased;
                  readIdents = _1087_recIdents;
                }
              } else if (_source43.is_Multiset) {
                DAST._IType _1088___mcc_h596 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1089_recursiveGen;
                  bool _1090_recOwned;
                  bool _1091_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1092_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out599;
                  bool _out600;
                  bool _out601;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out599, out _out600, out _out601, out _out602);
                  _1089_recursiveGen = _out599;
                  _1090_recOwned = _out600;
                  _1091_recErased = _out601;
                  _1092_recIdents = _out602;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1089_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1090_recOwned;
                  isErased = _1091_recErased;
                  readIdents = _1092_recIdents;
                }
              } else if (_source43.is_Map) {
                DAST._IType _1093___mcc_h598 = _source43.dtor_key;
                DAST._IType _1094___mcc_h599 = _source43.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1095_recursiveGen;
                  bool _1096_recOwned;
                  bool _1097_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1098_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out603;
                  bool _out604;
                  bool _out605;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out603, out _out604, out _out605, out _out606);
                  _1095_recursiveGen = _out603;
                  _1096_recOwned = _out604;
                  _1097_recErased = _out605;
                  _1098_recIdents = _out606;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1095_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1096_recOwned;
                  isErased = _1097_recErased;
                  readIdents = _1098_recIdents;
                }
              } else if (_source43.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1099___mcc_h602 = _source43.dtor_args;
                DAST._IType _1100___mcc_h603 = _source43.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1101_recursiveGen;
                  bool _1102_recOwned;
                  bool _1103_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1104_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out607;
                  bool _out608;
                  bool _out609;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out607, out _out608, out _out609, out _out610);
                  _1101_recursiveGen = _out607;
                  _1102_recOwned = _out608;
                  _1103_recErased = _out609;
                  _1104_recIdents = _out610;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1101_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1102_recOwned;
                  isErased = _1103_recErased;
                  readIdents = _1104_recIdents;
                }
              } else if (_source43.is_Primitive) {
                DAST._IPrimitive _1105___mcc_h606 = _source43.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1106_recursiveGen;
                  bool _1107_recOwned;
                  bool _1108_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1109_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out611;
                  bool _out612;
                  bool _out613;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out611, out _out612, out _out613, out _out614);
                  _1106_recursiveGen = _out611;
                  _1107_recOwned = _out612;
                  _1108_recErased = _out613;
                  _1109_recIdents = _out614;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1106_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1107_recOwned;
                  isErased = _1108_recErased;
                  readIdents = _1109_recIdents;
                }
              } else if (_source43.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1110___mcc_h608 = _source43.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1111_recursiveGen;
                  bool _1112_recOwned;
                  bool _1113_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1114_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out615;
                  bool _out616;
                  bool _out617;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out618;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out615, out _out616, out _out617, out _out618);
                  _1111_recursiveGen = _out615;
                  _1112_recOwned = _out616;
                  _1113_recErased = _out617;
                  _1114_recIdents = _out618;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1111_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1112_recOwned;
                  isErased = _1113_recErased;
                  readIdents = _1114_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1115___mcc_h610 = _source43.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1116_recursiveGen;
                  bool _1117_recOwned;
                  bool _1118_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1119_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out619;
                  bool _out620;
                  bool _out621;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out619, out _out620, out _out621, out _out622);
                  _1116_recursiveGen = _out619;
                  _1117_recOwned = _out620;
                  _1118_recErased = _out621;
                  _1119_recIdents = _out622;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1116_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1117_recOwned;
                  isErased = _1118_recErased;
                  readIdents = _1119_recIdents;
                }
              }
            } else if (_source29.is_Set) {
              DAST._IType _1120___mcc_h612 = _source29.dtor_element;
              DAST._IType _source45 = _542___mcc_h265;
              if (_source45.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1121___mcc_h616 = _source45.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1122___mcc_h617 = _source45.dtor_typeArgs;
                DAST._IResolvedType _1123___mcc_h618 = _source45.dtor_resolved;
                DAST._IResolvedType _source46 = _1123___mcc_h618;
                if (_source46.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1124___mcc_h622 = _source46.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1125_recursiveGen;
                    bool _1126_recOwned;
                    bool _1127_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1128_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out623;
                    bool _out624;
                    bool _out625;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out626;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out623, out _out624, out _out625, out _out626);
                    _1125_recursiveGen = _out623;
                    _1126_recOwned = _out624;
                    _1127_recErased = _out625;
                    _1128_recIdents = _out626;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1125_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1126_recOwned;
                    isErased = _1127_recErased;
                    readIdents = _1128_recIdents;
                  }
                } else if (_source46.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1129___mcc_h624 = _source46.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1130_recursiveGen;
                    bool _1131_recOwned;
                    bool _1132_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1133_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out627;
                    bool _out628;
                    bool _out629;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out627, out _out628, out _out629, out _out630);
                    _1130_recursiveGen = _out627;
                    _1131_recOwned = _out628;
                    _1132_recErased = _out629;
                    _1133_recIdents = _out630;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1130_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1131_recOwned;
                    isErased = _1132_recErased;
                    readIdents = _1133_recIdents;
                  }
                } else {
                  DAST._IType _1134___mcc_h626 = _source46.dtor_Newtype_a0;
                  DAST._IType _1135_b = _1134___mcc_h626;
                  {
                    if (object.Equals(_535_fromTpe, _1135_b)) {
                      Dafny.ISequence<Dafny.Rune> _1136_recursiveGen;
                      bool _1137_recOwned;
                      bool _1138_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1139_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out631;
                      bool _out632;
                      bool _out633;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out631, out _out632, out _out633, out _out634);
                      _1136_recursiveGen = _out631;
                      _1137_recOwned = _out632;
                      _1138_recErased = _out633;
                      _1139_recIdents = _out634;
                      Dafny.ISequence<Dafny.Rune> _1140_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out635;
                      _out635 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1140_rhsType = _out635;
                      Dafny.ISequence<Dafny.Rune> _1141_uneraseFn;
                      _1141_uneraseFn = ((_1137_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1140_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1141_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1136_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1137_recOwned;
                      isErased = false;
                      readIdents = _1139_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out636;
                      bool _out637;
                      bool _out638;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1135_b), _1135_b, _534_toTpe), selfIdent, @params, mustOwn, out _out636, out _out637, out _out638, out _out639);
                      s = _out636;
                      isOwned = _out637;
                      isErased = _out638;
                      readIdents = _out639;
                    }
                  }
                }
              } else if (_source45.is_Nullable) {
                DAST._IType _1142___mcc_h628 = _source45.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1143_recursiveGen;
                  bool _1144_recOwned;
                  bool _1145_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1146_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out640;
                  bool _out641;
                  bool _out642;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out640, out _out641, out _out642, out _out643);
                  _1143_recursiveGen = _out640;
                  _1144_recOwned = _out641;
                  _1145_recErased = _out642;
                  _1146_recIdents = _out643;
                  if (!(_1144_recOwned)) {
                    _1143_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1143_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1143_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1145_recErased;
                  readIdents = _1146_recIdents;
                }
              } else if (_source45.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1147___mcc_h630 = _source45.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1148_recursiveGen;
                  bool _1149_recOwned;
                  bool _1150_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1151_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out644;
                  bool _out645;
                  bool _out646;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out644, out _out645, out _out646, out _out647);
                  _1148_recursiveGen = _out644;
                  _1149_recOwned = _out645;
                  _1150_recErased = _out646;
                  _1151_recIdents = _out647;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1148_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1149_recOwned;
                  isErased = _1150_recErased;
                  readIdents = _1151_recIdents;
                }
              } else if (_source45.is_Array) {
                DAST._IType _1152___mcc_h632 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1153_recursiveGen;
                  bool _1154_recOwned;
                  bool _1155_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1156_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out648;
                  bool _out649;
                  bool _out650;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out651;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out648, out _out649, out _out650, out _out651);
                  _1153_recursiveGen = _out648;
                  _1154_recOwned = _out649;
                  _1155_recErased = _out650;
                  _1156_recIdents = _out651;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1153_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1154_recOwned;
                  isErased = _1155_recErased;
                  readIdents = _1156_recIdents;
                }
              } else if (_source45.is_Seq) {
                DAST._IType _1157___mcc_h634 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1158_recursiveGen;
                  bool _1159_recOwned;
                  bool _1160_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1161_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out652;
                  bool _out653;
                  bool _out654;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out652, out _out653, out _out654, out _out655);
                  _1158_recursiveGen = _out652;
                  _1159_recOwned = _out653;
                  _1160_recErased = _out654;
                  _1161_recIdents = _out655;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1158_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1159_recOwned;
                  isErased = _1160_recErased;
                  readIdents = _1161_recIdents;
                }
              } else if (_source45.is_Set) {
                DAST._IType _1162___mcc_h636 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1163_recursiveGen;
                  bool _1164_recOwned;
                  bool _1165_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1166_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out656;
                  bool _out657;
                  bool _out658;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out659;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out656, out _out657, out _out658, out _out659);
                  _1163_recursiveGen = _out656;
                  _1164_recOwned = _out657;
                  _1165_recErased = _out658;
                  _1166_recIdents = _out659;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1163_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1164_recOwned;
                  isErased = _1165_recErased;
                  readIdents = _1166_recIdents;
                }
              } else if (_source45.is_Multiset) {
                DAST._IType _1167___mcc_h638 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1168_recursiveGen;
                  bool _1169_recOwned;
                  bool _1170_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1171_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out660;
                  bool _out661;
                  bool _out662;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out660, out _out661, out _out662, out _out663);
                  _1168_recursiveGen = _out660;
                  _1169_recOwned = _out661;
                  _1170_recErased = _out662;
                  _1171_recIdents = _out663;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1168_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1169_recOwned;
                  isErased = _1170_recErased;
                  readIdents = _1171_recIdents;
                }
              } else if (_source45.is_Map) {
                DAST._IType _1172___mcc_h640 = _source45.dtor_key;
                DAST._IType _1173___mcc_h641 = _source45.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1174_recursiveGen;
                  bool _1175_recOwned;
                  bool _1176_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1177_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out664;
                  bool _out665;
                  bool _out666;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out664, out _out665, out _out666, out _out667);
                  _1174_recursiveGen = _out664;
                  _1175_recOwned = _out665;
                  _1176_recErased = _out666;
                  _1177_recIdents = _out667;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1174_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1175_recOwned;
                  isErased = _1176_recErased;
                  readIdents = _1177_recIdents;
                }
              } else if (_source45.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1178___mcc_h644 = _source45.dtor_args;
                DAST._IType _1179___mcc_h645 = _source45.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1180_recursiveGen;
                  bool _1181_recOwned;
                  bool _1182_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1183_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out668;
                  bool _out669;
                  bool _out670;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out671;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out668, out _out669, out _out670, out _out671);
                  _1180_recursiveGen = _out668;
                  _1181_recOwned = _out669;
                  _1182_recErased = _out670;
                  _1183_recIdents = _out671;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1180_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1181_recOwned;
                  isErased = _1182_recErased;
                  readIdents = _1183_recIdents;
                }
              } else if (_source45.is_Primitive) {
                DAST._IPrimitive _1184___mcc_h648 = _source45.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1185_recursiveGen;
                  bool _1186_recOwned;
                  bool _1187_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1188_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out672;
                  bool _out673;
                  bool _out674;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out675;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out672, out _out673, out _out674, out _out675);
                  _1185_recursiveGen = _out672;
                  _1186_recOwned = _out673;
                  _1187_recErased = _out674;
                  _1188_recIdents = _out675;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1185_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1186_recOwned;
                  isErased = _1187_recErased;
                  readIdents = _1188_recIdents;
                }
              } else if (_source45.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1189___mcc_h650 = _source45.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1190_recursiveGen;
                  bool _1191_recOwned;
                  bool _1192_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1193_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out676;
                  bool _out677;
                  bool _out678;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out676, out _out677, out _out678, out _out679);
                  _1190_recursiveGen = _out676;
                  _1191_recOwned = _out677;
                  _1192_recErased = _out678;
                  _1193_recIdents = _out679;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1190_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1191_recOwned;
                  isErased = _1192_recErased;
                  readIdents = _1193_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1194___mcc_h652 = _source45.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1195_recursiveGen;
                  bool _1196_recOwned;
                  bool _1197_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1198_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out680;
                  bool _out681;
                  bool _out682;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out683;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out680, out _out681, out _out682, out _out683);
                  _1195_recursiveGen = _out680;
                  _1196_recOwned = _out681;
                  _1197_recErased = _out682;
                  _1198_recIdents = _out683;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1195_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1196_recOwned;
                  isErased = _1197_recErased;
                  readIdents = _1198_recIdents;
                }
              }
            } else if (_source29.is_Multiset) {
              DAST._IType _1199___mcc_h654 = _source29.dtor_element;
              DAST._IType _source47 = _542___mcc_h265;
              if (_source47.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1200___mcc_h658 = _source47.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1201___mcc_h659 = _source47.dtor_typeArgs;
                DAST._IResolvedType _1202___mcc_h660 = _source47.dtor_resolved;
                DAST._IResolvedType _source48 = _1202___mcc_h660;
                if (_source48.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1203___mcc_h664 = _source48.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1204_recursiveGen;
                    bool _1205_recOwned;
                    bool _1206_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1207_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out684;
                    bool _out685;
                    bool _out686;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out687;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out684, out _out685, out _out686, out _out687);
                    _1204_recursiveGen = _out684;
                    _1205_recOwned = _out685;
                    _1206_recErased = _out686;
                    _1207_recIdents = _out687;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1204_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1205_recOwned;
                    isErased = _1206_recErased;
                    readIdents = _1207_recIdents;
                  }
                } else if (_source48.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1208___mcc_h666 = _source48.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1209_recursiveGen;
                    bool _1210_recOwned;
                    bool _1211_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1212_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out688;
                    bool _out689;
                    bool _out690;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out688, out _out689, out _out690, out _out691);
                    _1209_recursiveGen = _out688;
                    _1210_recOwned = _out689;
                    _1211_recErased = _out690;
                    _1212_recIdents = _out691;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1209_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1210_recOwned;
                    isErased = _1211_recErased;
                    readIdents = _1212_recIdents;
                  }
                } else {
                  DAST._IType _1213___mcc_h668 = _source48.dtor_Newtype_a0;
                  DAST._IType _1214_b = _1213___mcc_h668;
                  {
                    if (object.Equals(_535_fromTpe, _1214_b)) {
                      Dafny.ISequence<Dafny.Rune> _1215_recursiveGen;
                      bool _1216_recOwned;
                      bool _1217_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1218_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out692;
                      bool _out693;
                      bool _out694;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out695;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out692, out _out693, out _out694, out _out695);
                      _1215_recursiveGen = _out692;
                      _1216_recOwned = _out693;
                      _1217_recErased = _out694;
                      _1218_recIdents = _out695;
                      Dafny.ISequence<Dafny.Rune> _1219_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out696;
                      _out696 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1219_rhsType = _out696;
                      Dafny.ISequence<Dafny.Rune> _1220_uneraseFn;
                      _1220_uneraseFn = ((_1216_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1219_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1220_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1215_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1216_recOwned;
                      isErased = false;
                      readIdents = _1218_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out697;
                      bool _out698;
                      bool _out699;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1214_b), _1214_b, _534_toTpe), selfIdent, @params, mustOwn, out _out697, out _out698, out _out699, out _out700);
                      s = _out697;
                      isOwned = _out698;
                      isErased = _out699;
                      readIdents = _out700;
                    }
                  }
                }
              } else if (_source47.is_Nullable) {
                DAST._IType _1221___mcc_h670 = _source47.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1222_recursiveGen;
                  bool _1223_recOwned;
                  bool _1224_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1225_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out701;
                  bool _out702;
                  bool _out703;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out704;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out701, out _out702, out _out703, out _out704);
                  _1222_recursiveGen = _out701;
                  _1223_recOwned = _out702;
                  _1224_recErased = _out703;
                  _1225_recIdents = _out704;
                  if (!(_1223_recOwned)) {
                    _1222_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1222_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1222_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1224_recErased;
                  readIdents = _1225_recIdents;
                }
              } else if (_source47.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1226___mcc_h672 = _source47.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1227_recursiveGen;
                  bool _1228_recOwned;
                  bool _1229_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1230_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out705;
                  bool _out706;
                  bool _out707;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out708;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out705, out _out706, out _out707, out _out708);
                  _1227_recursiveGen = _out705;
                  _1228_recOwned = _out706;
                  _1229_recErased = _out707;
                  _1230_recIdents = _out708;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1227_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1228_recOwned;
                  isErased = _1229_recErased;
                  readIdents = _1230_recIdents;
                }
              } else if (_source47.is_Array) {
                DAST._IType _1231___mcc_h674 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1232_recursiveGen;
                  bool _1233_recOwned;
                  bool _1234_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1235_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out709;
                  bool _out710;
                  bool _out711;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out709, out _out710, out _out711, out _out712);
                  _1232_recursiveGen = _out709;
                  _1233_recOwned = _out710;
                  _1234_recErased = _out711;
                  _1235_recIdents = _out712;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1232_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1233_recOwned;
                  isErased = _1234_recErased;
                  readIdents = _1235_recIdents;
                }
              } else if (_source47.is_Seq) {
                DAST._IType _1236___mcc_h676 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1237_recursiveGen;
                  bool _1238_recOwned;
                  bool _1239_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1240_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out713;
                  bool _out714;
                  bool _out715;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out716;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out713, out _out714, out _out715, out _out716);
                  _1237_recursiveGen = _out713;
                  _1238_recOwned = _out714;
                  _1239_recErased = _out715;
                  _1240_recIdents = _out716;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1237_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1238_recOwned;
                  isErased = _1239_recErased;
                  readIdents = _1240_recIdents;
                }
              } else if (_source47.is_Set) {
                DAST._IType _1241___mcc_h678 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1242_recursiveGen;
                  bool _1243_recOwned;
                  bool _1244_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1245_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out717;
                  bool _out718;
                  bool _out719;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out720;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out717, out _out718, out _out719, out _out720);
                  _1242_recursiveGen = _out717;
                  _1243_recOwned = _out718;
                  _1244_recErased = _out719;
                  _1245_recIdents = _out720;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1242_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1243_recOwned;
                  isErased = _1244_recErased;
                  readIdents = _1245_recIdents;
                }
              } else if (_source47.is_Multiset) {
                DAST._IType _1246___mcc_h680 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1247_recursiveGen;
                  bool _1248_recOwned;
                  bool _1249_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1250_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out721;
                  bool _out722;
                  bool _out723;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out721, out _out722, out _out723, out _out724);
                  _1247_recursiveGen = _out721;
                  _1248_recOwned = _out722;
                  _1249_recErased = _out723;
                  _1250_recIdents = _out724;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1247_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1248_recOwned;
                  isErased = _1249_recErased;
                  readIdents = _1250_recIdents;
                }
              } else if (_source47.is_Map) {
                DAST._IType _1251___mcc_h682 = _source47.dtor_key;
                DAST._IType _1252___mcc_h683 = _source47.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1253_recursiveGen;
                  bool _1254_recOwned;
                  bool _1255_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1256_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out725;
                  bool _out726;
                  bool _out727;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out728;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out725, out _out726, out _out727, out _out728);
                  _1253_recursiveGen = _out725;
                  _1254_recOwned = _out726;
                  _1255_recErased = _out727;
                  _1256_recIdents = _out728;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1253_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1254_recOwned;
                  isErased = _1255_recErased;
                  readIdents = _1256_recIdents;
                }
              } else if (_source47.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1257___mcc_h686 = _source47.dtor_args;
                DAST._IType _1258___mcc_h687 = _source47.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1259_recursiveGen;
                  bool _1260_recOwned;
                  bool _1261_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1262_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out729;
                  bool _out730;
                  bool _out731;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out732;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out729, out _out730, out _out731, out _out732);
                  _1259_recursiveGen = _out729;
                  _1260_recOwned = _out730;
                  _1261_recErased = _out731;
                  _1262_recIdents = _out732;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1259_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1260_recOwned;
                  isErased = _1261_recErased;
                  readIdents = _1262_recIdents;
                }
              } else if (_source47.is_Primitive) {
                DAST._IPrimitive _1263___mcc_h690 = _source47.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1264_recursiveGen;
                  bool _1265_recOwned;
                  bool _1266_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1267_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out733;
                  bool _out734;
                  bool _out735;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out733, out _out734, out _out735, out _out736);
                  _1264_recursiveGen = _out733;
                  _1265_recOwned = _out734;
                  _1266_recErased = _out735;
                  _1267_recIdents = _out736;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1264_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1265_recOwned;
                  isErased = _1266_recErased;
                  readIdents = _1267_recIdents;
                }
              } else if (_source47.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1268___mcc_h692 = _source47.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1269_recursiveGen;
                  bool _1270_recOwned;
                  bool _1271_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1272_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out737;
                  bool _out738;
                  bool _out739;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out740;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out737, out _out738, out _out739, out _out740);
                  _1269_recursiveGen = _out737;
                  _1270_recOwned = _out738;
                  _1271_recErased = _out739;
                  _1272_recIdents = _out740;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1269_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1270_recOwned;
                  isErased = _1271_recErased;
                  readIdents = _1272_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1273___mcc_h694 = _source47.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1274_recursiveGen;
                  bool _1275_recOwned;
                  bool _1276_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1277_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out741;
                  bool _out742;
                  bool _out743;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out744;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out741, out _out742, out _out743, out _out744);
                  _1274_recursiveGen = _out741;
                  _1275_recOwned = _out742;
                  _1276_recErased = _out743;
                  _1277_recIdents = _out744;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1274_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1275_recOwned;
                  isErased = _1276_recErased;
                  readIdents = _1277_recIdents;
                }
              }
            } else if (_source29.is_Map) {
              DAST._IType _1278___mcc_h696 = _source29.dtor_key;
              DAST._IType _1279___mcc_h697 = _source29.dtor_value;
              DAST._IType _source49 = _542___mcc_h265;
              if (_source49.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1280___mcc_h704 = _source49.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1281___mcc_h705 = _source49.dtor_typeArgs;
                DAST._IResolvedType _1282___mcc_h706 = _source49.dtor_resolved;
                DAST._IResolvedType _source50 = _1282___mcc_h706;
                if (_source50.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1283___mcc_h710 = _source50.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1284_recursiveGen;
                    bool _1285_recOwned;
                    bool _1286_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1287_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out745;
                    bool _out746;
                    bool _out747;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out745, out _out746, out _out747, out _out748);
                    _1284_recursiveGen = _out745;
                    _1285_recOwned = _out746;
                    _1286_recErased = _out747;
                    _1287_recIdents = _out748;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1284_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1285_recOwned;
                    isErased = _1286_recErased;
                    readIdents = _1287_recIdents;
                  }
                } else if (_source50.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1288___mcc_h712 = _source50.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1289_recursiveGen;
                    bool _1290_recOwned;
                    bool _1291_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1292_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out749;
                    bool _out750;
                    bool _out751;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out752;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out749, out _out750, out _out751, out _out752);
                    _1289_recursiveGen = _out749;
                    _1290_recOwned = _out750;
                    _1291_recErased = _out751;
                    _1292_recIdents = _out752;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1289_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1290_recOwned;
                    isErased = _1291_recErased;
                    readIdents = _1292_recIdents;
                  }
                } else {
                  DAST._IType _1293___mcc_h714 = _source50.dtor_Newtype_a0;
                  DAST._IType _1294_b = _1293___mcc_h714;
                  {
                    if (object.Equals(_535_fromTpe, _1294_b)) {
                      Dafny.ISequence<Dafny.Rune> _1295_recursiveGen;
                      bool _1296_recOwned;
                      bool _1297_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1298_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out753;
                      bool _out754;
                      bool _out755;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out756;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out753, out _out754, out _out755, out _out756);
                      _1295_recursiveGen = _out753;
                      _1296_recOwned = _out754;
                      _1297_recErased = _out755;
                      _1298_recIdents = _out756;
                      Dafny.ISequence<Dafny.Rune> _1299_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out757;
                      _out757 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1299_rhsType = _out757;
                      Dafny.ISequence<Dafny.Rune> _1300_uneraseFn;
                      _1300_uneraseFn = ((_1296_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1299_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1300_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1295_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1296_recOwned;
                      isErased = false;
                      readIdents = _1298_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out758;
                      bool _out759;
                      bool _out760;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out761;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1294_b), _1294_b, _534_toTpe), selfIdent, @params, mustOwn, out _out758, out _out759, out _out760, out _out761);
                      s = _out758;
                      isOwned = _out759;
                      isErased = _out760;
                      readIdents = _out761;
                    }
                  }
                }
              } else if (_source49.is_Nullable) {
                DAST._IType _1301___mcc_h716 = _source49.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1302_recursiveGen;
                  bool _1303_recOwned;
                  bool _1304_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1305_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out762;
                  bool _out763;
                  bool _out764;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out762, out _out763, out _out764, out _out765);
                  _1302_recursiveGen = _out762;
                  _1303_recOwned = _out763;
                  _1304_recErased = _out764;
                  _1305_recIdents = _out765;
                  if (!(_1303_recOwned)) {
                    _1302_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1302_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1302_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1304_recErased;
                  readIdents = _1305_recIdents;
                }
              } else if (_source49.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1306___mcc_h718 = _source49.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1307_recursiveGen;
                  bool _1308_recOwned;
                  bool _1309_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1310_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out766;
                  bool _out767;
                  bool _out768;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out766, out _out767, out _out768, out _out769);
                  _1307_recursiveGen = _out766;
                  _1308_recOwned = _out767;
                  _1309_recErased = _out768;
                  _1310_recIdents = _out769;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1307_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1308_recOwned;
                  isErased = _1309_recErased;
                  readIdents = _1310_recIdents;
                }
              } else if (_source49.is_Array) {
                DAST._IType _1311___mcc_h720 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1312_recursiveGen;
                  bool _1313_recOwned;
                  bool _1314_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1315_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out770;
                  bool _out771;
                  bool _out772;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out773;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out770, out _out771, out _out772, out _out773);
                  _1312_recursiveGen = _out770;
                  _1313_recOwned = _out771;
                  _1314_recErased = _out772;
                  _1315_recIdents = _out773;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1312_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1313_recOwned;
                  isErased = _1314_recErased;
                  readIdents = _1315_recIdents;
                }
              } else if (_source49.is_Seq) {
                DAST._IType _1316___mcc_h722 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1317_recursiveGen;
                  bool _1318_recOwned;
                  bool _1319_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1320_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out774;
                  bool _out775;
                  bool _out776;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out777;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out774, out _out775, out _out776, out _out777);
                  _1317_recursiveGen = _out774;
                  _1318_recOwned = _out775;
                  _1319_recErased = _out776;
                  _1320_recIdents = _out777;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1317_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1318_recOwned;
                  isErased = _1319_recErased;
                  readIdents = _1320_recIdents;
                }
              } else if (_source49.is_Set) {
                DAST._IType _1321___mcc_h724 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1322_recursiveGen;
                  bool _1323_recOwned;
                  bool _1324_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1325_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out778;
                  bool _out779;
                  bool _out780;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out778, out _out779, out _out780, out _out781);
                  _1322_recursiveGen = _out778;
                  _1323_recOwned = _out779;
                  _1324_recErased = _out780;
                  _1325_recIdents = _out781;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1322_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1323_recOwned;
                  isErased = _1324_recErased;
                  readIdents = _1325_recIdents;
                }
              } else if (_source49.is_Multiset) {
                DAST._IType _1326___mcc_h726 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1327_recursiveGen;
                  bool _1328_recOwned;
                  bool _1329_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1330_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out782;
                  bool _out783;
                  bool _out784;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out785;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out782, out _out783, out _out784, out _out785);
                  _1327_recursiveGen = _out782;
                  _1328_recOwned = _out783;
                  _1329_recErased = _out784;
                  _1330_recIdents = _out785;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1327_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1328_recOwned;
                  isErased = _1329_recErased;
                  readIdents = _1330_recIdents;
                }
              } else if (_source49.is_Map) {
                DAST._IType _1331___mcc_h728 = _source49.dtor_key;
                DAST._IType _1332___mcc_h729 = _source49.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1333_recursiveGen;
                  bool _1334_recOwned;
                  bool _1335_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1336_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out786;
                  bool _out787;
                  bool _out788;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out789;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out786, out _out787, out _out788, out _out789);
                  _1333_recursiveGen = _out786;
                  _1334_recOwned = _out787;
                  _1335_recErased = _out788;
                  _1336_recIdents = _out789;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1333_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1334_recOwned;
                  isErased = _1335_recErased;
                  readIdents = _1336_recIdents;
                }
              } else if (_source49.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1337___mcc_h732 = _source49.dtor_args;
                DAST._IType _1338___mcc_h733 = _source49.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1339_recursiveGen;
                  bool _1340_recOwned;
                  bool _1341_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1342_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out790;
                  bool _out791;
                  bool _out792;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out790, out _out791, out _out792, out _out793);
                  _1339_recursiveGen = _out790;
                  _1340_recOwned = _out791;
                  _1341_recErased = _out792;
                  _1342_recIdents = _out793;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1339_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1340_recOwned;
                  isErased = _1341_recErased;
                  readIdents = _1342_recIdents;
                }
              } else if (_source49.is_Primitive) {
                DAST._IPrimitive _1343___mcc_h736 = _source49.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1344_recursiveGen;
                  bool _1345_recOwned;
                  bool _1346_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1347_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out794;
                  bool _out795;
                  bool _out796;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out797;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out794, out _out795, out _out796, out _out797);
                  _1344_recursiveGen = _out794;
                  _1345_recOwned = _out795;
                  _1346_recErased = _out796;
                  _1347_recIdents = _out797;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1344_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1345_recOwned;
                  isErased = _1346_recErased;
                  readIdents = _1347_recIdents;
                }
              } else if (_source49.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1348___mcc_h738 = _source49.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1349_recursiveGen;
                  bool _1350_recOwned;
                  bool _1351_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1352_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out798;
                  bool _out799;
                  bool _out800;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out801;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out798, out _out799, out _out800, out _out801);
                  _1349_recursiveGen = _out798;
                  _1350_recOwned = _out799;
                  _1351_recErased = _out800;
                  _1352_recIdents = _out801;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1349_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1350_recOwned;
                  isErased = _1351_recErased;
                  readIdents = _1352_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1353___mcc_h740 = _source49.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1354_recursiveGen;
                  bool _1355_recOwned;
                  bool _1356_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1357_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out802;
                  bool _out803;
                  bool _out804;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out802, out _out803, out _out804, out _out805);
                  _1354_recursiveGen = _out802;
                  _1355_recOwned = _out803;
                  _1356_recErased = _out804;
                  _1357_recIdents = _out805;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1354_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1355_recOwned;
                  isErased = _1356_recErased;
                  readIdents = _1357_recIdents;
                }
              }
            } else if (_source29.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1358___mcc_h742 = _source29.dtor_args;
              DAST._IType _1359___mcc_h743 = _source29.dtor_result;
              DAST._IType _source51 = _542___mcc_h265;
              if (_source51.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1360___mcc_h750 = _source51.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1361___mcc_h751 = _source51.dtor_typeArgs;
                DAST._IResolvedType _1362___mcc_h752 = _source51.dtor_resolved;
                DAST._IResolvedType _source52 = _1362___mcc_h752;
                if (_source52.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1363___mcc_h756 = _source52.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1364_recursiveGen;
                    bool _1365_recOwned;
                    bool _1366_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1367_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out806;
                    bool _out807;
                    bool _out808;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out809;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out806, out _out807, out _out808, out _out809);
                    _1364_recursiveGen = _out806;
                    _1365_recOwned = _out807;
                    _1366_recErased = _out808;
                    _1367_recIdents = _out809;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1364_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1365_recOwned;
                    isErased = _1366_recErased;
                    readIdents = _1367_recIdents;
                  }
                } else if (_source52.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1368___mcc_h758 = _source52.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1369_recursiveGen;
                    bool _1370_recOwned;
                    bool _1371_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1372_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out810;
                    bool _out811;
                    bool _out812;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out813;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out810, out _out811, out _out812, out _out813);
                    _1369_recursiveGen = _out810;
                    _1370_recOwned = _out811;
                    _1371_recErased = _out812;
                    _1372_recIdents = _out813;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1369_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1370_recOwned;
                    isErased = _1371_recErased;
                    readIdents = _1372_recIdents;
                  }
                } else {
                  DAST._IType _1373___mcc_h760 = _source52.dtor_Newtype_a0;
                  DAST._IType _1374_b = _1373___mcc_h760;
                  {
                    if (object.Equals(_535_fromTpe, _1374_b)) {
                      Dafny.ISequence<Dafny.Rune> _1375_recursiveGen;
                      bool _1376_recOwned;
                      bool _1377_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1378_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out814;
                      bool _out815;
                      bool _out816;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out814, out _out815, out _out816, out _out817);
                      _1375_recursiveGen = _out814;
                      _1376_recOwned = _out815;
                      _1377_recErased = _out816;
                      _1378_recIdents = _out817;
                      Dafny.ISequence<Dafny.Rune> _1379_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out818;
                      _out818 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1379_rhsType = _out818;
                      Dafny.ISequence<Dafny.Rune> _1380_uneraseFn;
                      _1380_uneraseFn = ((_1376_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1379_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1380_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1375_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1376_recOwned;
                      isErased = false;
                      readIdents = _1378_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out819;
                      bool _out820;
                      bool _out821;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out822;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1374_b), _1374_b, _534_toTpe), selfIdent, @params, mustOwn, out _out819, out _out820, out _out821, out _out822);
                      s = _out819;
                      isOwned = _out820;
                      isErased = _out821;
                      readIdents = _out822;
                    }
                  }
                }
              } else if (_source51.is_Nullable) {
                DAST._IType _1381___mcc_h762 = _source51.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1382_recursiveGen;
                  bool _1383_recOwned;
                  bool _1384_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1385_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out823;
                  bool _out824;
                  bool _out825;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out823, out _out824, out _out825, out _out826);
                  _1382_recursiveGen = _out823;
                  _1383_recOwned = _out824;
                  _1384_recErased = _out825;
                  _1385_recIdents = _out826;
                  if (!(_1383_recOwned)) {
                    _1382_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1382_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1382_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1384_recErased;
                  readIdents = _1385_recIdents;
                }
              } else if (_source51.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1386___mcc_h764 = _source51.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1387_recursiveGen;
                  bool _1388_recOwned;
                  bool _1389_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1390_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out827;
                  bool _out828;
                  bool _out829;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out830;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out827, out _out828, out _out829, out _out830);
                  _1387_recursiveGen = _out827;
                  _1388_recOwned = _out828;
                  _1389_recErased = _out829;
                  _1390_recIdents = _out830;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1387_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1388_recOwned;
                  isErased = _1389_recErased;
                  readIdents = _1390_recIdents;
                }
              } else if (_source51.is_Array) {
                DAST._IType _1391___mcc_h766 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1392_recursiveGen;
                  bool _1393_recOwned;
                  bool _1394_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1395_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out831;
                  bool _out832;
                  bool _out833;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out834;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out831, out _out832, out _out833, out _out834);
                  _1392_recursiveGen = _out831;
                  _1393_recOwned = _out832;
                  _1394_recErased = _out833;
                  _1395_recIdents = _out834;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1392_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1393_recOwned;
                  isErased = _1394_recErased;
                  readIdents = _1395_recIdents;
                }
              } else if (_source51.is_Seq) {
                DAST._IType _1396___mcc_h768 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1397_recursiveGen;
                  bool _1398_recOwned;
                  bool _1399_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1400_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out835;
                  bool _out836;
                  bool _out837;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out835, out _out836, out _out837, out _out838);
                  _1397_recursiveGen = _out835;
                  _1398_recOwned = _out836;
                  _1399_recErased = _out837;
                  _1400_recIdents = _out838;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1397_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1398_recOwned;
                  isErased = _1399_recErased;
                  readIdents = _1400_recIdents;
                }
              } else if (_source51.is_Set) {
                DAST._IType _1401___mcc_h770 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1402_recursiveGen;
                  bool _1403_recOwned;
                  bool _1404_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1405_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out839;
                  bool _out840;
                  bool _out841;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out842;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out839, out _out840, out _out841, out _out842);
                  _1402_recursiveGen = _out839;
                  _1403_recOwned = _out840;
                  _1404_recErased = _out841;
                  _1405_recIdents = _out842;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1402_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1403_recOwned;
                  isErased = _1404_recErased;
                  readIdents = _1405_recIdents;
                }
              } else if (_source51.is_Multiset) {
                DAST._IType _1406___mcc_h772 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1407_recursiveGen;
                  bool _1408_recOwned;
                  bool _1409_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1410_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out843;
                  bool _out844;
                  bool _out845;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out846;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out843, out _out844, out _out845, out _out846);
                  _1407_recursiveGen = _out843;
                  _1408_recOwned = _out844;
                  _1409_recErased = _out845;
                  _1410_recIdents = _out846;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1407_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1408_recOwned;
                  isErased = _1409_recErased;
                  readIdents = _1410_recIdents;
                }
              } else if (_source51.is_Map) {
                DAST._IType _1411___mcc_h774 = _source51.dtor_key;
                DAST._IType _1412___mcc_h775 = _source51.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1413_recursiveGen;
                  bool _1414_recOwned;
                  bool _1415_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1416_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out847;
                  bool _out848;
                  bool _out849;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out847, out _out848, out _out849, out _out850);
                  _1413_recursiveGen = _out847;
                  _1414_recOwned = _out848;
                  _1415_recErased = _out849;
                  _1416_recIdents = _out850;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1413_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1414_recOwned;
                  isErased = _1415_recErased;
                  readIdents = _1416_recIdents;
                }
              } else if (_source51.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1417___mcc_h778 = _source51.dtor_args;
                DAST._IType _1418___mcc_h779 = _source51.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1419_recursiveGen;
                  bool _1420_recOwned;
                  bool _1421_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1422_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out851;
                  bool _out852;
                  bool _out853;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out854;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out851, out _out852, out _out853, out _out854);
                  _1419_recursiveGen = _out851;
                  _1420_recOwned = _out852;
                  _1421_recErased = _out853;
                  _1422_recIdents = _out854;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1419_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1420_recOwned;
                  isErased = _1421_recErased;
                  readIdents = _1422_recIdents;
                }
              } else if (_source51.is_Primitive) {
                DAST._IPrimitive _1423___mcc_h782 = _source51.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1424_recursiveGen;
                  bool _1425_recOwned;
                  bool _1426_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1427_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out855;
                  bool _out856;
                  bool _out857;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out858;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out855, out _out856, out _out857, out _out858);
                  _1424_recursiveGen = _out855;
                  _1425_recOwned = _out856;
                  _1426_recErased = _out857;
                  _1427_recIdents = _out858;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1424_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1425_recOwned;
                  isErased = _1426_recErased;
                  readIdents = _1427_recIdents;
                }
              } else if (_source51.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1428___mcc_h784 = _source51.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1429_recursiveGen;
                  bool _1430_recOwned;
                  bool _1431_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1432_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out859;
                  bool _out860;
                  bool _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out859, out _out860, out _out861, out _out862);
                  _1429_recursiveGen = _out859;
                  _1430_recOwned = _out860;
                  _1431_recErased = _out861;
                  _1432_recIdents = _out862;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1429_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1430_recOwned;
                  isErased = _1431_recErased;
                  readIdents = _1432_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1433___mcc_h786 = _source51.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1434_recursiveGen;
                  bool _1435_recOwned;
                  bool _1436_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1437_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out863;
                  bool _out864;
                  bool _out865;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out866;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out863, out _out864, out _out865, out _out866);
                  _1434_recursiveGen = _out863;
                  _1435_recOwned = _out864;
                  _1436_recErased = _out865;
                  _1437_recIdents = _out866;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1434_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1435_recOwned;
                  isErased = _1436_recErased;
                  readIdents = _1437_recIdents;
                }
              }
            } else if (_source29.is_Primitive) {
              DAST._IPrimitive _1438___mcc_h788 = _source29.dtor_Primitive_a0;
              DAST._IPrimitive _source53 = _1438___mcc_h788;
              if (_source53.is_Int) {
                DAST._IType _source54 = _542___mcc_h265;
                if (_source54.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1439___mcc_h792 = _source54.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1440___mcc_h793 = _source54.dtor_typeArgs;
                  DAST._IResolvedType _1441___mcc_h794 = _source54.dtor_resolved;
                  DAST._IResolvedType _source55 = _1441___mcc_h794;
                  if (_source55.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1442___mcc_h798 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1443_recursiveGen;
                      bool _1444_recOwned;
                      bool _1445_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1446_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out867;
                      bool _out868;
                      bool _out869;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out870;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out867, out _out868, out _out869, out _out870);
                      _1443_recursiveGen = _out867;
                      _1444_recOwned = _out868;
                      _1445_recErased = _out869;
                      _1446_recIdents = _out870;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1443_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1444_recOwned;
                      isErased = _1445_recErased;
                      readIdents = _1446_recIdents;
                    }
                  } else if (_source55.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1447___mcc_h800 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1448_recursiveGen;
                      bool _1449_recOwned;
                      bool _1450_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1451_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out871;
                      bool _out872;
                      bool _out873;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out871, out _out872, out _out873, out _out874);
                      _1448_recursiveGen = _out871;
                      _1449_recOwned = _out872;
                      _1450_recErased = _out873;
                      _1451_recIdents = _out874;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1448_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1449_recOwned;
                      isErased = _1450_recErased;
                      readIdents = _1451_recIdents;
                    }
                  } else {
                    DAST._IType _1452___mcc_h802 = _source55.dtor_Newtype_a0;
                    DAST._IType _1453_b = _1452___mcc_h802;
                    {
                      if (object.Equals(_535_fromTpe, _1453_b)) {
                        Dafny.ISequence<Dafny.Rune> _1454_recursiveGen;
                        bool _1455_recOwned;
                        bool _1456_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1457_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out875;
                        bool _out876;
                        bool _out877;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out878;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out875, out _out876, out _out877, out _out878);
                        _1454_recursiveGen = _out875;
                        _1455_recOwned = _out876;
                        _1456_recErased = _out877;
                        _1457_recIdents = _out878;
                        Dafny.ISequence<Dafny.Rune> _1458_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out879;
                        _out879 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _1458_rhsType = _out879;
                        Dafny.ISequence<Dafny.Rune> _1459_uneraseFn;
                        _1459_uneraseFn = ((_1455_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1458_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1459_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1454_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1455_recOwned;
                        isErased = false;
                        readIdents = _1457_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out880;
                        bool _out881;
                        bool _out882;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1453_b), _1453_b, _534_toTpe), selfIdent, @params, mustOwn, out _out880, out _out881, out _out882, out _out883);
                        s = _out880;
                        isOwned = _out881;
                        isErased = _out882;
                        readIdents = _out883;
                      }
                    }
                  }
                } else if (_source54.is_Nullable) {
                  DAST._IType _1460___mcc_h804 = _source54.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1461_recursiveGen;
                    bool _1462_recOwned;
                    bool _1463_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1464_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out884;
                    bool _out885;
                    bool _out886;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out887;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out884, out _out885, out _out886, out _out887);
                    _1461_recursiveGen = _out884;
                    _1462_recOwned = _out885;
                    _1463_recErased = _out886;
                    _1464_recIdents = _out887;
                    if (!(_1462_recOwned)) {
                      _1461_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1461_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1461_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1463_recErased;
                    readIdents = _1464_recIdents;
                  }
                } else if (_source54.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1465___mcc_h806 = _source54.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1466_recursiveGen;
                    bool _1467_recOwned;
                    bool _1468_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out888;
                    bool _out889;
                    bool _out890;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out891;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out888, out _out889, out _out890, out _out891);
                    _1466_recursiveGen = _out888;
                    _1467_recOwned = _out889;
                    _1468_recErased = _out890;
                    _1469_recIdents = _out891;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1466_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1467_recOwned;
                    isErased = _1468_recErased;
                    readIdents = _1469_recIdents;
                  }
                } else if (_source54.is_Array) {
                  DAST._IType _1470___mcc_h808 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1471_recursiveGen;
                    bool _1472_recOwned;
                    bool _1473_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1474_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out892;
                    bool _out893;
                    bool _out894;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out892, out _out893, out _out894, out _out895);
                    _1471_recursiveGen = _out892;
                    _1472_recOwned = _out893;
                    _1473_recErased = _out894;
                    _1474_recIdents = _out895;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1471_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1472_recOwned;
                    isErased = _1473_recErased;
                    readIdents = _1474_recIdents;
                  }
                } else if (_source54.is_Seq) {
                  DAST._IType _1475___mcc_h810 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1476_recursiveGen;
                    bool _1477_recOwned;
                    bool _1478_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1479_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out896;
                    bool _out897;
                    bool _out898;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out899;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out896, out _out897, out _out898, out _out899);
                    _1476_recursiveGen = _out896;
                    _1477_recOwned = _out897;
                    _1478_recErased = _out898;
                    _1479_recIdents = _out899;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1476_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1477_recOwned;
                    isErased = _1478_recErased;
                    readIdents = _1479_recIdents;
                  }
                } else if (_source54.is_Set) {
                  DAST._IType _1480___mcc_h812 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1481_recursiveGen;
                    bool _1482_recOwned;
                    bool _1483_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1484_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out900;
                    bool _out901;
                    bool _out902;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out903;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out900, out _out901, out _out902, out _out903);
                    _1481_recursiveGen = _out900;
                    _1482_recOwned = _out901;
                    _1483_recErased = _out902;
                    _1484_recIdents = _out903;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1481_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1482_recOwned;
                    isErased = _1483_recErased;
                    readIdents = _1484_recIdents;
                  }
                } else if (_source54.is_Multiset) {
                  DAST._IType _1485___mcc_h814 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1486_recursiveGen;
                    bool _1487_recOwned;
                    bool _1488_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1489_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out904;
                    bool _out905;
                    bool _out906;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out904, out _out905, out _out906, out _out907);
                    _1486_recursiveGen = _out904;
                    _1487_recOwned = _out905;
                    _1488_recErased = _out906;
                    _1489_recIdents = _out907;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1486_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1487_recOwned;
                    isErased = _1488_recErased;
                    readIdents = _1489_recIdents;
                  }
                } else if (_source54.is_Map) {
                  DAST._IType _1490___mcc_h816 = _source54.dtor_key;
                  DAST._IType _1491___mcc_h817 = _source54.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1492_recursiveGen;
                    bool _1493_recOwned;
                    bool _1494_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1495_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out908;
                    bool _out909;
                    bool _out910;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out911;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out908, out _out909, out _out910, out _out911);
                    _1492_recursiveGen = _out908;
                    _1493_recOwned = _out909;
                    _1494_recErased = _out910;
                    _1495_recIdents = _out911;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1492_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1493_recOwned;
                    isErased = _1494_recErased;
                    readIdents = _1495_recIdents;
                  }
                } else if (_source54.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1496___mcc_h820 = _source54.dtor_args;
                  DAST._IType _1497___mcc_h821 = _source54.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1498_recursiveGen;
                    bool _1499_recOwned;
                    bool _1500_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1501_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out912;
                    bool _out913;
                    bool _out914;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out915;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out912, out _out913, out _out914, out _out915);
                    _1498_recursiveGen = _out912;
                    _1499_recOwned = _out913;
                    _1500_recErased = _out914;
                    _1501_recIdents = _out915;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1498_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1499_recOwned;
                    isErased = _1500_recErased;
                    readIdents = _1501_recIdents;
                  }
                } else if (_source54.is_Primitive) {
                  DAST._IPrimitive _1502___mcc_h824 = _source54.dtor_Primitive_a0;
                  DAST._IPrimitive _source56 = _1502___mcc_h824;
                  if (_source56.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1503_recursiveGen;
                      bool _1504_recOwned;
                      bool _1505_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1506_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out916;
                      bool _out917;
                      bool _out918;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out916, out _out917, out _out918, out _out919);
                      _1503_recursiveGen = _out916;
                      _1504_recOwned = _out917;
                      _1505_recErased = _out918;
                      _1506_recIdents = _out919;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1503_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1504_recOwned;
                      isErased = _1505_recErased;
                      readIdents = _1506_recIdents;
                    }
                  } else if (_source56.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1507_recursiveGen;
                      bool _1508___v47;
                      bool _1509___v48;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out920;
                      bool _out921;
                      bool _out922;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out923;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, true, out _out920, out _out921, out _out922, out _out923);
                      _1507_recursiveGen = _out920;
                      _1508___v47 = _out921;
                      _1509___v48 = _out922;
                      _1510_recIdents = _out923;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1507_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1510_recIdents;
                    }
                  } else if (_source56.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1511_recursiveGen;
                      bool _1512_recOwned;
                      bool _1513_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1514_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out924;
                      bool _out925;
                      bool _out926;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out927;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out924, out _out925, out _out926, out _out927);
                      _1511_recursiveGen = _out924;
                      _1512_recOwned = _out925;
                      _1513_recErased = _out926;
                      _1514_recIdents = _out927;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1511_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1512_recOwned;
                      isErased = _1513_recErased;
                      readIdents = _1514_recIdents;
                    }
                  } else if (_source56.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1515_recursiveGen;
                      bool _1516_recOwned;
                      bool _1517_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1518_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out928;
                      bool _out929;
                      bool _out930;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out928, out _out929, out _out930, out _out931);
                      _1515_recursiveGen = _out928;
                      _1516_recOwned = _out929;
                      _1517_recErased = _out930;
                      _1518_recIdents = _out931;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1515_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1516_recOwned;
                      isErased = _1517_recErased;
                      readIdents = _1518_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1519_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out932;
                      _out932 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1519_rhsType = _out932;
                      Dafny.ISequence<Dafny.Rune> _1520_recursiveGen;
                      bool _1521___v57;
                      bool _1522___v58;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1523_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out933;
                      bool _out934;
                      bool _out935;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, true, out _out933, out _out934, out _out935, out _out936);
                      _1520_recursiveGen = _out933;
                      _1521___v57 = _out934;
                      _1522___v58 = _out935;
                      _1523_recIdents = _out936;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1520_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1523_recIdents;
                    }
                  }
                } else if (_source54.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1524___mcc_h826 = _source54.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1525_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out937;
                    _out937 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                    _1525_rhsType = _out937;
                    Dafny.ISequence<Dafny.Rune> _1526_recursiveGen;
                    bool _1527___v52;
                    bool _1528___v53;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1529_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out938;
                    bool _out939;
                    bool _out940;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out941;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, true, out _out938, out _out939, out _out940, out _out941);
                    _1526_recursiveGen = _out938;
                    _1527___v52 = _out939;
                    _1528___v53 = _out940;
                    _1529_recIdents = _out941;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1525_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1526_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1529_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1530___mcc_h828 = _source54.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1531_recursiveGen;
                    bool _1532_recOwned;
                    bool _1533_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1534_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out942;
                    bool _out943;
                    bool _out944;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out942, out _out943, out _out944, out _out945);
                    _1531_recursiveGen = _out942;
                    _1532_recOwned = _out943;
                    _1533_recErased = _out944;
                    _1534_recIdents = _out945;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1531_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1532_recOwned;
                    isErased = _1533_recErased;
                    readIdents = _1534_recIdents;
                  }
                }
              } else if (_source53.is_Real) {
                DAST._IType _source57 = _542___mcc_h265;
                if (_source57.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1535___mcc_h830 = _source57.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1536___mcc_h831 = _source57.dtor_typeArgs;
                  DAST._IResolvedType _1537___mcc_h832 = _source57.dtor_resolved;
                  DAST._IResolvedType _source58 = _1537___mcc_h832;
                  if (_source58.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1538___mcc_h836 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1539_recursiveGen;
                      bool _1540_recOwned;
                      bool _1541_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1542_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out946;
                      bool _out947;
                      bool _out948;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out946, out _out947, out _out948, out _out949);
                      _1539_recursiveGen = _out946;
                      _1540_recOwned = _out947;
                      _1541_recErased = _out948;
                      _1542_recIdents = _out949;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1539_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1540_recOwned;
                      isErased = _1541_recErased;
                      readIdents = _1542_recIdents;
                    }
                  } else if (_source58.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1543___mcc_h838 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1544_recursiveGen;
                      bool _1545_recOwned;
                      bool _1546_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1547_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out950;
                      bool _out951;
                      bool _out952;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out953;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out950, out _out951, out _out952, out _out953);
                      _1544_recursiveGen = _out950;
                      _1545_recOwned = _out951;
                      _1546_recErased = _out952;
                      _1547_recIdents = _out953;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1544_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1545_recOwned;
                      isErased = _1546_recErased;
                      readIdents = _1547_recIdents;
                    }
                  } else {
                    DAST._IType _1548___mcc_h840 = _source58.dtor_Newtype_a0;
                    DAST._IType _1549_b = _1548___mcc_h840;
                    {
                      if (object.Equals(_535_fromTpe, _1549_b)) {
                        Dafny.ISequence<Dafny.Rune> _1550_recursiveGen;
                        bool _1551_recOwned;
                        bool _1552_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1553_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out954;
                        bool _out955;
                        bool _out956;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out954, out _out955, out _out956, out _out957);
                        _1550_recursiveGen = _out954;
                        _1551_recOwned = _out955;
                        _1552_recErased = _out956;
                        _1553_recIdents = _out957;
                        Dafny.ISequence<Dafny.Rune> _1554_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out958;
                        _out958 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _1554_rhsType = _out958;
                        Dafny.ISequence<Dafny.Rune> _1555_uneraseFn;
                        _1555_uneraseFn = ((_1551_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1554_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1555_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1550_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1551_recOwned;
                        isErased = false;
                        readIdents = _1553_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out959;
                        bool _out960;
                        bool _out961;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out962;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1549_b), _1549_b, _534_toTpe), selfIdent, @params, mustOwn, out _out959, out _out960, out _out961, out _out962);
                        s = _out959;
                        isOwned = _out960;
                        isErased = _out961;
                        readIdents = _out962;
                      }
                    }
                  }
                } else if (_source57.is_Nullable) {
                  DAST._IType _1556___mcc_h842 = _source57.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1557_recursiveGen;
                    bool _1558_recOwned;
                    bool _1559_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1560_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out963;
                    bool _out964;
                    bool _out965;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out963, out _out964, out _out965, out _out966);
                    _1557_recursiveGen = _out963;
                    _1558_recOwned = _out964;
                    _1559_recErased = _out965;
                    _1560_recIdents = _out966;
                    if (!(_1558_recOwned)) {
                      _1557_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1557_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1557_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1559_recErased;
                    readIdents = _1560_recIdents;
                  }
                } else if (_source57.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1561___mcc_h844 = _source57.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1562_recursiveGen;
                    bool _1563_recOwned;
                    bool _1564_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1565_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out967;
                    bool _out968;
                    bool _out969;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out970;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out967, out _out968, out _out969, out _out970);
                    _1562_recursiveGen = _out967;
                    _1563_recOwned = _out968;
                    _1564_recErased = _out969;
                    _1565_recIdents = _out970;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1562_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1563_recOwned;
                    isErased = _1564_recErased;
                    readIdents = _1565_recIdents;
                  }
                } else if (_source57.is_Array) {
                  DAST._IType _1566___mcc_h846 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1567_recursiveGen;
                    bool _1568_recOwned;
                    bool _1569_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1570_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out971;
                    bool _out972;
                    bool _out973;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out971, out _out972, out _out973, out _out974);
                    _1567_recursiveGen = _out971;
                    _1568_recOwned = _out972;
                    _1569_recErased = _out973;
                    _1570_recIdents = _out974;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1567_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1568_recOwned;
                    isErased = _1569_recErased;
                    readIdents = _1570_recIdents;
                  }
                } else if (_source57.is_Seq) {
                  DAST._IType _1571___mcc_h848 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1572_recursiveGen;
                    bool _1573_recOwned;
                    bool _1574_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1575_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out975;
                    bool _out976;
                    bool _out977;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out978;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out975, out _out976, out _out977, out _out978);
                    _1572_recursiveGen = _out975;
                    _1573_recOwned = _out976;
                    _1574_recErased = _out977;
                    _1575_recIdents = _out978;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1572_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1573_recOwned;
                    isErased = _1574_recErased;
                    readIdents = _1575_recIdents;
                  }
                } else if (_source57.is_Set) {
                  DAST._IType _1576___mcc_h850 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1577_recursiveGen;
                    bool _1578_recOwned;
                    bool _1579_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1580_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out979;
                    bool _out980;
                    bool _out981;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out979, out _out980, out _out981, out _out982);
                    _1577_recursiveGen = _out979;
                    _1578_recOwned = _out980;
                    _1579_recErased = _out981;
                    _1580_recIdents = _out982;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1577_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1578_recOwned;
                    isErased = _1579_recErased;
                    readIdents = _1580_recIdents;
                  }
                } else if (_source57.is_Multiset) {
                  DAST._IType _1581___mcc_h852 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1582_recursiveGen;
                    bool _1583_recOwned;
                    bool _1584_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1585_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out983;
                    bool _out984;
                    bool _out985;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out986;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out983, out _out984, out _out985, out _out986);
                    _1582_recursiveGen = _out983;
                    _1583_recOwned = _out984;
                    _1584_recErased = _out985;
                    _1585_recIdents = _out986;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1582_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1583_recOwned;
                    isErased = _1584_recErased;
                    readIdents = _1585_recIdents;
                  }
                } else if (_source57.is_Map) {
                  DAST._IType _1586___mcc_h854 = _source57.dtor_key;
                  DAST._IType _1587___mcc_h855 = _source57.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1588_recursiveGen;
                    bool _1589_recOwned;
                    bool _1590_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1591_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out987;
                    bool _out988;
                    bool _out989;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out987, out _out988, out _out989, out _out990);
                    _1588_recursiveGen = _out987;
                    _1589_recOwned = _out988;
                    _1590_recErased = _out989;
                    _1591_recIdents = _out990;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1588_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1589_recOwned;
                    isErased = _1590_recErased;
                    readIdents = _1591_recIdents;
                  }
                } else if (_source57.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1592___mcc_h858 = _source57.dtor_args;
                  DAST._IType _1593___mcc_h859 = _source57.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1594_recursiveGen;
                    bool _1595_recOwned;
                    bool _1596_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1597_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out991;
                    bool _out992;
                    bool _out993;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out994;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out991, out _out992, out _out993, out _out994);
                    _1594_recursiveGen = _out991;
                    _1595_recOwned = _out992;
                    _1596_recErased = _out993;
                    _1597_recIdents = _out994;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1594_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1595_recOwned;
                    isErased = _1596_recErased;
                    readIdents = _1597_recIdents;
                  }
                } else if (_source57.is_Primitive) {
                  DAST._IPrimitive _1598___mcc_h862 = _source57.dtor_Primitive_a0;
                  DAST._IPrimitive _source59 = _1598___mcc_h862;
                  if (_source59.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1599_recursiveGen;
                      bool _1600___v49;
                      bool _1601___v50;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1602_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out995;
                      bool _out996;
                      bool _out997;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out998;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, false, out _out995, out _out996, out _out997, out _out998);
                      _1599_recursiveGen = _out995;
                      _1600___v49 = _out996;
                      _1601___v50 = _out997;
                      _1602_recIdents = _out998;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1599_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1602_recIdents;
                    }
                  } else if (_source59.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1603_recursiveGen;
                      bool _1604_recOwned;
                      bool _1605_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1606_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out999;
                      bool _out1000;
                      bool _out1001;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out999, out _out1000, out _out1001, out _out1002);
                      _1603_recursiveGen = _out999;
                      _1604_recOwned = _out1000;
                      _1605_recErased = _out1001;
                      _1606_recIdents = _out1002;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1603_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1604_recOwned;
                      isErased = _1605_recErased;
                      readIdents = _1606_recIdents;
                    }
                  } else if (_source59.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1607_recursiveGen;
                      bool _1608_recOwned;
                      bool _1609_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1610_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1003;
                      bool _out1004;
                      bool _out1005;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1006;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1003, out _out1004, out _out1005, out _out1006);
                      _1607_recursiveGen = _out1003;
                      _1608_recOwned = _out1004;
                      _1609_recErased = _out1005;
                      _1610_recIdents = _out1006;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1607_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1608_recOwned;
                      isErased = _1609_recErased;
                      readIdents = _1610_recIdents;
                    }
                  } else if (_source59.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1611_recursiveGen;
                      bool _1612_recOwned;
                      bool _1613_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1614_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1007;
                      bool _out1008;
                      bool _out1009;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1007, out _out1008, out _out1009, out _out1010);
                      _1611_recursiveGen = _out1007;
                      _1612_recOwned = _out1008;
                      _1613_recErased = _out1009;
                      _1614_recIdents = _out1010;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1611_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1612_recOwned;
                      isErased = _1613_recErased;
                      readIdents = _1614_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1615_recursiveGen;
                      bool _1616_recOwned;
                      bool _1617_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1618_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1011;
                      bool _out1012;
                      bool _out1013;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1011, out _out1012, out _out1013, out _out1014);
                      _1615_recursiveGen = _out1011;
                      _1616_recOwned = _out1012;
                      _1617_recErased = _out1013;
                      _1618_recIdents = _out1014;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1615_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1616_recOwned;
                      isErased = _1617_recErased;
                      readIdents = _1618_recIdents;
                    }
                  }
                } else if (_source57.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1619___mcc_h864 = _source57.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1620_recursiveGen;
                    bool _1621_recOwned;
                    bool _1622_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1623_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1015;
                    bool _out1016;
                    bool _out1017;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1018;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1015, out _out1016, out _out1017, out _out1018);
                    _1620_recursiveGen = _out1015;
                    _1621_recOwned = _out1016;
                    _1622_recErased = _out1017;
                    _1623_recIdents = _out1018;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1620_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1621_recOwned;
                    isErased = _1622_recErased;
                    readIdents = _1623_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1624___mcc_h866 = _source57.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1625_recursiveGen;
                    bool _1626_recOwned;
                    bool _1627_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1019;
                    bool _out1020;
                    bool _out1021;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1019, out _out1020, out _out1021, out _out1022);
                    _1625_recursiveGen = _out1019;
                    _1626_recOwned = _out1020;
                    _1627_recErased = _out1021;
                    _1628_recIdents = _out1022;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1625_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1626_recOwned;
                    isErased = _1627_recErased;
                    readIdents = _1628_recIdents;
                  }
                }
              } else if (_source53.is_String) {
                DAST._IType _source60 = _542___mcc_h265;
                if (_source60.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1629___mcc_h868 = _source60.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1630___mcc_h869 = _source60.dtor_typeArgs;
                  DAST._IResolvedType _1631___mcc_h870 = _source60.dtor_resolved;
                  DAST._IResolvedType _source61 = _1631___mcc_h870;
                  if (_source61.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1632___mcc_h874 = _source61.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1633_recursiveGen;
                      bool _1634_recOwned;
                      bool _1635_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1636_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1023;
                      bool _out1024;
                      bool _out1025;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1023, out _out1024, out _out1025, out _out1026);
                      _1633_recursiveGen = _out1023;
                      _1634_recOwned = _out1024;
                      _1635_recErased = _out1025;
                      _1636_recIdents = _out1026;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1633_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1634_recOwned;
                      isErased = _1635_recErased;
                      readIdents = _1636_recIdents;
                    }
                  } else if (_source61.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1637___mcc_h876 = _source61.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1638_recursiveGen;
                      bool _1639_recOwned;
                      bool _1640_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1641_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1027;
                      bool _out1028;
                      bool _out1029;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1030;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1027, out _out1028, out _out1029, out _out1030);
                      _1638_recursiveGen = _out1027;
                      _1639_recOwned = _out1028;
                      _1640_recErased = _out1029;
                      _1641_recIdents = _out1030;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1638_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1639_recOwned;
                      isErased = _1640_recErased;
                      readIdents = _1641_recIdents;
                    }
                  } else {
                    DAST._IType _1642___mcc_h878 = _source61.dtor_Newtype_a0;
                    DAST._IType _1643_b = _1642___mcc_h878;
                    {
                      if (object.Equals(_535_fromTpe, _1643_b)) {
                        Dafny.ISequence<Dafny.Rune> _1644_recursiveGen;
                        bool _1645_recOwned;
                        bool _1646_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1647_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1031;
                        bool _out1032;
                        bool _out1033;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1031, out _out1032, out _out1033, out _out1034);
                        _1644_recursiveGen = _out1031;
                        _1645_recOwned = _out1032;
                        _1646_recErased = _out1033;
                        _1647_recIdents = _out1034;
                        Dafny.ISequence<Dafny.Rune> _1648_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1035;
                        _out1035 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _1648_rhsType = _out1035;
                        Dafny.ISequence<Dafny.Rune> _1649_uneraseFn;
                        _1649_uneraseFn = ((_1645_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1648_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1649_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1644_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1645_recOwned;
                        isErased = false;
                        readIdents = _1647_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1036;
                        bool _out1037;
                        bool _out1038;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1039;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1643_b), _1643_b, _534_toTpe), selfIdent, @params, mustOwn, out _out1036, out _out1037, out _out1038, out _out1039);
                        s = _out1036;
                        isOwned = _out1037;
                        isErased = _out1038;
                        readIdents = _out1039;
                      }
                    }
                  }
                } else if (_source60.is_Nullable) {
                  DAST._IType _1650___mcc_h880 = _source60.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1651_recursiveGen;
                    bool _1652_recOwned;
                    bool _1653_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1654_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1040;
                    bool _out1041;
                    bool _out1042;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1040, out _out1041, out _out1042, out _out1043);
                    _1651_recursiveGen = _out1040;
                    _1652_recOwned = _out1041;
                    _1653_recErased = _out1042;
                    _1654_recIdents = _out1043;
                    if (!(_1652_recOwned)) {
                      _1651_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1651_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1651_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1653_recErased;
                    readIdents = _1654_recIdents;
                  }
                } else if (_source60.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1655___mcc_h882 = _source60.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1656_recursiveGen;
                    bool _1657_recOwned;
                    bool _1658_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1659_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1044;
                    bool _out1045;
                    bool _out1046;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1047;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1044, out _out1045, out _out1046, out _out1047);
                    _1656_recursiveGen = _out1044;
                    _1657_recOwned = _out1045;
                    _1658_recErased = _out1046;
                    _1659_recIdents = _out1047;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1656_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1657_recOwned;
                    isErased = _1658_recErased;
                    readIdents = _1659_recIdents;
                  }
                } else if (_source60.is_Array) {
                  DAST._IType _1660___mcc_h884 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1661_recursiveGen;
                    bool _1662_recOwned;
                    bool _1663_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1664_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1048;
                    bool _out1049;
                    bool _out1050;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1051;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1048, out _out1049, out _out1050, out _out1051);
                    _1661_recursiveGen = _out1048;
                    _1662_recOwned = _out1049;
                    _1663_recErased = _out1050;
                    _1664_recIdents = _out1051;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1661_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1662_recOwned;
                    isErased = _1663_recErased;
                    readIdents = _1664_recIdents;
                  }
                } else if (_source60.is_Seq) {
                  DAST._IType _1665___mcc_h886 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1666_recursiveGen;
                    bool _1667_recOwned;
                    bool _1668_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1052;
                    bool _out1053;
                    bool _out1054;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1052, out _out1053, out _out1054, out _out1055);
                    _1666_recursiveGen = _out1052;
                    _1667_recOwned = _out1053;
                    _1668_recErased = _out1054;
                    _1669_recIdents = _out1055;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1666_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1667_recOwned;
                    isErased = _1668_recErased;
                    readIdents = _1669_recIdents;
                  }
                } else if (_source60.is_Set) {
                  DAST._IType _1670___mcc_h888 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1671_recursiveGen;
                    bool _1672_recOwned;
                    bool _1673_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1674_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1056;
                    bool _out1057;
                    bool _out1058;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1059;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1056, out _out1057, out _out1058, out _out1059);
                    _1671_recursiveGen = _out1056;
                    _1672_recOwned = _out1057;
                    _1673_recErased = _out1058;
                    _1674_recIdents = _out1059;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1671_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1672_recOwned;
                    isErased = _1673_recErased;
                    readIdents = _1674_recIdents;
                  }
                } else if (_source60.is_Multiset) {
                  DAST._IType _1675___mcc_h890 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1676_recursiveGen;
                    bool _1677_recOwned;
                    bool _1678_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1679_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1060;
                    bool _out1061;
                    bool _out1062;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1063;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1060, out _out1061, out _out1062, out _out1063);
                    _1676_recursiveGen = _out1060;
                    _1677_recOwned = _out1061;
                    _1678_recErased = _out1062;
                    _1679_recIdents = _out1063;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1676_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1677_recOwned;
                    isErased = _1678_recErased;
                    readIdents = _1679_recIdents;
                  }
                } else if (_source60.is_Map) {
                  DAST._IType _1680___mcc_h892 = _source60.dtor_key;
                  DAST._IType _1681___mcc_h893 = _source60.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1682_recursiveGen;
                    bool _1683_recOwned;
                    bool _1684_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1685_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1064;
                    bool _out1065;
                    bool _out1066;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1064, out _out1065, out _out1066, out _out1067);
                    _1682_recursiveGen = _out1064;
                    _1683_recOwned = _out1065;
                    _1684_recErased = _out1066;
                    _1685_recIdents = _out1067;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1682_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1683_recOwned;
                    isErased = _1684_recErased;
                    readIdents = _1685_recIdents;
                  }
                } else if (_source60.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1686___mcc_h896 = _source60.dtor_args;
                  DAST._IType _1687___mcc_h897 = _source60.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1688_recursiveGen;
                    bool _1689_recOwned;
                    bool _1690_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1691_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1068;
                    bool _out1069;
                    bool _out1070;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1071;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1068, out _out1069, out _out1070, out _out1071);
                    _1688_recursiveGen = _out1068;
                    _1689_recOwned = _out1069;
                    _1690_recErased = _out1070;
                    _1691_recIdents = _out1071;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1688_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1689_recOwned;
                    isErased = _1690_recErased;
                    readIdents = _1691_recIdents;
                  }
                } else if (_source60.is_Primitive) {
                  DAST._IPrimitive _1692___mcc_h900 = _source60.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1693_recursiveGen;
                    bool _1694_recOwned;
                    bool _1695_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1072;
                    bool _out1073;
                    bool _out1074;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1075;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1072, out _out1073, out _out1074, out _out1075);
                    _1693_recursiveGen = _out1072;
                    _1694_recOwned = _out1073;
                    _1695_recErased = _out1074;
                    _1696_recIdents = _out1075;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1693_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1694_recOwned;
                    isErased = _1695_recErased;
                    readIdents = _1696_recIdents;
                  }
                } else if (_source60.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1697___mcc_h902 = _source60.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1698_recursiveGen;
                    bool _1699_recOwned;
                    bool _1700_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1076;
                    bool _out1077;
                    bool _out1078;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1076, out _out1077, out _out1078, out _out1079);
                    _1698_recursiveGen = _out1076;
                    _1699_recOwned = _out1077;
                    _1700_recErased = _out1078;
                    _1701_recIdents = _out1079;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1698_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1699_recOwned;
                    isErased = _1700_recErased;
                    readIdents = _1701_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1702___mcc_h904 = _source60.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1703_recursiveGen;
                    bool _1704_recOwned;
                    bool _1705_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1706_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1080;
                    bool _out1081;
                    bool _out1082;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1083;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1080, out _out1081, out _out1082, out _out1083);
                    _1703_recursiveGen = _out1080;
                    _1704_recOwned = _out1081;
                    _1705_recErased = _out1082;
                    _1706_recIdents = _out1083;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1703_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1704_recOwned;
                    isErased = _1705_recErased;
                    readIdents = _1706_recIdents;
                  }
                }
              } else if (_source53.is_Bool) {
                DAST._IType _source62 = _542___mcc_h265;
                if (_source62.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1707___mcc_h906 = _source62.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1708___mcc_h907 = _source62.dtor_typeArgs;
                  DAST._IResolvedType _1709___mcc_h908 = _source62.dtor_resolved;
                  DAST._IResolvedType _source63 = _1709___mcc_h908;
                  if (_source63.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1710___mcc_h912 = _source63.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1711_recursiveGen;
                      bool _1712_recOwned;
                      bool _1713_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1714_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1084;
                      bool _out1085;
                      bool _out1086;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1087;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1084, out _out1085, out _out1086, out _out1087);
                      _1711_recursiveGen = _out1084;
                      _1712_recOwned = _out1085;
                      _1713_recErased = _out1086;
                      _1714_recIdents = _out1087;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1711_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1712_recOwned;
                      isErased = _1713_recErased;
                      readIdents = _1714_recIdents;
                    }
                  } else if (_source63.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1715___mcc_h914 = _source63.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1716_recursiveGen;
                      bool _1717_recOwned;
                      bool _1718_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1719_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1088;
                      bool _out1089;
                      bool _out1090;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1088, out _out1089, out _out1090, out _out1091);
                      _1716_recursiveGen = _out1088;
                      _1717_recOwned = _out1089;
                      _1718_recErased = _out1090;
                      _1719_recIdents = _out1091;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1716_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1717_recOwned;
                      isErased = _1718_recErased;
                      readIdents = _1719_recIdents;
                    }
                  } else {
                    DAST._IType _1720___mcc_h916 = _source63.dtor_Newtype_a0;
                    DAST._IType _1721_b = _1720___mcc_h916;
                    {
                      if (object.Equals(_535_fromTpe, _1721_b)) {
                        Dafny.ISequence<Dafny.Rune> _1722_recursiveGen;
                        bool _1723_recOwned;
                        bool _1724_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1725_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1092;
                        bool _out1093;
                        bool _out1094;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1095;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1092, out _out1093, out _out1094, out _out1095);
                        _1722_recursiveGen = _out1092;
                        _1723_recOwned = _out1093;
                        _1724_recErased = _out1094;
                        _1725_recIdents = _out1095;
                        Dafny.ISequence<Dafny.Rune> _1726_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1096;
                        _out1096 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _1726_rhsType = _out1096;
                        Dafny.ISequence<Dafny.Rune> _1727_uneraseFn;
                        _1727_uneraseFn = ((_1723_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1726_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1727_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1722_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1723_recOwned;
                        isErased = false;
                        readIdents = _1725_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1097;
                        bool _out1098;
                        bool _out1099;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1721_b), _1721_b, _534_toTpe), selfIdent, @params, mustOwn, out _out1097, out _out1098, out _out1099, out _out1100);
                        s = _out1097;
                        isOwned = _out1098;
                        isErased = _out1099;
                        readIdents = _out1100;
                      }
                    }
                  }
                } else if (_source62.is_Nullable) {
                  DAST._IType _1728___mcc_h918 = _source62.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1729_recursiveGen;
                    bool _1730_recOwned;
                    bool _1731_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1732_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1101;
                    bool _out1102;
                    bool _out1103;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1104;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1101, out _out1102, out _out1103, out _out1104);
                    _1729_recursiveGen = _out1101;
                    _1730_recOwned = _out1102;
                    _1731_recErased = _out1103;
                    _1732_recIdents = _out1104;
                    if (!(_1730_recOwned)) {
                      _1729_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1729_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1729_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1731_recErased;
                    readIdents = _1732_recIdents;
                  }
                } else if (_source62.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1733___mcc_h920 = _source62.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1734_recursiveGen;
                    bool _1735_recOwned;
                    bool _1736_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1737_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1105;
                    bool _out1106;
                    bool _out1107;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1108;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1105, out _out1106, out _out1107, out _out1108);
                    _1734_recursiveGen = _out1105;
                    _1735_recOwned = _out1106;
                    _1736_recErased = _out1107;
                    _1737_recIdents = _out1108;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1734_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1735_recOwned;
                    isErased = _1736_recErased;
                    readIdents = _1737_recIdents;
                  }
                } else if (_source62.is_Array) {
                  DAST._IType _1738___mcc_h922 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1739_recursiveGen;
                    bool _1740_recOwned;
                    bool _1741_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1742_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1109;
                    bool _out1110;
                    bool _out1111;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1109, out _out1110, out _out1111, out _out1112);
                    _1739_recursiveGen = _out1109;
                    _1740_recOwned = _out1110;
                    _1741_recErased = _out1111;
                    _1742_recIdents = _out1112;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1739_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1740_recOwned;
                    isErased = _1741_recErased;
                    readIdents = _1742_recIdents;
                  }
                } else if (_source62.is_Seq) {
                  DAST._IType _1743___mcc_h924 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1744_recursiveGen;
                    bool _1745_recOwned;
                    bool _1746_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1113;
                    bool _out1114;
                    bool _out1115;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1116;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1113, out _out1114, out _out1115, out _out1116);
                    _1744_recursiveGen = _out1113;
                    _1745_recOwned = _out1114;
                    _1746_recErased = _out1115;
                    _1747_recIdents = _out1116;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1744_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1745_recOwned;
                    isErased = _1746_recErased;
                    readIdents = _1747_recIdents;
                  }
                } else if (_source62.is_Set) {
                  DAST._IType _1748___mcc_h926 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1749_recursiveGen;
                    bool _1750_recOwned;
                    bool _1751_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1752_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1117;
                    bool _out1118;
                    bool _out1119;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1120;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1117, out _out1118, out _out1119, out _out1120);
                    _1749_recursiveGen = _out1117;
                    _1750_recOwned = _out1118;
                    _1751_recErased = _out1119;
                    _1752_recIdents = _out1120;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1749_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1750_recOwned;
                    isErased = _1751_recErased;
                    readIdents = _1752_recIdents;
                  }
                } else if (_source62.is_Multiset) {
                  DAST._IType _1753___mcc_h928 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1754_recursiveGen;
                    bool _1755_recOwned;
                    bool _1756_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1757_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1121;
                    bool _out1122;
                    bool _out1123;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1121, out _out1122, out _out1123, out _out1124);
                    _1754_recursiveGen = _out1121;
                    _1755_recOwned = _out1122;
                    _1756_recErased = _out1123;
                    _1757_recIdents = _out1124;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1754_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1755_recOwned;
                    isErased = _1756_recErased;
                    readIdents = _1757_recIdents;
                  }
                } else if (_source62.is_Map) {
                  DAST._IType _1758___mcc_h930 = _source62.dtor_key;
                  DAST._IType _1759___mcc_h931 = _source62.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1760_recursiveGen;
                    bool _1761_recOwned;
                    bool _1762_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1763_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1125;
                    bool _out1126;
                    bool _out1127;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1125, out _out1126, out _out1127, out _out1128);
                    _1760_recursiveGen = _out1125;
                    _1761_recOwned = _out1126;
                    _1762_recErased = _out1127;
                    _1763_recIdents = _out1128;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1760_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1761_recOwned;
                    isErased = _1762_recErased;
                    readIdents = _1763_recIdents;
                  }
                } else if (_source62.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1764___mcc_h934 = _source62.dtor_args;
                  DAST._IType _1765___mcc_h935 = _source62.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1766_recursiveGen;
                    bool _1767_recOwned;
                    bool _1768_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1769_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1129;
                    bool _out1130;
                    bool _out1131;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1132;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1129, out _out1130, out _out1131, out _out1132);
                    _1766_recursiveGen = _out1129;
                    _1767_recOwned = _out1130;
                    _1768_recErased = _out1131;
                    _1769_recIdents = _out1132;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1766_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1767_recOwned;
                    isErased = _1768_recErased;
                    readIdents = _1769_recIdents;
                  }
                } else if (_source62.is_Primitive) {
                  DAST._IPrimitive _1770___mcc_h938 = _source62.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1771_recursiveGen;
                    bool _1772_recOwned;
                    bool _1773_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1774_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1133;
                    bool _out1134;
                    bool _out1135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1133, out _out1134, out _out1135, out _out1136);
                    _1771_recursiveGen = _out1133;
                    _1772_recOwned = _out1134;
                    _1773_recErased = _out1135;
                    _1774_recIdents = _out1136;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1771_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1772_recOwned;
                    isErased = _1773_recErased;
                    readIdents = _1774_recIdents;
                  }
                } else if (_source62.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1775___mcc_h940 = _source62.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1776_recursiveGen;
                    bool _1777_recOwned;
                    bool _1778_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1779_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1137;
                    bool _out1138;
                    bool _out1139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1140;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1137, out _out1138, out _out1139, out _out1140);
                    _1776_recursiveGen = _out1137;
                    _1777_recOwned = _out1138;
                    _1778_recErased = _out1139;
                    _1779_recIdents = _out1140;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1776_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1777_recOwned;
                    isErased = _1778_recErased;
                    readIdents = _1779_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1780___mcc_h942 = _source62.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1781_recursiveGen;
                    bool _1782_recOwned;
                    bool _1783_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1784_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1141;
                    bool _out1142;
                    bool _out1143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1144;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1141, out _out1142, out _out1143, out _out1144);
                    _1781_recursiveGen = _out1141;
                    _1782_recOwned = _out1142;
                    _1783_recErased = _out1143;
                    _1784_recIdents = _out1144;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1781_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1782_recOwned;
                    isErased = _1783_recErased;
                    readIdents = _1784_recIdents;
                  }
                }
              } else {
                DAST._IType _source64 = _542___mcc_h265;
                if (_source64.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1785___mcc_h944 = _source64.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1786___mcc_h945 = _source64.dtor_typeArgs;
                  DAST._IResolvedType _1787___mcc_h946 = _source64.dtor_resolved;
                  DAST._IResolvedType _source65 = _1787___mcc_h946;
                  if (_source65.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1788___mcc_h950 = _source65.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1789_recursiveGen;
                      bool _1790_recOwned;
                      bool _1791_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1145;
                      bool _out1146;
                      bool _out1147;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1145, out _out1146, out _out1147, out _out1148);
                      _1789_recursiveGen = _out1145;
                      _1790_recOwned = _out1146;
                      _1791_recErased = _out1147;
                      _1792_recIdents = _out1148;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1789_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1790_recOwned;
                      isErased = _1791_recErased;
                      readIdents = _1792_recIdents;
                    }
                  } else if (_source65.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1793___mcc_h952 = _source65.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1794_recursiveGen;
                      bool _1795_recOwned;
                      bool _1796_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1797_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1149;
                      bool _out1150;
                      bool _out1151;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1152;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1149, out _out1150, out _out1151, out _out1152);
                      _1794_recursiveGen = _out1149;
                      _1795_recOwned = _out1150;
                      _1796_recErased = _out1151;
                      _1797_recIdents = _out1152;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1794_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1795_recOwned;
                      isErased = _1796_recErased;
                      readIdents = _1797_recIdents;
                    }
                  } else {
                    DAST._IType _1798___mcc_h954 = _source65.dtor_Newtype_a0;
                    DAST._IType _1799_b = _1798___mcc_h954;
                    {
                      if (object.Equals(_535_fromTpe, _1799_b)) {
                        Dafny.ISequence<Dafny.Rune> _1800_recursiveGen;
                        bool _1801_recOwned;
                        bool _1802_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1803_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1153;
                        bool _out1154;
                        bool _out1155;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1156;
                        DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1153, out _out1154, out _out1155, out _out1156);
                        _1800_recursiveGen = _out1153;
                        _1801_recOwned = _out1154;
                        _1802_recErased = _out1155;
                        _1803_recIdents = _out1156;
                        Dafny.ISequence<Dafny.Rune> _1804_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1157;
                        _out1157 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                        _1804_rhsType = _out1157;
                        Dafny.ISequence<Dafny.Rune> _1805_uneraseFn;
                        _1805_uneraseFn = ((_1801_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1804_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1805_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1800_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1801_recOwned;
                        isErased = false;
                        readIdents = _1803_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1158;
                        bool _out1159;
                        bool _out1160;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1161;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1799_b), _1799_b, _534_toTpe), selfIdent, @params, mustOwn, out _out1158, out _out1159, out _out1160, out _out1161);
                        s = _out1158;
                        isOwned = _out1159;
                        isErased = _out1160;
                        readIdents = _out1161;
                      }
                    }
                  }
                } else if (_source64.is_Nullable) {
                  DAST._IType _1806___mcc_h956 = _source64.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1807_recursiveGen;
                    bool _1808_recOwned;
                    bool _1809_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1810_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1162;
                    bool _out1163;
                    bool _out1164;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1165;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1162, out _out1163, out _out1164, out _out1165);
                    _1807_recursiveGen = _out1162;
                    _1808_recOwned = _out1163;
                    _1809_recErased = _out1164;
                    _1810_recIdents = _out1165;
                    if (!(_1808_recOwned)) {
                      _1807_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1807_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1807_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1809_recErased;
                    readIdents = _1810_recIdents;
                  }
                } else if (_source64.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1811___mcc_h958 = _source64.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1812_recursiveGen;
                    bool _1813_recOwned;
                    bool _1814_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1166;
                    bool _out1167;
                    bool _out1168;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1166, out _out1167, out _out1168, out _out1169);
                    _1812_recursiveGen = _out1166;
                    _1813_recOwned = _out1167;
                    _1814_recErased = _out1168;
                    _1815_recIdents = _out1169;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1812_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1813_recOwned;
                    isErased = _1814_recErased;
                    readIdents = _1815_recIdents;
                  }
                } else if (_source64.is_Array) {
                  DAST._IType _1816___mcc_h960 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1817_recursiveGen;
                    bool _1818_recOwned;
                    bool _1819_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1170;
                    bool _out1171;
                    bool _out1172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1173;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1170, out _out1171, out _out1172, out _out1173);
                    _1817_recursiveGen = _out1170;
                    _1818_recOwned = _out1171;
                    _1819_recErased = _out1172;
                    _1820_recIdents = _out1173;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1817_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1818_recOwned;
                    isErased = _1819_recErased;
                    readIdents = _1820_recIdents;
                  }
                } else if (_source64.is_Seq) {
                  DAST._IType _1821___mcc_h962 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1822_recursiveGen;
                    bool _1823_recOwned;
                    bool _1824_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1174;
                    bool _out1175;
                    bool _out1176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1177;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1174, out _out1175, out _out1176, out _out1177);
                    _1822_recursiveGen = _out1174;
                    _1823_recOwned = _out1175;
                    _1824_recErased = _out1176;
                    _1825_recIdents = _out1177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1822_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1823_recOwned;
                    isErased = _1824_recErased;
                    readIdents = _1825_recIdents;
                  }
                } else if (_source64.is_Set) {
                  DAST._IType _1826___mcc_h964 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1827_recursiveGen;
                    bool _1828_recOwned;
                    bool _1829_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1830_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1178;
                    bool _out1179;
                    bool _out1180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1178, out _out1179, out _out1180, out _out1181);
                    _1827_recursiveGen = _out1178;
                    _1828_recOwned = _out1179;
                    _1829_recErased = _out1180;
                    _1830_recIdents = _out1181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1827_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1828_recOwned;
                    isErased = _1829_recErased;
                    readIdents = _1830_recIdents;
                  }
                } else if (_source64.is_Multiset) {
                  DAST._IType _1831___mcc_h966 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1832_recursiveGen;
                    bool _1833_recOwned;
                    bool _1834_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1835_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1182;
                    bool _out1183;
                    bool _out1184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1185;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1182, out _out1183, out _out1184, out _out1185);
                    _1832_recursiveGen = _out1182;
                    _1833_recOwned = _out1183;
                    _1834_recErased = _out1184;
                    _1835_recIdents = _out1185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1832_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1833_recOwned;
                    isErased = _1834_recErased;
                    readIdents = _1835_recIdents;
                  }
                } else if (_source64.is_Map) {
                  DAST._IType _1836___mcc_h968 = _source64.dtor_key;
                  DAST._IType _1837___mcc_h969 = _source64.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1838_recursiveGen;
                    bool _1839_recOwned;
                    bool _1840_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1841_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1186;
                    bool _out1187;
                    bool _out1188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1189;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1186, out _out1187, out _out1188, out _out1189);
                    _1838_recursiveGen = _out1186;
                    _1839_recOwned = _out1187;
                    _1840_recErased = _out1188;
                    _1841_recIdents = _out1189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1838_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1839_recOwned;
                    isErased = _1840_recErased;
                    readIdents = _1841_recIdents;
                  }
                } else if (_source64.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1842___mcc_h972 = _source64.dtor_args;
                  DAST._IType _1843___mcc_h973 = _source64.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1844_recursiveGen;
                    bool _1845_recOwned;
                    bool _1846_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1847_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1190;
                    bool _out1191;
                    bool _out1192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1190, out _out1191, out _out1192, out _out1193);
                    _1844_recursiveGen = _out1190;
                    _1845_recOwned = _out1191;
                    _1846_recErased = _out1192;
                    _1847_recIdents = _out1193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1844_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1845_recOwned;
                    isErased = _1846_recErased;
                    readIdents = _1847_recIdents;
                  }
                } else if (_source64.is_Primitive) {
                  DAST._IPrimitive _1848___mcc_h976 = _source64.dtor_Primitive_a0;
                  DAST._IPrimitive _source66 = _1848___mcc_h976;
                  if (_source66.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1849_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1194;
                      _out1194 = DCOMP.COMP.GenType(_535_fromTpe, true, false);
                      _1849_rhsType = _out1194;
                      Dafny.ISequence<Dafny.Rune> _1850_recursiveGen;
                      bool _1851___v59;
                      bool _1852___v60;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1853_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1195;
                      bool _out1196;
                      bool _out1197;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1198;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, true, out _out1195, out _out1196, out _out1197, out _out1198);
                      _1850_recursiveGen = _out1195;
                      _1851___v59 = _out1196;
                      _1852___v60 = _out1197;
                      _1853_recIdents = _out1198;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1850_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1853_recIdents;
                    }
                  } else if (_source66.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1854_recursiveGen;
                      bool _1855_recOwned;
                      bool _1856_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1857_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1199;
                      bool _out1200;
                      bool _out1201;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1199, out _out1200, out _out1201, out _out1202);
                      _1854_recursiveGen = _out1199;
                      _1855_recOwned = _out1200;
                      _1856_recErased = _out1201;
                      _1857_recIdents = _out1202;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1854_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1855_recOwned;
                      isErased = _1856_recErased;
                      readIdents = _1857_recIdents;
                    }
                  } else if (_source66.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1858_recursiveGen;
                      bool _1859_recOwned;
                      bool _1860_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1203;
                      bool _out1204;
                      bool _out1205;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1206;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1203, out _out1204, out _out1205, out _out1206);
                      _1858_recursiveGen = _out1203;
                      _1859_recOwned = _out1204;
                      _1860_recErased = _out1205;
                      _1861_recIdents = _out1206;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1858_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1859_recOwned;
                      isErased = _1860_recErased;
                      readIdents = _1861_recIdents;
                    }
                  } else if (_source66.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1862_recursiveGen;
                      bool _1863_recOwned;
                      bool _1864_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1207;
                      bool _out1208;
                      bool _out1209;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1210;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1207, out _out1208, out _out1209, out _out1210);
                      _1862_recursiveGen = _out1207;
                      _1863_recOwned = _out1208;
                      _1864_recErased = _out1209;
                      _1865_recIdents = _out1210;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1862_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1863_recOwned;
                      isErased = _1864_recErased;
                      readIdents = _1865_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1866_recursiveGen;
                      bool _1867_recOwned;
                      bool _1868_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1869_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1211;
                      bool _out1212;
                      bool _out1213;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1211, out _out1212, out _out1213, out _out1214);
                      _1866_recursiveGen = _out1211;
                      _1867_recOwned = _out1212;
                      _1868_recErased = _out1213;
                      _1869_recIdents = _out1214;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1866_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1867_recOwned;
                      isErased = _1868_recErased;
                      readIdents = _1869_recIdents;
                    }
                  }
                } else if (_source64.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1870___mcc_h978 = _source64.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1871_recursiveGen;
                    bool _1872_recOwned;
                    bool _1873_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1215;
                    bool _out1216;
                    bool _out1217;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1218;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1215, out _out1216, out _out1217, out _out1218);
                    _1871_recursiveGen = _out1215;
                    _1872_recOwned = _out1216;
                    _1873_recErased = _out1217;
                    _1874_recIdents = _out1218;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1871_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1872_recOwned;
                    isErased = _1873_recErased;
                    readIdents = _1874_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1875___mcc_h980 = _source64.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1876_recursiveGen;
                    bool _1877_recOwned;
                    bool _1878_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1219;
                    bool _out1220;
                    bool _out1221;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1222;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1219, out _out1220, out _out1221, out _out1222);
                    _1876_recursiveGen = _out1219;
                    _1877_recOwned = _out1220;
                    _1878_recErased = _out1221;
                    _1879_recIdents = _out1222;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1877_recOwned;
                    isErased = _1878_recErased;
                    readIdents = _1879_recIdents;
                  }
                }
              }
            } else if (_source29.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1880___mcc_h982 = _source29.dtor_Passthrough_a0;
              DAST._IType _source67 = _542___mcc_h265;
              if (_source67.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1881___mcc_h986 = _source67.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1882___mcc_h987 = _source67.dtor_typeArgs;
                DAST._IResolvedType _1883___mcc_h988 = _source67.dtor_resolved;
                DAST._IResolvedType _source68 = _1883___mcc_h988;
                if (_source68.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1884___mcc_h992 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1885_recursiveGen;
                    bool _1886_recOwned;
                    bool _1887_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1888_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1223;
                    bool _out1224;
                    bool _out1225;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1223, out _out1224, out _out1225, out _out1226);
                    _1885_recursiveGen = _out1223;
                    _1886_recOwned = _out1224;
                    _1887_recErased = _out1225;
                    _1888_recIdents = _out1226;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1885_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1886_recOwned;
                    isErased = _1887_recErased;
                    readIdents = _1888_recIdents;
                  }
                } else if (_source68.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1889___mcc_h994 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1890_recursiveGen;
                    bool _1891_recOwned;
                    bool _1892_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1227;
                    bool _out1228;
                    bool _out1229;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1230;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1227, out _out1228, out _out1229, out _out1230);
                    _1890_recursiveGen = _out1227;
                    _1891_recOwned = _out1228;
                    _1892_recErased = _out1229;
                    _1893_recIdents = _out1230;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1890_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1891_recOwned;
                    isErased = _1892_recErased;
                    readIdents = _1893_recIdents;
                  }
                } else {
                  DAST._IType _1894___mcc_h996 = _source68.dtor_Newtype_a0;
                  DAST._IType _1895_b = _1894___mcc_h996;
                  {
                    if (object.Equals(_535_fromTpe, _1895_b)) {
                      Dafny.ISequence<Dafny.Rune> _1896_recursiveGen;
                      bool _1897_recOwned;
                      bool _1898_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1899_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1231;
                      bool _out1232;
                      bool _out1233;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1234;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1231, out _out1232, out _out1233, out _out1234);
                      _1896_recursiveGen = _out1231;
                      _1897_recOwned = _out1232;
                      _1898_recErased = _out1233;
                      _1899_recIdents = _out1234;
                      Dafny.ISequence<Dafny.Rune> _1900_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1235;
                      _out1235 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1900_rhsType = _out1235;
                      Dafny.ISequence<Dafny.Rune> _1901_uneraseFn;
                      _1901_uneraseFn = ((_1897_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1900_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1901_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1896_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1897_recOwned;
                      isErased = false;
                      readIdents = _1899_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1236;
                      bool _out1237;
                      bool _out1238;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1239;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1895_b), _1895_b, _534_toTpe), selfIdent, @params, mustOwn, out _out1236, out _out1237, out _out1238, out _out1239);
                      s = _out1236;
                      isOwned = _out1237;
                      isErased = _out1238;
                      readIdents = _out1239;
                    }
                  }
                }
              } else if (_source67.is_Nullable) {
                DAST._IType _1902___mcc_h998 = _source67.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1903_recursiveGen;
                  bool _1904_recOwned;
                  bool _1905_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1906_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1240;
                  bool _out1241;
                  bool _out1242;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1240, out _out1241, out _out1242, out _out1243);
                  _1903_recursiveGen = _out1240;
                  _1904_recOwned = _out1241;
                  _1905_recErased = _out1242;
                  _1906_recIdents = _out1243;
                  if (!(_1904_recOwned)) {
                    _1903_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1903_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1903_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1905_recErased;
                  readIdents = _1906_recIdents;
                }
              } else if (_source67.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1907___mcc_h1000 = _source67.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1908_recursiveGen;
                  bool _1909_recOwned;
                  bool _1910_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1911_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1244;
                  bool _out1245;
                  bool _out1246;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1244, out _out1245, out _out1246, out _out1247);
                  _1908_recursiveGen = _out1244;
                  _1909_recOwned = _out1245;
                  _1910_recErased = _out1246;
                  _1911_recIdents = _out1247;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1908_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1909_recOwned;
                  isErased = _1910_recErased;
                  readIdents = _1911_recIdents;
                }
              } else if (_source67.is_Array) {
                DAST._IType _1912___mcc_h1002 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1913_recursiveGen;
                  bool _1914_recOwned;
                  bool _1915_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1248;
                  bool _out1249;
                  bool _out1250;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1248, out _out1249, out _out1250, out _out1251);
                  _1913_recursiveGen = _out1248;
                  _1914_recOwned = _out1249;
                  _1915_recErased = _out1250;
                  _1916_recIdents = _out1251;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1913_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1914_recOwned;
                  isErased = _1915_recErased;
                  readIdents = _1916_recIdents;
                }
              } else if (_source67.is_Seq) {
                DAST._IType _1917___mcc_h1004 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1918_recursiveGen;
                  bool _1919_recOwned;
                  bool _1920_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1921_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1252;
                  bool _out1253;
                  bool _out1254;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1255;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1252, out _out1253, out _out1254, out _out1255);
                  _1918_recursiveGen = _out1252;
                  _1919_recOwned = _out1253;
                  _1920_recErased = _out1254;
                  _1921_recIdents = _out1255;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1918_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1919_recOwned;
                  isErased = _1920_recErased;
                  readIdents = _1921_recIdents;
                }
              } else if (_source67.is_Set) {
                DAST._IType _1922___mcc_h1006 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1923_recursiveGen;
                  bool _1924_recOwned;
                  bool _1925_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1926_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1256;
                  bool _out1257;
                  bool _out1258;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1256, out _out1257, out _out1258, out _out1259);
                  _1923_recursiveGen = _out1256;
                  _1924_recOwned = _out1257;
                  _1925_recErased = _out1258;
                  _1926_recIdents = _out1259;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1923_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1924_recOwned;
                  isErased = _1925_recErased;
                  readIdents = _1926_recIdents;
                }
              } else if (_source67.is_Multiset) {
                DAST._IType _1927___mcc_h1008 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1928_recursiveGen;
                  bool _1929_recOwned;
                  bool _1930_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1931_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1260;
                  bool _out1261;
                  bool _out1262;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1263;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1260, out _out1261, out _out1262, out _out1263);
                  _1928_recursiveGen = _out1260;
                  _1929_recOwned = _out1261;
                  _1930_recErased = _out1262;
                  _1931_recIdents = _out1263;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1928_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1929_recOwned;
                  isErased = _1930_recErased;
                  readIdents = _1931_recIdents;
                }
              } else if (_source67.is_Map) {
                DAST._IType _1932___mcc_h1010 = _source67.dtor_key;
                DAST._IType _1933___mcc_h1011 = _source67.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1934_recursiveGen;
                  bool _1935_recOwned;
                  bool _1936_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1937_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1264;
                  bool _out1265;
                  bool _out1266;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1267;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1264, out _out1265, out _out1266, out _out1267);
                  _1934_recursiveGen = _out1264;
                  _1935_recOwned = _out1265;
                  _1936_recErased = _out1266;
                  _1937_recIdents = _out1267;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1934_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1935_recOwned;
                  isErased = _1936_recErased;
                  readIdents = _1937_recIdents;
                }
              } else if (_source67.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1938___mcc_h1014 = _source67.dtor_args;
                DAST._IType _1939___mcc_h1015 = _source67.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1940_recursiveGen;
                  bool _1941_recOwned;
                  bool _1942_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1943_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1268;
                  bool _out1269;
                  bool _out1270;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1268, out _out1269, out _out1270, out _out1271);
                  _1940_recursiveGen = _out1268;
                  _1941_recOwned = _out1269;
                  _1942_recErased = _out1270;
                  _1943_recIdents = _out1271;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1940_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1941_recOwned;
                  isErased = _1942_recErased;
                  readIdents = _1943_recIdents;
                }
              } else if (_source67.is_Primitive) {
                DAST._IPrimitive _1944___mcc_h1018 = _source67.dtor_Primitive_a0;
                DAST._IPrimitive _source69 = _1944___mcc_h1018;
                if (_source69.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1945_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1272;
                    _out1272 = DCOMP.COMP.GenType(_535_fromTpe, true, false);
                    _1945_rhsType = _out1272;
                    Dafny.ISequence<Dafny.Rune> _1946_recursiveGen;
                    bool _1947___v55;
                    bool _1948___v56;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1273;
                    bool _out1274;
                    bool _out1275;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1276;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, true, out _out1273, out _out1274, out _out1275, out _out1276);
                    _1946_recursiveGen = _out1273;
                    _1947___v55 = _out1274;
                    _1948___v56 = _out1275;
                    _1949_recIdents = _out1276;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1946_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1949_recIdents;
                  }
                } else if (_source69.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1950_recursiveGen;
                    bool _1951_recOwned;
                    bool _1952_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1953_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1277;
                    bool _out1278;
                    bool _out1279;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1277, out _out1278, out _out1279, out _out1280);
                    _1950_recursiveGen = _out1277;
                    _1951_recOwned = _out1278;
                    _1952_recErased = _out1279;
                    _1953_recIdents = _out1280;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1950_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1951_recOwned;
                    isErased = _1952_recErased;
                    readIdents = _1953_recIdents;
                  }
                } else if (_source69.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1954_recursiveGen;
                    bool _1955_recOwned;
                    bool _1956_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1957_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1281;
                    bool _out1282;
                    bool _out1283;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1281, out _out1282, out _out1283, out _out1284);
                    _1954_recursiveGen = _out1281;
                    _1955_recOwned = _out1282;
                    _1956_recErased = _out1283;
                    _1957_recIdents = _out1284;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1954_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1955_recOwned;
                    isErased = _1956_recErased;
                    readIdents = _1957_recIdents;
                  }
                } else if (_source69.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1958_recursiveGen;
                    bool _1959_recOwned;
                    bool _1960_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1285;
                    bool _out1286;
                    bool _out1287;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1288;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1285, out _out1286, out _out1287, out _out1288);
                    _1958_recursiveGen = _out1285;
                    _1959_recOwned = _out1286;
                    _1960_recErased = _out1287;
                    _1961_recIdents = _out1288;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1958_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1959_recOwned;
                    isErased = _1960_recErased;
                    readIdents = _1961_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _1962_recursiveGen;
                    bool _1963_recOwned;
                    bool _1964_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1965_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1289;
                    bool _out1290;
                    bool _out1291;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1289, out _out1290, out _out1291, out _out1292);
                    _1962_recursiveGen = _out1289;
                    _1963_recOwned = _out1290;
                    _1964_recErased = _out1291;
                    _1965_recIdents = _out1292;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1962_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1963_recOwned;
                    isErased = _1964_recErased;
                    readIdents = _1965_recIdents;
                  }
                }
              } else if (_source67.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1966___mcc_h1020 = _source67.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1967_recursiveGen;
                  bool _1968___v63;
                  bool _1969___v64;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1970_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1293;
                  bool _out1294;
                  bool _out1295;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1296;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, true, out _out1293, out _out1294, out _out1295, out _out1296);
                  _1967_recursiveGen = _out1293;
                  _1968___v63 = _out1294;
                  _1969___v64 = _out1295;
                  _1970_recIdents = _out1296;
                  Dafny.ISequence<Dafny.Rune> _1971_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1297;
                  _out1297 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                  _1971_toTpeGen = _out1297;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _1967_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _1971_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _1970_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1972___mcc_h1022 = _source67.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1973_recursiveGen;
                  bool _1974_recOwned;
                  bool _1975_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1976_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1298;
                  bool _out1299;
                  bool _out1300;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1298, out _out1299, out _out1300, out _out1301);
                  _1973_recursiveGen = _out1298;
                  _1974_recOwned = _out1299;
                  _1975_recErased = _out1300;
                  _1976_recIdents = _out1301;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1973_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1974_recOwned;
                  isErased = _1975_recErased;
                  readIdents = _1976_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _1977___mcc_h1024 = _source29.dtor_TypeArg_a0;
              DAST._IType _source70 = _542___mcc_h265;
              if (_source70.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1978___mcc_h1028 = _source70.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1979___mcc_h1029 = _source70.dtor_typeArgs;
                DAST._IResolvedType _1980___mcc_h1030 = _source70.dtor_resolved;
                DAST._IResolvedType _source71 = _1980___mcc_h1030;
                if (_source71.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1981___mcc_h1034 = _source71.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1982_recursiveGen;
                    bool _1983_recOwned;
                    bool _1984_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1985_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1302;
                    bool _out1303;
                    bool _out1304;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1302, out _out1303, out _out1304, out _out1305);
                    _1982_recursiveGen = _out1302;
                    _1983_recOwned = _out1303;
                    _1984_recErased = _out1304;
                    _1985_recIdents = _out1305;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1982_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1983_recOwned;
                    isErased = _1984_recErased;
                    readIdents = _1985_recIdents;
                  }
                } else if (_source71.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1986___mcc_h1036 = _source71.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1987_recursiveGen;
                    bool _1988_recOwned;
                    bool _1989_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1990_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1306;
                    bool _out1307;
                    bool _out1308;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1309;
                    DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1306, out _out1307, out _out1308, out _out1309);
                    _1987_recursiveGen = _out1306;
                    _1988_recOwned = _out1307;
                    _1989_recErased = _out1308;
                    _1990_recIdents = _out1309;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1987_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1988_recOwned;
                    isErased = _1989_recErased;
                    readIdents = _1990_recIdents;
                  }
                } else {
                  DAST._IType _1991___mcc_h1038 = _source71.dtor_Newtype_a0;
                  DAST._IType _1992_b = _1991___mcc_h1038;
                  {
                    if (object.Equals(_535_fromTpe, _1992_b)) {
                      Dafny.ISequence<Dafny.Rune> _1993_recursiveGen;
                      bool _1994_recOwned;
                      bool _1995_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1310;
                      bool _out1311;
                      bool _out1312;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
                      DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1310, out _out1311, out _out1312, out _out1313);
                      _1993_recursiveGen = _out1310;
                      _1994_recOwned = _out1311;
                      _1995_recErased = _out1312;
                      _1996_recIdents = _out1313;
                      Dafny.ISequence<Dafny.Rune> _1997_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1314;
                      _out1314 = DCOMP.COMP.GenType(_534_toTpe, true, false);
                      _1997_rhsType = _out1314;
                      Dafny.ISequence<Dafny.Rune> _1998_uneraseFn;
                      _1998_uneraseFn = ((_1994_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1997_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1998_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1993_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1994_recOwned;
                      isErased = false;
                      readIdents = _1996_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1315;
                      bool _out1316;
                      bool _out1317;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1318;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_536_expr, _535_fromTpe, _1992_b), _1992_b, _534_toTpe), selfIdent, @params, mustOwn, out _out1315, out _out1316, out _out1317, out _out1318);
                      s = _out1315;
                      isOwned = _out1316;
                      isErased = _out1317;
                      readIdents = _out1318;
                    }
                  }
                }
              } else if (_source70.is_Nullable) {
                DAST._IType _1999___mcc_h1040 = _source70.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2000_recursiveGen;
                  bool _2001_recOwned;
                  bool _2002_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2003_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1319;
                  bool _out1320;
                  bool _out1321;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1319, out _out1320, out _out1321, out _out1322);
                  _2000_recursiveGen = _out1319;
                  _2001_recOwned = _out1320;
                  _2002_recErased = _out1321;
                  _2003_recIdents = _out1322;
                  if (!(_2001_recOwned)) {
                    _2000_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_2000_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _2000_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _2002_recErased;
                  readIdents = _2003_recIdents;
                }
              } else if (_source70.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2004___mcc_h1042 = _source70.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2005_recursiveGen;
                  bool _2006_recOwned;
                  bool _2007_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2008_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1323;
                  bool _out1324;
                  bool _out1325;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1323, out _out1324, out _out1325, out _out1326);
                  _2005_recursiveGen = _out1323;
                  _2006_recOwned = _out1324;
                  _2007_recErased = _out1325;
                  _2008_recIdents = _out1326;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2005_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2006_recOwned;
                  isErased = _2007_recErased;
                  readIdents = _2008_recIdents;
                }
              } else if (_source70.is_Array) {
                DAST._IType _2009___mcc_h1044 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2010_recursiveGen;
                  bool _2011_recOwned;
                  bool _2012_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1327;
                  bool _out1328;
                  bool _out1329;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1330;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1327, out _out1328, out _out1329, out _out1330);
                  _2010_recursiveGen = _out1327;
                  _2011_recOwned = _out1328;
                  _2012_recErased = _out1329;
                  _2013_recIdents = _out1330;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2010_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2011_recOwned;
                  isErased = _2012_recErased;
                  readIdents = _2013_recIdents;
                }
              } else if (_source70.is_Seq) {
                DAST._IType _2014___mcc_h1046 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2015_recursiveGen;
                  bool _2016_recOwned;
                  bool _2017_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2018_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1331;
                  bool _out1332;
                  bool _out1333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1331, out _out1332, out _out1333, out _out1334);
                  _2015_recursiveGen = _out1331;
                  _2016_recOwned = _out1332;
                  _2017_recErased = _out1333;
                  _2018_recIdents = _out1334;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2015_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2016_recOwned;
                  isErased = _2017_recErased;
                  readIdents = _2018_recIdents;
                }
              } else if (_source70.is_Set) {
                DAST._IType _2019___mcc_h1048 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2020_recursiveGen;
                  bool _2021_recOwned;
                  bool _2022_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2023_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1335;
                  bool _out1336;
                  bool _out1337;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1335, out _out1336, out _out1337, out _out1338);
                  _2020_recursiveGen = _out1335;
                  _2021_recOwned = _out1336;
                  _2022_recErased = _out1337;
                  _2023_recIdents = _out1338;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2020_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2021_recOwned;
                  isErased = _2022_recErased;
                  readIdents = _2023_recIdents;
                }
              } else if (_source70.is_Multiset) {
                DAST._IType _2024___mcc_h1050 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2025_recursiveGen;
                  bool _2026_recOwned;
                  bool _2027_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2028_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1339;
                  bool _out1340;
                  bool _out1341;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1342;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1339, out _out1340, out _out1341, out _out1342);
                  _2025_recursiveGen = _out1339;
                  _2026_recOwned = _out1340;
                  _2027_recErased = _out1341;
                  _2028_recIdents = _out1342;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2025_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2026_recOwned;
                  isErased = _2027_recErased;
                  readIdents = _2028_recIdents;
                }
              } else if (_source70.is_Map) {
                DAST._IType _2029___mcc_h1052 = _source70.dtor_key;
                DAST._IType _2030___mcc_h1053 = _source70.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _2031_recursiveGen;
                  bool _2032_recOwned;
                  bool _2033_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2034_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1343;
                  bool _out1344;
                  bool _out1345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1346;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1343, out _out1344, out _out1345, out _out1346);
                  _2031_recursiveGen = _out1343;
                  _2032_recOwned = _out1344;
                  _2033_recErased = _out1345;
                  _2034_recIdents = _out1346;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2031_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2032_recOwned;
                  isErased = _2033_recErased;
                  readIdents = _2034_recIdents;
                }
              } else if (_source70.is_Arrow) {
                Dafny.ISequence<DAST._IType> _2035___mcc_h1056 = _source70.dtor_args;
                DAST._IType _2036___mcc_h1057 = _source70.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _2037_recursiveGen;
                  bool _2038_recOwned;
                  bool _2039_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2040_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1347;
                  bool _out1348;
                  bool _out1349;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1350;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1347, out _out1348, out _out1349, out _out1350);
                  _2037_recursiveGen = _out1347;
                  _2038_recOwned = _out1348;
                  _2039_recErased = _out1349;
                  _2040_recIdents = _out1350;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2037_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2038_recOwned;
                  isErased = _2039_recErased;
                  readIdents = _2040_recIdents;
                }
              } else if (_source70.is_Primitive) {
                DAST._IPrimitive _2041___mcc_h1060 = _source70.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2042_recursiveGen;
                  bool _2043_recOwned;
                  bool _2044_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2045_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1351;
                  bool _out1352;
                  bool _out1353;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1351, out _out1352, out _out1353, out _out1354);
                  _2042_recursiveGen = _out1351;
                  _2043_recOwned = _out1352;
                  _2044_recErased = _out1353;
                  _2045_recIdents = _out1354;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2042_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2043_recOwned;
                  isErased = _2044_recErased;
                  readIdents = _2045_recIdents;
                }
              } else if (_source70.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _2046___mcc_h1062 = _source70.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2047_recursiveGen;
                  bool _2048_recOwned;
                  bool _2049_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1355;
                  bool _out1356;
                  bool _out1357;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1358;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1355, out _out1356, out _out1357, out _out1358);
                  _2047_recursiveGen = _out1355;
                  _2048_recOwned = _out1356;
                  _2049_recErased = _out1357;
                  _2050_recIdents = _out1358;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2047_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2048_recOwned;
                  isErased = _2049_recErased;
                  readIdents = _2050_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _2051___mcc_h1064 = _source70.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2052_recursiveGen;
                  bool _2053_recOwned;
                  bool _2054_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2055_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1359;
                  bool _out1360;
                  bool _out1361;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
                  DCOMP.COMP.GenExpr(_536_expr, selfIdent, @params, mustOwn, out _out1359, out _out1360, out _out1361, out _out1362);
                  _2052_recursiveGen = _out1359;
                  _2053_recOwned = _out1360;
                  _2054_recErased = _out1361;
                  _2055_recIdents = _out1362;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2052_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2053_recOwned;
                  isErased = _2054_recErased;
                  readIdents = _2055_recIdents;
                }
              }
            }
          }
        }
      } else if (_source22.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _2056___mcc_h22 = _source22.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2057_exprs = _2056___mcc_h22;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2058_generatedValues;
          _2058_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2059_i;
          _2059_i = BigInteger.Zero;
          bool _2060_allErased;
          _2060_allErased = true;
          while ((_2059_i) < (new BigInteger((_2057_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2061_recursiveGen;
            bool _2062___v66;
            bool _2063_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2064_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1363;
            bool _out1364;
            bool _out1365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1366;
            DCOMP.COMP.GenExpr((_2057_exprs).Select(_2059_i), selfIdent, @params, true, out _out1363, out _out1364, out _out1365, out _out1366);
            _2061_recursiveGen = _out1363;
            _2062___v66 = _out1364;
            _2063_isErased = _out1365;
            _2064_recIdents = _out1366;
            _2060_allErased = (_2060_allErased) && (_2063_isErased);
            _2058_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2058_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2061_recursiveGen, _2063_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2064_recIdents);
            _2059_i = (_2059_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2059_i = BigInteger.Zero;
          while ((_2059_i) < (new BigInteger((_2058_generatedValues).Count))) {
            if ((_2059_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2065_gen;
            _2065_gen = ((_2058_generatedValues).Select(_2059_i)).dtor__0;
            if ((((_2058_generatedValues).Select(_2059_i)).dtor__1) && (!(_2060_allErased))) {
              _2065_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2065_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2065_gen);
            _2059_i = (_2059_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _2060_allErased;
        }
      } else if (_source22.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _2066___mcc_h23 = _source22.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2067_exprs = _2066___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2068_generatedValues;
          _2068_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2069_i;
          _2069_i = BigInteger.Zero;
          bool _2070_allErased;
          _2070_allErased = true;
          while ((_2069_i) < (new BigInteger((_2067_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2071_recursiveGen;
            bool _2072___v67;
            bool _2073_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2074_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1367;
            bool _out1368;
            bool _out1369;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
            DCOMP.COMP.GenExpr((_2067_exprs).Select(_2069_i), selfIdent, @params, true, out _out1367, out _out1368, out _out1369, out _out1370);
            _2071_recursiveGen = _out1367;
            _2072___v67 = _out1368;
            _2073_isErased = _out1369;
            _2074_recIdents = _out1370;
            _2070_allErased = (_2070_allErased) && (_2073_isErased);
            _2068_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2068_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2071_recursiveGen, _2073_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2074_recIdents);
            _2069_i = (_2069_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2069_i = BigInteger.Zero;
          while ((_2069_i) < (new BigInteger((_2068_generatedValues).Count))) {
            if ((_2069_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2075_gen;
            _2075_gen = ((_2068_generatedValues).Select(_2069_i)).dtor__0;
            if ((((_2068_generatedValues).Select(_2069_i)).dtor__1) && (!(_2070_allErased))) {
              _2075_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2075_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2075_gen);
            _2069_i = (_2069_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashSet<_>>()"));
          isOwned = true;
          isErased = _2070_allErased;
        }
      } else if (_source22.is_MapValue) {
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2076___mcc_h24 = _source22.dtor_mapElems;
        Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2077_mapElems = _2076___mcc_h24;
        {
          Dafny.ISequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>> _2078_generatedValues;
          _2078_generatedValues = Dafny.Sequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2079_i;
          _2079_i = BigInteger.Zero;
          bool _2080_allErased;
          _2080_allErased = true;
          while ((_2079_i) < (new BigInteger((_2077_mapElems).Count))) {
            Dafny.ISequence<Dafny.Rune> _2081_recursiveGenKey;
            bool _2082___v68;
            bool _2083_isErasedKey;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2084_recIdentsKey;
            Dafny.ISequence<Dafny.Rune> _out1371;
            bool _out1372;
            bool _out1373;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
            DCOMP.COMP.GenExpr(((_2077_mapElems).Select(_2079_i)).dtor__0, selfIdent, @params, true, out _out1371, out _out1372, out _out1373, out _out1374);
            _2081_recursiveGenKey = _out1371;
            _2082___v68 = _out1372;
            _2083_isErasedKey = _out1373;
            _2084_recIdentsKey = _out1374;
            Dafny.ISequence<Dafny.Rune> _2085_recursiveGenValue;
            bool _2086___v69;
            bool _2087_isErasedValue;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2088_recIdentsValue;
            Dafny.ISequence<Dafny.Rune> _out1375;
            bool _out1376;
            bool _out1377;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1378;
            DCOMP.COMP.GenExpr(((_2077_mapElems).Select(_2079_i)).dtor__1, selfIdent, @params, true, out _out1375, out _out1376, out _out1377, out _out1378);
            _2085_recursiveGenValue = _out1375;
            _2086___v69 = _out1376;
            _2087_isErasedValue = _out1377;
            _2088_recIdentsValue = _out1378;
            _2080_allErased = ((_2080_allErased) && (_2083_isErasedKey)) && (_2087_isErasedValue);
            _2078_generatedValues = Dafny.Sequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>>.Concat(_2078_generatedValues, Dafny.Sequence<_System._ITuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>>.FromElements(_System.Tuple4<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, bool, bool>.create(_2081_recursiveGenKey, _2085_recursiveGenValue, _2083_isErasedKey, _2087_isErasedValue)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2084_recIdentsKey), _2088_recIdentsValue);
            _2079_i = (_2079_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2079_i = BigInteger.Zero;
          while ((_2079_i) < (new BigInteger((_2078_generatedValues).Count))) {
            if ((_2079_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2089_genKey;
            _2089_genKey = ((_2078_generatedValues).Select(_2079_i)).dtor__0;
            Dafny.ISequence<Dafny.Rune> _2090_genValue;
            _2090_genValue = ((_2078_generatedValues).Select(_2079_i)).dtor__1;
            if ((((_2078_generatedValues).Select(_2079_i)).dtor__2) && (!(_2080_allErased))) {
              _2089_genKey = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2089_genKey), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((((_2078_generatedValues).Select(_2079_i)).dtor__3) && (!(_2080_allErased))) {
              _2090_genValue = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2090_genValue), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2089_genKey), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2090_genValue), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            _2079_i = (_2079_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashMap<_, _>>()"));
          isOwned = true;
          isErased = _2080_allErased;
        }
      } else if (_source22.is_This) {
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source72 = selfIdent;
          if (_source72.is_Some) {
            Dafny.ISequence<Dafny.Rune> _2091___mcc_h1066 = _source72.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _2092_id = _2091___mcc_h1066;
            {
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(_2092_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                isOwned = true;
              } else {
                if ((_2092_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
                } else {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2092_id);
                }
                isOwned = false;
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2092_id);
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
        DAST._IExpression _2093___mcc_h25 = _source22.dtor_cond;
        DAST._IExpression _2094___mcc_h26 = _source22.dtor_thn;
        DAST._IExpression _2095___mcc_h27 = _source22.dtor_els;
        DAST._IExpression _2096_f = _2095___mcc_h27;
        DAST._IExpression _2097_t = _2094___mcc_h26;
        DAST._IExpression _2098_cond = _2093___mcc_h25;
        {
          Dafny.ISequence<Dafny.Rune> _2099_condString;
          bool _2100___v70;
          bool _2101_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2102_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1379;
          bool _out1380;
          bool _out1381;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1382;
          DCOMP.COMP.GenExpr(_2098_cond, selfIdent, @params, true, out _out1379, out _out1380, out _out1381, out _out1382);
          _2099_condString = _out1379;
          _2100___v70 = _out1380;
          _2101_condErased = _out1381;
          _2102_recIdentsCond = _out1382;
          if (!(_2101_condErased)) {
            _2099_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2099_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2103___v71;
          bool _2104_tHasToBeOwned;
          bool _2105___v72;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2106___v73;
          Dafny.ISequence<Dafny.Rune> _out1383;
          bool _out1384;
          bool _out1385;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1386;
          DCOMP.COMP.GenExpr(_2097_t, selfIdent, @params, mustOwn, out _out1383, out _out1384, out _out1385, out _out1386);
          _2103___v71 = _out1383;
          _2104_tHasToBeOwned = _out1384;
          _2105___v72 = _out1385;
          _2106___v73 = _out1386;
          Dafny.ISequence<Dafny.Rune> _2107_fString;
          bool _2108_fOwned;
          bool _2109_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2110_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1387;
          bool _out1388;
          bool _out1389;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1390;
          DCOMP.COMP.GenExpr(_2096_f, selfIdent, @params, _2104_tHasToBeOwned, out _out1387, out _out1388, out _out1389, out _out1390);
          _2107_fString = _out1387;
          _2108_fOwned = _out1388;
          _2109_fErased = _out1389;
          _2110_recIdentsF = _out1390;
          Dafny.ISequence<Dafny.Rune> _2111_tString;
          bool _2112___v74;
          bool _2113_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2114_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1391;
          bool _out1392;
          bool _out1393;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
          DCOMP.COMP.GenExpr(_2097_t, selfIdent, @params, _2108_fOwned, out _out1391, out _out1392, out _out1393, out _out1394);
          _2111_tString = _out1391;
          _2112___v74 = _out1392;
          _2113_tErased = _out1393;
          _2114_recIdentsT = _out1394;
          if ((!(_2109_fErased)) || (!(_2113_tErased))) {
            if (_2109_fErased) {
              _2107_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2107_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2113_tErased) {
              _2111_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2111_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _2099_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2111_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _2107_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _2108_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2102_recIdentsCond, _2114_recIdentsT), _2110_recIdentsF);
          isErased = (_2109_fErased) || (_2113_tErased);
        }
      } else if (_source22.is_UnOp) {
        DAST._IUnaryOp _2115___mcc_h28 = _source22.dtor_unOp;
        DAST._IExpression _2116___mcc_h29 = _source22.dtor_expr;
        DAST._IUnaryOp _source73 = _2115___mcc_h28;
        if (_source73.is_Not) {
          DAST._IExpression _2117_e = _2116___mcc_h29;
          {
            Dafny.ISequence<Dafny.Rune> _2118_recursiveGen;
            bool _2119___v75;
            bool _2120_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2121_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1395;
            bool _out1396;
            bool _out1397;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1398;
            DCOMP.COMP.GenExpr(_2117_e, selfIdent, @params, true, out _out1395, out _out1396, out _out1397, out _out1398);
            _2118_recursiveGen = _out1395;
            _2119___v75 = _out1396;
            _2120_recErased = _out1397;
            _2121_recIdents = _out1398;
            if (!(_2120_recErased)) {
              _2118_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2118_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _2118_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2121_recIdents;
            isErased = true;
          }
        } else if (_source73.is_BitwiseNot) {
          DAST._IExpression _2122_e = _2116___mcc_h29;
          {
            Dafny.ISequence<Dafny.Rune> _2123_recursiveGen;
            bool _2124___v76;
            bool _2125_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2126_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1399;
            bool _out1400;
            bool _out1401;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
            DCOMP.COMP.GenExpr(_2122_e, selfIdent, @params, true, out _out1399, out _out1400, out _out1401, out _out1402);
            _2123_recursiveGen = _out1399;
            _2124___v76 = _out1400;
            _2125_recErased = _out1401;
            _2126_recIdents = _out1402;
            if (!(_2125_recErased)) {
              _2123_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2123_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _2123_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2126_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _2127_e = _2116___mcc_h29;
          {
            Dafny.ISequence<Dafny.Rune> _2128_recursiveGen;
            bool _2129_recOwned;
            bool _2130_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2131_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1403;
            bool _out1404;
            bool _out1405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1406;
            DCOMP.COMP.GenExpr(_2127_e, selfIdent, @params, false, out _out1403, out _out1404, out _out1405, out _out1406);
            _2128_recursiveGen = _out1403;
            _2129_recOwned = _out1404;
            _2130_recErased = _out1405;
            _2131_recIdents = _out1406;
            if (!(_2130_recErased)) {
              Dafny.ISequence<Dafny.Rune> _2132_eraseFn;
              _2132_eraseFn = ((_2129_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2128_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2132_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2128_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2128_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len())"));
            isOwned = true;
            readIdents = _2131_recIdents;
            isErased = true;
          }
        }
      } else if (_source22.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _2133___mcc_h30 = _source22.dtor_op;
        DAST._IExpression _2134___mcc_h31 = _source22.dtor_left;
        DAST._IExpression _2135___mcc_h32 = _source22.dtor_right;
        DAST._IExpression _2136_r = _2135___mcc_h32;
        DAST._IExpression _2137_l = _2134___mcc_h31;
        Dafny.ISequence<Dafny.Rune> _2138_op = _2133___mcc_h30;
        {
          Dafny.ISequence<Dafny.Rune> _2139_left;
          bool _2140___v77;
          bool _2141_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2142_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1407;
          bool _out1408;
          bool _out1409;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1410;
          DCOMP.COMP.GenExpr(_2137_l, selfIdent, @params, true, out _out1407, out _out1408, out _out1409, out _out1410);
          _2139_left = _out1407;
          _2140___v77 = _out1408;
          _2141_leftErased = _out1409;
          _2142_recIdentsL = _out1410;
          Dafny.ISequence<Dafny.Rune> _2143_right;
          bool _2144___v78;
          bool _2145_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2146_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1411;
          bool _out1412;
          bool _out1413;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1414;
          DCOMP.COMP.GenExpr(_2136_r, selfIdent, @params, true, out _out1411, out _out1412, out _out1413, out _out1414);
          _2143_right = _out1411;
          _2144___v78 = _out1412;
          _2145_rightErased = _out1413;
          _2146_recIdentsR = _out1414;
          if (!(_2141_leftErased)) {
            _2139_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2139_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_2145_rightErased)) {
            _2143_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2143_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_2138_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _2139_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2143_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_2138_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _2139_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2143_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2139_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2138_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2143_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2142_recIdentsL, _2146_recIdentsR);
          isErased = true;
        }
      } else if (_source22.is_ArrayLen) {
        DAST._IExpression _2147___mcc_h33 = _source22.dtor_expr;
        DAST._IExpression _2148_expr = _2147___mcc_h33;
        {
          Dafny.ISequence<Dafny.Rune> _2149_recursiveGen;
          bool _2150___v79;
          bool _2151_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2152_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1415;
          bool _out1416;
          bool _out1417;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
          DCOMP.COMP.GenExpr(_2148_expr, selfIdent, @params, true, out _out1415, out _out1416, out _out1417, out _out1418);
          _2149_recursiveGen = _out1415;
          _2150___v79 = _out1416;
          _2151_recErased = _out1417;
          _2152_recIdents = _out1418;
          if (!(_2151_recErased)) {
            _2149_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2149_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2149_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())"));
          isOwned = true;
          readIdents = _2152_recIdents;
          isErased = true;
        }
      } else if (_source22.is_Select) {
        DAST._IExpression _2153___mcc_h34 = _source22.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2154___mcc_h35 = _source22.dtor_field;
        bool _2155___mcc_h36 = _source22.dtor_isConstant;
        bool _2156___mcc_h37 = _source22.dtor_onDatatype;
        DAST._IExpression _source74 = _2153___mcc_h34;
        if (_source74.is_Literal) {
          DAST._ILiteral _2157___mcc_h38 = _source74.dtor_Literal_a0;
          bool _2158_isDatatype = _2156___mcc_h37;
          bool _2159_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2160_field = _2154___mcc_h35;
          DAST._IExpression _2161_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2162_onString;
            bool _2163_onOwned;
            bool _2164_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2165_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1419;
            bool _out1420;
            bool _out1421;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1422;
            DCOMP.COMP.GenExpr(_2161_on, selfIdent, @params, false, out _out1419, out _out1420, out _out1421, out _out1422);
            _2162_onString = _out1419;
            _2163_onOwned = _out1420;
            _2164_onErased = _out1421;
            _2165_recIdents = _out1422;
            if (!(_2164_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2166_eraseFn;
              _2166_eraseFn = ((_2163_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2162_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2166_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2162_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2158_isDatatype) || (_2159_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2162_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2160_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2159_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2162_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2160_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2165_recIdents;
          }
        } else if (_source74.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2167___mcc_h40 = _source74.dtor_Ident_a0;
          bool _2168_isDatatype = _2156___mcc_h37;
          bool _2169_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2170_field = _2154___mcc_h35;
          DAST._IExpression _2171_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2172_onString;
            bool _2173_onOwned;
            bool _2174_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1423;
            bool _out1424;
            bool _out1425;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1426;
            DCOMP.COMP.GenExpr(_2171_on, selfIdent, @params, false, out _out1423, out _out1424, out _out1425, out _out1426);
            _2172_onString = _out1423;
            _2173_onOwned = _out1424;
            _2174_onErased = _out1425;
            _2175_recIdents = _out1426;
            if (!(_2174_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2176_eraseFn;
              _2176_eraseFn = ((_2173_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2172_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2176_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2172_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2168_isDatatype) || (_2169_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2172_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2170_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2169_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2172_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2170_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2175_recIdents;
          }
        } else if (_source74.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2177___mcc_h42 = _source74.dtor_Companion_a0;
          bool _2178_isDatatype = _2156___mcc_h37;
          bool _2179_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2180_field = _2154___mcc_h35;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2181_c = _2177___mcc_h42;
          {
            Dafny.ISequence<Dafny.Rune> _2182_onString;
            bool _2183_onOwned;
            bool _2184_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2185_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1427;
            bool _out1428;
            bool _out1429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1430;
            DCOMP.COMP.GenExpr(DAST.Expression.create_Companion(_2181_c), selfIdent, @params, false, out _out1427, out _out1428, out _out1429, out _out1430);
            _2182_onString = _out1427;
            _2183_onOwned = _out1428;
            _2184_onErased = _out1429;
            _2185_recIdents = _out1430;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2182_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2180_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            isOwned = true;
            isErased = false;
            readIdents = _2185_recIdents;
          }
        } else if (_source74.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2186___mcc_h44 = _source74.dtor_Tuple_a0;
          bool _2187_isDatatype = _2156___mcc_h37;
          bool _2188_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2189_field = _2154___mcc_h35;
          DAST._IExpression _2190_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2191_onString;
            bool _2192_onOwned;
            bool _2193_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1431;
            bool _out1432;
            bool _out1433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1434;
            DCOMP.COMP.GenExpr(_2190_on, selfIdent, @params, false, out _out1431, out _out1432, out _out1433, out _out1434);
            _2191_onString = _out1431;
            _2192_onOwned = _out1432;
            _2193_onErased = _out1433;
            _2194_recIdents = _out1434;
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
        } else if (_source74.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2196___mcc_h46 = _source74.dtor_path;
          Dafny.ISequence<DAST._IExpression> _2197___mcc_h47 = _source74.dtor_args;
          bool _2198_isDatatype = _2156___mcc_h37;
          bool _2199_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2200_field = _2154___mcc_h35;
          DAST._IExpression _2201_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2202_onString;
            bool _2203_onOwned;
            bool _2204_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2205_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1435;
            bool _out1436;
            bool _out1437;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1438;
            DCOMP.COMP.GenExpr(_2201_on, selfIdent, @params, false, out _out1435, out _out1436, out _out1437, out _out1438);
            _2202_onString = _out1435;
            _2203_onOwned = _out1436;
            _2204_onErased = _out1437;
            _2205_recIdents = _out1438;
            if (!(_2204_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2206_eraseFn;
              _2206_eraseFn = ((_2203_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2202_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2206_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2202_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2198_isDatatype) || (_2199_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2202_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2200_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2199_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2202_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2200_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2205_recIdents;
          }
        } else if (_source74.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _2207___mcc_h50 = _source74.dtor_dims;
          bool _2208_isDatatype = _2156___mcc_h37;
          bool _2209_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2210_field = _2154___mcc_h35;
          DAST._IExpression _2211_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2212_onString;
            bool _2213_onOwned;
            bool _2214_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2215_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1439;
            bool _out1440;
            bool _out1441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
            DCOMP.COMP.GenExpr(_2211_on, selfIdent, @params, false, out _out1439, out _out1440, out _out1441, out _out1442);
            _2212_onString = _out1439;
            _2213_onOwned = _out1440;
            _2214_onErased = _out1441;
            _2215_recIdents = _out1442;
            if (!(_2214_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2216_eraseFn;
              _2216_eraseFn = ((_2213_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2212_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2216_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2212_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2208_isDatatype) || (_2209_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2212_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2210_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2209_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2212_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2210_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2215_recIdents;
          }
        } else if (_source74.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2217___mcc_h52 = _source74.dtor_path;
          Dafny.ISequence<Dafny.Rune> _2218___mcc_h53 = _source74.dtor_variant;
          bool _2219___mcc_h54 = _source74.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2220___mcc_h55 = _source74.dtor_contents;
          bool _2221_isDatatype = _2156___mcc_h37;
          bool _2222_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2223_field = _2154___mcc_h35;
          DAST._IExpression _2224_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2225_onString;
            bool _2226_onOwned;
            bool _2227_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2228_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1443;
            bool _out1444;
            bool _out1445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1446;
            DCOMP.COMP.GenExpr(_2224_on, selfIdent, @params, false, out _out1443, out _out1444, out _out1445, out _out1446);
            _2225_onString = _out1443;
            _2226_onOwned = _out1444;
            _2227_onErased = _out1445;
            _2228_recIdents = _out1446;
            if (!(_2227_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2229_eraseFn;
              _2229_eraseFn = ((_2226_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2225_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2229_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2225_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2221_isDatatype) || (_2222_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2225_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2223_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2222_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2225_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2223_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2228_recIdents;
          }
        } else if (_source74.is_Convert) {
          DAST._IExpression _2230___mcc_h60 = _source74.dtor_value;
          DAST._IType _2231___mcc_h61 = _source74.dtor_from;
          DAST._IType _2232___mcc_h62 = _source74.dtor_typ;
          bool _2233_isDatatype = _2156___mcc_h37;
          bool _2234_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2235_field = _2154___mcc_h35;
          DAST._IExpression _2236_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2237_onString;
            bool _2238_onOwned;
            bool _2239_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2240_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1447;
            bool _out1448;
            bool _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            DCOMP.COMP.GenExpr(_2236_on, selfIdent, @params, false, out _out1447, out _out1448, out _out1449, out _out1450);
            _2237_onString = _out1447;
            _2238_onOwned = _out1448;
            _2239_onErased = _out1449;
            _2240_recIdents = _out1450;
            if (!(_2239_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2241_eraseFn;
              _2241_eraseFn = ((_2238_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2237_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2241_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2237_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2233_isDatatype) || (_2234_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2237_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2235_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2234_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2237_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2235_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2240_recIdents;
          }
        } else if (_source74.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2242___mcc_h66 = _source74.dtor_elements;
          bool _2243_isDatatype = _2156___mcc_h37;
          bool _2244_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2245_field = _2154___mcc_h35;
          DAST._IExpression _2246_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2247_onString;
            bool _2248_onOwned;
            bool _2249_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2250_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1451;
            bool _out1452;
            bool _out1453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1454;
            DCOMP.COMP.GenExpr(_2246_on, selfIdent, @params, false, out _out1451, out _out1452, out _out1453, out _out1454);
            _2247_onString = _out1451;
            _2248_onOwned = _out1452;
            _2249_onErased = _out1453;
            _2250_recIdents = _out1454;
            if (!(_2249_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2251_eraseFn;
              _2251_eraseFn = ((_2248_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2247_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2251_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2247_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2243_isDatatype) || (_2244_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2247_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2245_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2244_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2247_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2245_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2250_recIdents;
          }
        } else if (_source74.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2252___mcc_h68 = _source74.dtor_elements;
          bool _2253_isDatatype = _2156___mcc_h37;
          bool _2254_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2255_field = _2154___mcc_h35;
          DAST._IExpression _2256_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2257_onString;
            bool _2258_onOwned;
            bool _2259_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2260_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1455;
            bool _out1456;
            bool _out1457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1458;
            DCOMP.COMP.GenExpr(_2256_on, selfIdent, @params, false, out _out1455, out _out1456, out _out1457, out _out1458);
            _2257_onString = _out1455;
            _2258_onOwned = _out1456;
            _2259_onErased = _out1457;
            _2260_recIdents = _out1458;
            if (!(_2259_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2261_eraseFn;
              _2261_eraseFn = ((_2258_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2257_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2261_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2257_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2253_isDatatype) || (_2254_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2257_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2255_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2254_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2257_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2255_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2260_recIdents;
          }
        } else if (_source74.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2262___mcc_h70 = _source74.dtor_mapElems;
          bool _2263_isDatatype = _2156___mcc_h37;
          bool _2264_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2265_field = _2154___mcc_h35;
          DAST._IExpression _2266_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2267_onString;
            bool _2268_onOwned;
            bool _2269_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2270_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1459;
            bool _out1460;
            bool _out1461;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
            DCOMP.COMP.GenExpr(_2266_on, selfIdent, @params, false, out _out1459, out _out1460, out _out1461, out _out1462);
            _2267_onString = _out1459;
            _2268_onOwned = _out1460;
            _2269_onErased = _out1461;
            _2270_recIdents = _out1462;
            if (!(_2269_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2271_eraseFn;
              _2271_eraseFn = ((_2268_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2267_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2271_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2267_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2263_isDatatype) || (_2264_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2267_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2265_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2264_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2267_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2265_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2270_recIdents;
          }
        } else if (_source74.is_This) {
          bool _2272_isDatatype = _2156___mcc_h37;
          bool _2273_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2274_field = _2154___mcc_h35;
          DAST._IExpression _2275_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2276_onString;
            bool _2277_onOwned;
            bool _2278_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2279_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1463;
            bool _out1464;
            bool _out1465;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1466;
            DCOMP.COMP.GenExpr(_2275_on, selfIdent, @params, false, out _out1463, out _out1464, out _out1465, out _out1466);
            _2276_onString = _out1463;
            _2277_onOwned = _out1464;
            _2278_onErased = _out1465;
            _2279_recIdents = _out1466;
            if (!(_2278_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2280_eraseFn;
              _2280_eraseFn = ((_2277_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2276_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2280_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2276_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2272_isDatatype) || (_2273_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2276_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2274_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2273_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2276_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2274_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2279_recIdents;
          }
        } else if (_source74.is_Ite) {
          DAST._IExpression _2281___mcc_h72 = _source74.dtor_cond;
          DAST._IExpression _2282___mcc_h73 = _source74.dtor_thn;
          DAST._IExpression _2283___mcc_h74 = _source74.dtor_els;
          bool _2284_isDatatype = _2156___mcc_h37;
          bool _2285_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2286_field = _2154___mcc_h35;
          DAST._IExpression _2287_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2288_onString;
            bool _2289_onOwned;
            bool _2290_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2291_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1467;
            bool _out1468;
            bool _out1469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
            DCOMP.COMP.GenExpr(_2287_on, selfIdent, @params, false, out _out1467, out _out1468, out _out1469, out _out1470);
            _2288_onString = _out1467;
            _2289_onOwned = _out1468;
            _2290_onErased = _out1469;
            _2291_recIdents = _out1470;
            if (!(_2290_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2292_eraseFn;
              _2292_eraseFn = ((_2289_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2288_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2292_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2288_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2284_isDatatype) || (_2285_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2288_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2286_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2285_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2288_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2286_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2291_recIdents;
          }
        } else if (_source74.is_UnOp) {
          DAST._IUnaryOp _2293___mcc_h78 = _source74.dtor_unOp;
          DAST._IExpression _2294___mcc_h79 = _source74.dtor_expr;
          bool _2295_isDatatype = _2156___mcc_h37;
          bool _2296_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2297_field = _2154___mcc_h35;
          DAST._IExpression _2298_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2299_onString;
            bool _2300_onOwned;
            bool _2301_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2302_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1471;
            bool _out1472;
            bool _out1473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1474;
            DCOMP.COMP.GenExpr(_2298_on, selfIdent, @params, false, out _out1471, out _out1472, out _out1473, out _out1474);
            _2299_onString = _out1471;
            _2300_onOwned = _out1472;
            _2301_onErased = _out1473;
            _2302_recIdents = _out1474;
            if (!(_2301_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2303_eraseFn;
              _2303_eraseFn = ((_2300_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2299_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2303_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2299_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2295_isDatatype) || (_2296_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2299_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2297_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2296_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2299_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2297_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2302_recIdents;
          }
        } else if (_source74.is_BinOp) {
          Dafny.ISequence<Dafny.Rune> _2304___mcc_h82 = _source74.dtor_op;
          DAST._IExpression _2305___mcc_h83 = _source74.dtor_left;
          DAST._IExpression _2306___mcc_h84 = _source74.dtor_right;
          bool _2307_isDatatype = _2156___mcc_h37;
          bool _2308_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2309_field = _2154___mcc_h35;
          DAST._IExpression _2310_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2311_onString;
            bool _2312_onOwned;
            bool _2313_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2314_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1475;
            bool _out1476;
            bool _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            DCOMP.COMP.GenExpr(_2310_on, selfIdent, @params, false, out _out1475, out _out1476, out _out1477, out _out1478);
            _2311_onString = _out1475;
            _2312_onOwned = _out1476;
            _2313_onErased = _out1477;
            _2314_recIdents = _out1478;
            if (!(_2313_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2315_eraseFn;
              _2315_eraseFn = ((_2312_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2311_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2315_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2311_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2307_isDatatype) || (_2308_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2311_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2309_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2308_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2311_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2309_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2314_recIdents;
          }
        } else if (_source74.is_ArrayLen) {
          DAST._IExpression _2316___mcc_h88 = _source74.dtor_expr;
          bool _2317_isDatatype = _2156___mcc_h37;
          bool _2318_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2319_field = _2154___mcc_h35;
          DAST._IExpression _2320_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2321_onString;
            bool _2322_onOwned;
            bool _2323_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2324_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1479;
            bool _out1480;
            bool _out1481;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1482;
            DCOMP.COMP.GenExpr(_2320_on, selfIdent, @params, false, out _out1479, out _out1480, out _out1481, out _out1482);
            _2321_onString = _out1479;
            _2322_onOwned = _out1480;
            _2323_onErased = _out1481;
            _2324_recIdents = _out1482;
            if (!(_2323_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2325_eraseFn;
              _2325_eraseFn = ((_2322_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2321_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2325_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2321_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2317_isDatatype) || (_2318_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2321_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2319_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2318_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2321_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2319_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2324_recIdents;
          }
        } else if (_source74.is_Select) {
          DAST._IExpression _2326___mcc_h90 = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2327___mcc_h91 = _source74.dtor_field;
          bool _2328___mcc_h92 = _source74.dtor_isConstant;
          bool _2329___mcc_h93 = _source74.dtor_onDatatype;
          bool _2330_isDatatype = _2156___mcc_h37;
          bool _2331_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2332_field = _2154___mcc_h35;
          DAST._IExpression _2333_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2334_onString;
            bool _2335_onOwned;
            bool _2336_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2337_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1483;
            bool _out1484;
            bool _out1485;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
            DCOMP.COMP.GenExpr(_2333_on, selfIdent, @params, false, out _out1483, out _out1484, out _out1485, out _out1486);
            _2334_onString = _out1483;
            _2335_onOwned = _out1484;
            _2336_onErased = _out1485;
            _2337_recIdents = _out1486;
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
        } else if (_source74.is_SelectFn) {
          DAST._IExpression _2339___mcc_h98 = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2340___mcc_h99 = _source74.dtor_field;
          bool _2341___mcc_h100 = _source74.dtor_onDatatype;
          bool _2342___mcc_h101 = _source74.dtor_isStatic;
          BigInteger _2343___mcc_h102 = _source74.dtor_arity;
          bool _2344_isDatatype = _2156___mcc_h37;
          bool _2345_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2346_field = _2154___mcc_h35;
          DAST._IExpression _2347_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2348_onString;
            bool _2349_onOwned;
            bool _2350_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2351_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1487;
            bool _out1488;
            bool _out1489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1490;
            DCOMP.COMP.GenExpr(_2347_on, selfIdent, @params, false, out _out1487, out _out1488, out _out1489, out _out1490);
            _2348_onString = _out1487;
            _2349_onOwned = _out1488;
            _2350_onErased = _out1489;
            _2351_recIdents = _out1490;
            if (!(_2350_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2352_eraseFn;
              _2352_eraseFn = ((_2349_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2348_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2352_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2348_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2344_isDatatype) || (_2345_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2348_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2346_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2345_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2348_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2346_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2351_recIdents;
          }
        } else if (_source74.is_Index) {
          DAST._IExpression _2353___mcc_h108 = _source74.dtor_expr;
          DAST._ICollKind _2354___mcc_h109 = _source74.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2355___mcc_h110 = _source74.dtor_indices;
          bool _2356_isDatatype = _2156___mcc_h37;
          bool _2357_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2358_field = _2154___mcc_h35;
          DAST._IExpression _2359_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2360_onString;
            bool _2361_onOwned;
            bool _2362_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2363_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1491;
            bool _out1492;
            bool _out1493;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1494;
            DCOMP.COMP.GenExpr(_2359_on, selfIdent, @params, false, out _out1491, out _out1492, out _out1493, out _out1494);
            _2360_onString = _out1491;
            _2361_onOwned = _out1492;
            _2362_onErased = _out1493;
            _2363_recIdents = _out1494;
            if (!(_2362_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2364_eraseFn;
              _2364_eraseFn = ((_2361_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2360_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2364_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2360_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2356_isDatatype) || (_2357_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2360_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2358_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2357_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2360_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2358_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2363_recIdents;
          }
        } else if (_source74.is_IndexRange) {
          DAST._IExpression _2365___mcc_h114 = _source74.dtor_expr;
          bool _2366___mcc_h115 = _source74.dtor_isArray;
          DAST._IOptional<DAST._IExpression> _2367___mcc_h116 = _source74.dtor_low;
          DAST._IOptional<DAST._IExpression> _2368___mcc_h117 = _source74.dtor_high;
          bool _2369_isDatatype = _2156___mcc_h37;
          bool _2370_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2371_field = _2154___mcc_h35;
          DAST._IExpression _2372_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2373_onString;
            bool _2374_onOwned;
            bool _2375_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2376_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1495;
            bool _out1496;
            bool _out1497;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1498;
            DCOMP.COMP.GenExpr(_2372_on, selfIdent, @params, false, out _out1495, out _out1496, out _out1497, out _out1498);
            _2373_onString = _out1495;
            _2374_onOwned = _out1496;
            _2375_onErased = _out1497;
            _2376_recIdents = _out1498;
            if (!(_2375_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2377_eraseFn;
              _2377_eraseFn = ((_2374_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2373_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2377_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2373_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2369_isDatatype) || (_2370_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2373_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2371_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2370_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2373_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2371_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2376_recIdents;
          }
        } else if (_source74.is_TupleSelect) {
          DAST._IExpression _2378___mcc_h122 = _source74.dtor_expr;
          BigInteger _2379___mcc_h123 = _source74.dtor_index;
          bool _2380_isDatatype = _2156___mcc_h37;
          bool _2381_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2382_field = _2154___mcc_h35;
          DAST._IExpression _2383_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2384_onString;
            bool _2385_onOwned;
            bool _2386_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2387_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1499;
            bool _out1500;
            bool _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            DCOMP.COMP.GenExpr(_2383_on, selfIdent, @params, false, out _out1499, out _out1500, out _out1501, out _out1502);
            _2384_onString = _out1499;
            _2385_onOwned = _out1500;
            _2386_onErased = _out1501;
            _2387_recIdents = _out1502;
            if (!(_2386_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2388_eraseFn;
              _2388_eraseFn = ((_2385_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2384_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2388_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2384_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2380_isDatatype) || (_2381_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2384_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2382_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2381_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2384_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2382_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2387_recIdents;
          }
        } else if (_source74.is_Call) {
          DAST._IExpression _2389___mcc_h126 = _source74.dtor_on;
          Dafny.ISequence<Dafny.Rune> _2390___mcc_h127 = _source74.dtor_name;
          Dafny.ISequence<DAST._IType> _2391___mcc_h128 = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2392___mcc_h129 = _source74.dtor_args;
          bool _2393_isDatatype = _2156___mcc_h37;
          bool _2394_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2395_field = _2154___mcc_h35;
          DAST._IExpression _2396_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2397_onString;
            bool _2398_onOwned;
            bool _2399_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2400_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1503;
            bool _out1504;
            bool _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            DCOMP.COMP.GenExpr(_2396_on, selfIdent, @params, false, out _out1503, out _out1504, out _out1505, out _out1506);
            _2397_onString = _out1503;
            _2398_onOwned = _out1504;
            _2399_onErased = _out1505;
            _2400_recIdents = _out1506;
            if (!(_2399_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2401_eraseFn;
              _2401_eraseFn = ((_2398_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2397_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2401_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2397_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2393_isDatatype) || (_2394_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2397_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2395_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2394_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2397_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2395_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2400_recIdents;
          }
        } else if (_source74.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2402___mcc_h134 = _source74.dtor_params;
          DAST._IType _2403___mcc_h135 = _source74.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2404___mcc_h136 = _source74.dtor_body;
          bool _2405_isDatatype = _2156___mcc_h37;
          bool _2406_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2407_field = _2154___mcc_h35;
          DAST._IExpression _2408_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2409_onString;
            bool _2410_onOwned;
            bool _2411_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2412_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1507;
            bool _out1508;
            bool _out1509;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1510;
            DCOMP.COMP.GenExpr(_2408_on, selfIdent, @params, false, out _out1507, out _out1508, out _out1509, out _out1510);
            _2409_onString = _out1507;
            _2410_onOwned = _out1508;
            _2411_onErased = _out1509;
            _2412_recIdents = _out1510;
            if (!(_2411_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2413_eraseFn;
              _2413_eraseFn = ((_2410_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2409_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2413_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2409_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2405_isDatatype) || (_2406_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2409_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2407_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2406_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2409_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2407_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2412_recIdents;
          }
        } else if (_source74.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2414___mcc_h140 = _source74.dtor_values;
          DAST._IType _2415___mcc_h141 = _source74.dtor_retType;
          DAST._IExpression _2416___mcc_h142 = _source74.dtor_expr;
          bool _2417_isDatatype = _2156___mcc_h37;
          bool _2418_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2419_field = _2154___mcc_h35;
          DAST._IExpression _2420_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2421_onString;
            bool _2422_onOwned;
            bool _2423_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2424_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1511;
            bool _out1512;
            bool _out1513;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1514;
            DCOMP.COMP.GenExpr(_2420_on, selfIdent, @params, false, out _out1511, out _out1512, out _out1513, out _out1514);
            _2421_onString = _out1511;
            _2422_onOwned = _out1512;
            _2423_onErased = _out1513;
            _2424_recIdents = _out1514;
            if (!(_2423_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2425_eraseFn;
              _2425_eraseFn = ((_2422_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2421_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2425_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2421_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2417_isDatatype) || (_2418_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2421_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2419_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2418_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2421_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2419_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2424_recIdents;
          }
        } else if (_source74.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2426___mcc_h146 = _source74.dtor_name;
          DAST._IType _2427___mcc_h147 = _source74.dtor_typ;
          DAST._IExpression _2428___mcc_h148 = _source74.dtor_value;
          DAST._IExpression _2429___mcc_h149 = _source74.dtor_iifeBody;
          bool _2430_isDatatype = _2156___mcc_h37;
          bool _2431_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2432_field = _2154___mcc_h35;
          DAST._IExpression _2433_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2434_onString;
            bool _2435_onOwned;
            bool _2436_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2437_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1515;
            bool _out1516;
            bool _out1517;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
            DCOMP.COMP.GenExpr(_2433_on, selfIdent, @params, false, out _out1515, out _out1516, out _out1517, out _out1518);
            _2434_onString = _out1515;
            _2435_onOwned = _out1516;
            _2436_onErased = _out1517;
            _2437_recIdents = _out1518;
            if (!(_2436_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2438_eraseFn;
              _2438_eraseFn = ((_2435_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2434_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2438_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2434_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2430_isDatatype) || (_2431_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2434_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2432_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2431_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2434_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2432_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2437_recIdents;
          }
        } else if (_source74.is_Apply) {
          DAST._IExpression _2439___mcc_h154 = _source74.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2440___mcc_h155 = _source74.dtor_args;
          bool _2441_isDatatype = _2156___mcc_h37;
          bool _2442_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2443_field = _2154___mcc_h35;
          DAST._IExpression _2444_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2445_onString;
            bool _2446_onOwned;
            bool _2447_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2448_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1519;
            bool _out1520;
            bool _out1521;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1522;
            DCOMP.COMP.GenExpr(_2444_on, selfIdent, @params, false, out _out1519, out _out1520, out _out1521, out _out1522);
            _2445_onString = _out1519;
            _2446_onOwned = _out1520;
            _2447_onErased = _out1521;
            _2448_recIdents = _out1522;
            if (!(_2447_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2449_eraseFn;
              _2449_eraseFn = ((_2446_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2445_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2449_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2445_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2441_isDatatype) || (_2442_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2445_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2443_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2442_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2445_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2443_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2448_recIdents;
          }
        } else if (_source74.is_TypeTest) {
          DAST._IExpression _2450___mcc_h158 = _source74.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2451___mcc_h159 = _source74.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2452___mcc_h160 = _source74.dtor_variant;
          bool _2453_isDatatype = _2156___mcc_h37;
          bool _2454_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2455_field = _2154___mcc_h35;
          DAST._IExpression _2456_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2457_onString;
            bool _2458_onOwned;
            bool _2459_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2460_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1523;
            bool _out1524;
            bool _out1525;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1526;
            DCOMP.COMP.GenExpr(_2456_on, selfIdent, @params, false, out _out1523, out _out1524, out _out1525, out _out1526);
            _2457_onString = _out1523;
            _2458_onOwned = _out1524;
            _2459_onErased = _out1525;
            _2460_recIdents = _out1526;
            if (!(_2459_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2461_eraseFn;
              _2461_eraseFn = ((_2458_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2457_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2461_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2457_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2453_isDatatype) || (_2454_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2457_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2455_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2454_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2457_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2455_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2460_recIdents;
          }
        } else {
          DAST._IType _2462___mcc_h164 = _source74.dtor_typ;
          bool _2463_isDatatype = _2156___mcc_h37;
          bool _2464_isConstant = _2155___mcc_h36;
          Dafny.ISequence<Dafny.Rune> _2465_field = _2154___mcc_h35;
          DAST._IExpression _2466_on = _2153___mcc_h34;
          {
            Dafny.ISequence<Dafny.Rune> _2467_onString;
            bool _2468_onOwned;
            bool _2469_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2470_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1527;
            bool _out1528;
            bool _out1529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1530;
            DCOMP.COMP.GenExpr(_2466_on, selfIdent, @params, false, out _out1527, out _out1528, out _out1529, out _out1530);
            _2467_onString = _out1527;
            _2468_onOwned = _out1528;
            _2469_onErased = _out1529;
            _2470_recIdents = _out1530;
            if (!(_2469_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2471_eraseFn;
              _2471_eraseFn = ((_2468_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2467_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2471_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2467_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2463_isDatatype) || (_2464_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2467_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2465_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2464_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2467_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2465_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2470_recIdents;
          }
        }
      } else if (_source22.is_SelectFn) {
        DAST._IExpression _2472___mcc_h166 = _source22.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2473___mcc_h167 = _source22.dtor_field;
        bool _2474___mcc_h168 = _source22.dtor_onDatatype;
        bool _2475___mcc_h169 = _source22.dtor_isStatic;
        BigInteger _2476___mcc_h170 = _source22.dtor_arity;
        BigInteger _2477_arity = _2476___mcc_h170;
        bool _2478_isStatic = _2475___mcc_h169;
        bool _2479_isDatatype = _2474___mcc_h168;
        Dafny.ISequence<Dafny.Rune> _2480_field = _2473___mcc_h167;
        DAST._IExpression _2481_on = _2472___mcc_h166;
        {
          Dafny.ISequence<Dafny.Rune> _2482_onString;
          bool _2483_onOwned;
          bool _2484___v80;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2485_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1531;
          bool _out1532;
          bool _out1533;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1534;
          DCOMP.COMP.GenExpr(_2481_on, selfIdent, @params, false, out _out1531, out _out1532, out _out1533, out _out1534);
          _2482_onString = _out1531;
          _2483_onOwned = _out1532;
          _2484___v80 = _out1533;
          _2485_recIdents = _out1534;
          if (_2478_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2482_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2480_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2482_onString), ((_2483_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _2486_args;
            _2486_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _2487_i;
            _2487_i = BigInteger.Zero;
            while ((_2487_i) < (_2477_arity)) {
              if ((_2487_i).Sign == 1) {
                _2486_args = Dafny.Sequence<Dafny.Rune>.Concat(_2486_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2486_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2486_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_2487_i));
              _2487_i = (_2487_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2486_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _2480_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2486_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper(::std::rc::Rc::new("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
          readIdents = _2485_recIdents;
        }
      } else if (_source22.is_Index) {
        DAST._IExpression _2488___mcc_h171 = _source22.dtor_expr;
        DAST._ICollKind _2489___mcc_h172 = _source22.dtor_collKind;
        Dafny.ISequence<DAST._IExpression> _2490___mcc_h173 = _source22.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2491_indices = _2490___mcc_h173;
        DAST._ICollKind _2492_collKind = _2489___mcc_h172;
        DAST._IExpression _2493_on = _2488___mcc_h171;
        {
          Dafny.ISequence<Dafny.Rune> _2494_onString;
          bool _2495_onOwned;
          bool _2496_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2497_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1535;
          bool _out1536;
          bool _out1537;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1538;
          DCOMP.COMP.GenExpr(_2493_on, selfIdent, @params, false, out _out1535, out _out1536, out _out1537, out _out1538);
          _2494_onString = _out1535;
          _2495_onOwned = _out1536;
          _2496_onErased = _out1537;
          _2497_recIdents = _out1538;
          readIdents = _2497_recIdents;
          if (!(_2496_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2498_eraseFn;
            _2498_eraseFn = ((_2495_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2494_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2498_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2494_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2494_onString;
          BigInteger _2499_i;
          _2499_i = BigInteger.Zero;
          while ((_2499_i) < (new BigInteger((_2491_indices).Count))) {
            if (object.Equals(_2492_collKind, DAST.CollKind.create_Array())) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
            }
            if (object.Equals(_2492_collKind, DAST.CollKind.create_Map())) {
              Dafny.ISequence<Dafny.Rune> _2500_idx;
              bool _2501_idxOwned;
              bool _2502_idxErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2503_recIdentsIdx;
              Dafny.ISequence<Dafny.Rune> _out1539;
              bool _out1540;
              bool _out1541;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1542;
              DCOMP.COMP.GenExpr((_2491_indices).Select(_2499_i), selfIdent, @params, false, out _out1539, out _out1540, out _out1541, out _out1542);
              _2500_idx = _out1539;
              _2501_idxOwned = _out1540;
              _2502_idxErased = _out1541;
              _2503_recIdentsIdx = _out1542;
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")[")), ((_2501_idxOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _2500_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2503_recIdentsIdx);
            } else {
              Dafny.ISequence<Dafny.Rune> _2504_idx;
              bool _2505___v81;
              bool _2506_idxErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2507_recIdentsIdx;
              Dafny.ISequence<Dafny.Rune> _out1543;
              bool _out1544;
              bool _out1545;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1546;
              DCOMP.COMP.GenExpr((_2491_indices).Select(_2499_i), selfIdent, @params, true, out _out1543, out _out1544, out _out1545, out _out1546);
              _2504_idx = _out1543;
              _2505___v81 = _out1544;
              _2506_idxErased = _out1545;
              _2507_recIdentsIdx = _out1546;
              if (!(_2506_idxErased)) {
                _2504_idx = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2504_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")[<usize as ::dafny_runtime::NumCast>::from(")), _2504_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2507_recIdentsIdx);
            }
            _2499_i = (_2499_i) + (BigInteger.One);
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = false;
          }
          isErased = _2496_onErased;
        }
      } else if (_source22.is_IndexRange) {
        DAST._IExpression _2508___mcc_h174 = _source22.dtor_expr;
        bool _2509___mcc_h175 = _source22.dtor_isArray;
        DAST._IOptional<DAST._IExpression> _2510___mcc_h176 = _source22.dtor_low;
        DAST._IOptional<DAST._IExpression> _2511___mcc_h177 = _source22.dtor_high;
        DAST._IOptional<DAST._IExpression> _2512_high = _2511___mcc_h177;
        DAST._IOptional<DAST._IExpression> _2513_low = _2510___mcc_h176;
        bool _2514_isArray = _2509___mcc_h175;
        DAST._IExpression _2515_on = _2508___mcc_h174;
        {
          Dafny.ISequence<Dafny.Rune> _2516_onString;
          bool _2517_onOwned;
          bool _2518_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2519_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1547;
          bool _out1548;
          bool _out1549;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1550;
          DCOMP.COMP.GenExpr(_2515_on, selfIdent, @params, false, out _out1547, out _out1548, out _out1549, out _out1550);
          _2516_onString = _out1547;
          _2517_onOwned = _out1548;
          _2518_onErased = _out1549;
          _2519_recIdents = _out1550;
          readIdents = _2519_recIdents;
          if (!(_2518_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2520_eraseFn;
            _2520_eraseFn = ((_2517_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2516_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2520_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2516_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2516_onString;
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2521_lowString;
          _2521_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source75 = _2513_low;
          if (_source75.is_Some) {
            DAST._IExpression _2522___mcc_h1067 = _source75.dtor_Some_a0;
            DAST._IExpression _2523_l = _2522___mcc_h1067;
            {
              Dafny.ISequence<Dafny.Rune> _2524_lString;
              bool _2525___v82;
              bool _2526_lErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2527_recIdentsL;
              Dafny.ISequence<Dafny.Rune> _out1551;
              bool _out1552;
              bool _out1553;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1554;
              DCOMP.COMP.GenExpr(_2523_l, selfIdent, @params, true, out _out1551, out _out1552, out _out1553, out _out1554);
              _2524_lString = _out1551;
              _2525___v82 = _out1552;
              _2526_lErased = _out1553;
              _2527_recIdentsL = _out1554;
              if (!(_2526_lErased)) {
                _2524_lString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2524_lString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2521_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2524_lString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2527_recIdentsL);
            }
          } else {
          }
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2528_highString;
          _2528_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source76 = _2512_high;
          if (_source76.is_Some) {
            DAST._IExpression _2529___mcc_h1068 = _source76.dtor_Some_a0;
            DAST._IExpression _2530_h = _2529___mcc_h1068;
            {
              Dafny.ISequence<Dafny.Rune> _2531_hString;
              bool _2532___v83;
              bool _2533_hErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2534_recIdentsH;
              Dafny.ISequence<Dafny.Rune> _out1555;
              bool _out1556;
              bool _out1557;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1558;
              DCOMP.COMP.GenExpr(_2530_h, selfIdent, @params, true, out _out1555, out _out1556, out _out1557, out _out1558);
              _2531_hString = _out1555;
              _2532___v83 = _out1556;
              _2533_hErased = _out1557;
              _2534_recIdentsH = _out1558;
              if (!(_2533_hErased)) {
                _2531_hString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2531_hString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2528_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2531_hString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2534_recIdentsH);
            }
          } else {
          }
          if (_2514_isArray) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source77) => {
            if (_source77.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2535___mcc_h1069 = _source77.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2535___mcc_h1069, _pat_let0_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let0_0, _2536_l => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2536_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2521_lowString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source78) => {
            if (_source78.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2537___mcc_h1070 = _source78.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2537___mcc_h1070, _pat_let1_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let1_0, _2538_h => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2538_h), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2528_highString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isErased = _2518_onErased;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".to_vec())"));
          isOwned = true;
        }
      } else if (_source22.is_TupleSelect) {
        DAST._IExpression _2539___mcc_h178 = _source22.dtor_expr;
        BigInteger _2540___mcc_h179 = _source22.dtor_index;
        BigInteger _2541_idx = _2540___mcc_h179;
        DAST._IExpression _2542_on = _2539___mcc_h178;
        {
          Dafny.ISequence<Dafny.Rune> _2543_onString;
          bool _2544___v84;
          bool _2545_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2546_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1559;
          bool _out1560;
          bool _out1561;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1562;
          DCOMP.COMP.GenExpr(_2542_on, selfIdent, @params, false, out _out1559, out _out1560, out _out1561, out _out1562);
          _2543_onString = _out1559;
          _2544___v84 = _out1560;
          _2545_tupErased = _out1561;
          _2546_recIdents = _out1562;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2543_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_2541_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _2545_tupErased;
          readIdents = _2546_recIdents;
        }
      } else if (_source22.is_Call) {
        DAST._IExpression _2547___mcc_h180 = _source22.dtor_on;
        Dafny.ISequence<Dafny.Rune> _2548___mcc_h181 = _source22.dtor_name;
        Dafny.ISequence<DAST._IType> _2549___mcc_h182 = _source22.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2550___mcc_h183 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2551_args = _2550___mcc_h183;
        Dafny.ISequence<DAST._IType> _2552_typeArgs = _2549___mcc_h182;
        Dafny.ISequence<Dafny.Rune> _2553_name = _2548___mcc_h181;
        DAST._IExpression _2554_on = _2547___mcc_h180;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2555_typeArgString;
          _2555_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2552_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2556_typeI;
            _2556_typeI = BigInteger.Zero;
            _2555_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_2556_typeI) < (new BigInteger((_2552_typeArgs).Count))) {
              if ((_2556_typeI).Sign == 1) {
                _2555_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2555_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _2557_typeString;
              Dafny.ISequence<Dafny.Rune> _out1563;
              _out1563 = DCOMP.COMP.GenType((_2552_typeArgs).Select(_2556_typeI), false, false);
              _2557_typeString = _out1563;
              _2555_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2555_typeArgString, _2557_typeString);
              _2556_typeI = (_2556_typeI) + (BigInteger.One);
            }
            _2555_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2555_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _2558_argString;
          _2558_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2559_i;
          _2559_i = BigInteger.Zero;
          while ((_2559_i) < (new BigInteger((_2551_args).Count))) {
            if ((_2559_i).Sign == 1) {
              _2558_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2558_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2560_argExpr;
            bool _2561_isOwned;
            bool _2562_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2563_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1564;
            bool _out1565;
            bool _out1566;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1567;
            DCOMP.COMP.GenExpr((_2551_args).Select(_2559_i), selfIdent, @params, false, out _out1564, out _out1565, out _out1566, out _out1567);
            _2560_argExpr = _out1564;
            _2561_isOwned = _out1565;
            _2562_argErased = _out1566;
            _2563_argIdents = _out1567;
            if (_2561_isOwned) {
              _2560_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2560_argExpr);
            }
            _2558_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2558_argString, _2560_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2563_argIdents);
            _2559_i = (_2559_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2564_enclosingString;
          bool _2565___v85;
          bool _2566___v86;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2567_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1568;
          bool _out1569;
          bool _out1570;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1571;
          DCOMP.COMP.GenExpr(_2554_on, selfIdent, @params, false, out _out1568, out _out1569, out _out1570, out _out1571);
          _2564_enclosingString = _out1568;
          _2565___v85 = _out1569;
          _2566___v86 = _out1570;
          _2567_recIdents = _out1571;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2567_recIdents);
          DAST._IExpression _source79 = _2554_on;
          if (_source79.is_Literal) {
            DAST._ILiteral _2568___mcc_h1071 = _source79.dtor_Literal_a0;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2569___mcc_h1073 = _source79.dtor_Ident_a0;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2570___mcc_h1075 = _source79.dtor_Companion_a0;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2564_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (_2553_name));
            }
          } else if (_source79.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2571___mcc_h1077 = _source79.dtor_Tuple_a0;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2572___mcc_h1079 = _source79.dtor_path;
            Dafny.ISequence<DAST._IExpression> _2573___mcc_h1080 = _source79.dtor_args;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2574___mcc_h1083 = _source79.dtor_dims;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2575___mcc_h1085 = _source79.dtor_path;
            Dafny.ISequence<Dafny.Rune> _2576___mcc_h1086 = _source79.dtor_variant;
            bool _2577___mcc_h1087 = _source79.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2578___mcc_h1088 = _source79.dtor_contents;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Convert) {
            DAST._IExpression _2579___mcc_h1093 = _source79.dtor_value;
            DAST._IType _2580___mcc_h1094 = _source79.dtor_from;
            DAST._IType _2581___mcc_h1095 = _source79.dtor_typ;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2582___mcc_h1099 = _source79.dtor_elements;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2583___mcc_h1101 = _source79.dtor_elements;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_MapValue) {
            Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2584___mcc_h1103 = _source79.dtor_mapElems;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_This) {
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Ite) {
            DAST._IExpression _2585___mcc_h1105 = _source79.dtor_cond;
            DAST._IExpression _2586___mcc_h1106 = _source79.dtor_thn;
            DAST._IExpression _2587___mcc_h1107 = _source79.dtor_els;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_UnOp) {
            DAST._IUnaryOp _2588___mcc_h1111 = _source79.dtor_unOp;
            DAST._IExpression _2589___mcc_h1112 = _source79.dtor_expr;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _2590___mcc_h1115 = _source79.dtor_op;
            DAST._IExpression _2591___mcc_h1116 = _source79.dtor_left;
            DAST._IExpression _2592___mcc_h1117 = _source79.dtor_right;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_ArrayLen) {
            DAST._IExpression _2593___mcc_h1121 = _source79.dtor_expr;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Select) {
            DAST._IExpression _2594___mcc_h1123 = _source79.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2595___mcc_h1124 = _source79.dtor_field;
            bool _2596___mcc_h1125 = _source79.dtor_isConstant;
            bool _2597___mcc_h1126 = _source79.dtor_onDatatype;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_SelectFn) {
            DAST._IExpression _2598___mcc_h1131 = _source79.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2599___mcc_h1132 = _source79.dtor_field;
            bool _2600___mcc_h1133 = _source79.dtor_onDatatype;
            bool _2601___mcc_h1134 = _source79.dtor_isStatic;
            BigInteger _2602___mcc_h1135 = _source79.dtor_arity;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Index) {
            DAST._IExpression _2603___mcc_h1141 = _source79.dtor_expr;
            DAST._ICollKind _2604___mcc_h1142 = _source79.dtor_collKind;
            Dafny.ISequence<DAST._IExpression> _2605___mcc_h1143 = _source79.dtor_indices;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_IndexRange) {
            DAST._IExpression _2606___mcc_h1147 = _source79.dtor_expr;
            bool _2607___mcc_h1148 = _source79.dtor_isArray;
            DAST._IOptional<DAST._IExpression> _2608___mcc_h1149 = _source79.dtor_low;
            DAST._IOptional<DAST._IExpression> _2609___mcc_h1150 = _source79.dtor_high;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_TupleSelect) {
            DAST._IExpression _2610___mcc_h1155 = _source79.dtor_expr;
            BigInteger _2611___mcc_h1156 = _source79.dtor_index;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Call) {
            DAST._IExpression _2612___mcc_h1159 = _source79.dtor_on;
            Dafny.ISequence<Dafny.Rune> _2613___mcc_h1160 = _source79.dtor_name;
            Dafny.ISequence<DAST._IType> _2614___mcc_h1161 = _source79.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2615___mcc_h1162 = _source79.dtor_args;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2616___mcc_h1167 = _source79.dtor_params;
            DAST._IType _2617___mcc_h1168 = _source79.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2618___mcc_h1169 = _source79.dtor_body;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_BetaRedex) {
            Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2619___mcc_h1173 = _source79.dtor_values;
            DAST._IType _2620___mcc_h1174 = _source79.dtor_retType;
            DAST._IExpression _2621___mcc_h1175 = _source79.dtor_expr;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2622___mcc_h1179 = _source79.dtor_name;
            DAST._IType _2623___mcc_h1180 = _source79.dtor_typ;
            DAST._IExpression _2624___mcc_h1181 = _source79.dtor_value;
            DAST._IExpression _2625___mcc_h1182 = _source79.dtor_iifeBody;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_Apply) {
            DAST._IExpression _2626___mcc_h1187 = _source79.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2627___mcc_h1188 = _source79.dtor_args;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else if (_source79.is_TypeTest) {
            DAST._IExpression _2628___mcc_h1191 = _source79.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2629___mcc_h1192 = _source79.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2630___mcc_h1193 = _source79.dtor_variant;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          } else {
            DAST._IType _2631___mcc_h1197 = _source79.dtor_typ;
            {
              _2564_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2564_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2553_name));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2564_enclosingString, _2555_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2558_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2632___mcc_h184 = _source22.dtor_params;
        DAST._IType _2633___mcc_h185 = _source22.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2634___mcc_h186 = _source22.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2635_body = _2634___mcc_h186;
        DAST._IType _2636_retType = _2633___mcc_h185;
        Dafny.ISequence<DAST._IFormal> _2637_params = _2632___mcc_h184;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2638_paramNames;
          _2638_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2639_i;
          _2639_i = BigInteger.Zero;
          while ((_2639_i) < (new BigInteger((_2637_params).Count))) {
            _2638_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2638_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2637_params).Select(_2639_i)).dtor_name));
            _2639_i = (_2639_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2640_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2641_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1572;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1573;
          DCOMP.COMP.GenStmts(_2635_body, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), _2638_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1572, out _out1573);
          _2640_recursiveGen = _out1572;
          _2641_recIdents = _out1573;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2642_allReadCloned;
          _2642_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2641_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2643_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2641_recIdents).Elements) {
              _2643_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2641_recIdents).Contains(_2643_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1798)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2638_paramNames).Contains(_2643_next))) {
              _2642_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2642_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2643_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2643_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2643_next));
            }
            _2641_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2641_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2643_next));
          }
          Dafny.ISequence<Dafny.Rune> _2644_paramsString;
          _2644_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          Dafny.ISequence<Dafny.Rune> _2645_paramTypes;
          _2645_paramTypes = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2639_i = BigInteger.Zero;
          while ((_2639_i) < (new BigInteger((_2637_params).Count))) {
            if ((_2639_i).Sign == 1) {
              _2644_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2644_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              _2645_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(_2645_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2646_typStr;
            Dafny.ISequence<Dafny.Rune> _out1574;
            _out1574 = DCOMP.COMP.GenType(((_2637_params).Select(_2639_i)).dtor_typ, false, true);
            _2646_typStr = _out1574;
            _2644_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2644_paramsString, ((_2637_params).Select(_2639_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2646_typStr);
            _2645_paramTypes = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2645_paramTypes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), _2646_typStr);
            _2639_i = (_2639_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2647_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1575;
          _out1575 = DCOMP.COMP.GenType(_2636_retType, false, true);
          _2647_retTypeGen = _out1575;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn Fn("), _2645_paramTypes), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), _2647_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>({\n")), _2642_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(move |")), _2644_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2647_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2640_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_BetaRedex) {
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2648___mcc_h187 = _source22.dtor_values;
        DAST._IType _2649___mcc_h188 = _source22.dtor_retType;
        DAST._IExpression _2650___mcc_h189 = _source22.dtor_expr;
        DAST._IExpression _2651_expr = _2650___mcc_h189;
        DAST._IType _2652_retType = _2649___mcc_h188;
        Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2653_values = _2648___mcc_h187;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2654_paramNames;
          _2654_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2655_paramNamesSet;
          _2655_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2656_i;
          _2656_i = BigInteger.Zero;
          while ((_2656_i) < (new BigInteger((_2653_values).Count))) {
            _2654_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2654_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((((_2653_values).Select(_2656_i)).dtor__0).dtor_name));
            _2655_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2655_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((((_2653_values).Select(_2656_i)).dtor__0).dtor_name));
            _2656_i = (_2656_i) + (BigInteger.One);
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
          Dafny.ISequence<Dafny.Rune> _2657_paramsString;
          _2657_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2656_i = BigInteger.Zero;
          while ((_2656_i) < (new BigInteger((_2653_values).Count))) {
            if ((_2656_i).Sign == 1) {
              _2657_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2657_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2658_typStr;
            Dafny.ISequence<Dafny.Rune> _out1576;
            _out1576 = DCOMP.COMP.GenType((((_2653_values).Select(_2656_i)).dtor__0).dtor_typ, false, true);
            _2658_typStr = _out1576;
            Dafny.ISequence<Dafny.Rune> _2659_valueGen;
            bool _2660___v89;
            bool _2661_valueErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2662_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1577;
            bool _out1578;
            bool _out1579;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1580;
            DCOMP.COMP.GenExpr(((_2653_values).Select(_2656_i)).dtor__1, selfIdent, @params, true, out _out1577, out _out1578, out _out1579, out _out1580);
            _2659_valueGen = _out1577;
            _2660___v89 = _out1578;
            _2661_valueErased = _out1579;
            _2662_recIdents = _out1580;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), (((_2653_values).Select(_2656_i)).dtor__0).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), _2658_typStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2662_recIdents);
            if (_2661_valueErased) {
              _2659_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2659_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _2659_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            _2656_i = (_2656_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2663_recGen;
          bool _2664_recOwned;
          bool _2665_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2666_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1581;
          bool _out1582;
          bool _out1583;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1584;
          DCOMP.COMP.GenExpr(_2651_expr, selfIdent, _2654_paramNames, mustOwn, out _out1581, out _out1582, out _out1583, out _out1584);
          _2663_recGen = _out1581;
          _2664_recOwned = _out1582;
          _2665_recErased = _out1583;
          _2666_recIdents = _out1584;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2666_recIdents, _2655_paramNamesSet);
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _2663_recGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2664_recOwned;
          isErased = _2665_recErased;
        }
      } else if (_source22.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2667___mcc_h190 = _source22.dtor_name;
        DAST._IType _2668___mcc_h191 = _source22.dtor_typ;
        DAST._IExpression _2669___mcc_h192 = _source22.dtor_value;
        DAST._IExpression _2670___mcc_h193 = _source22.dtor_iifeBody;
        DAST._IExpression _2671_iifeBody = _2670___mcc_h193;
        DAST._IExpression _2672_value = _2669___mcc_h192;
        DAST._IType _2673_tpe = _2668___mcc_h191;
        Dafny.ISequence<Dafny.Rune> _2674_name = _2667___mcc_h190;
        {
          Dafny.ISequence<Dafny.Rune> _2675_valueGen;
          bool _2676_valueOwned;
          bool _2677_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2678_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1585;
          bool _out1586;
          bool _out1587;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1588;
          DCOMP.COMP.GenExpr(_2672_value, selfIdent, @params, false, out _out1585, out _out1586, out _out1587, out _out1588);
          _2675_valueGen = _out1585;
          _2676_valueOwned = _out1586;
          _2677_valueErased = _out1587;
          _2678_recIdents = _out1588;
          if (_2677_valueErased) {
            Dafny.ISequence<Dafny.Rune> _2679_eraseFn;
            _2679_eraseFn = ((_2676_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
            _2675_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::"), _2679_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2675_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2678_recIdents;
          Dafny.ISequence<Dafny.Rune> _2680_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1589;
          _out1589 = DCOMP.COMP.GenType(_2673_tpe, false, true);
          _2680_valueTypeGen = _out1589;
          Dafny.ISequence<Dafny.Rune> _2681_bodyGen;
          bool _2682_bodyOwned;
          bool _2683_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2684_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1590;
          bool _out1591;
          bool _out1592;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1593;
          DCOMP.COMP.GenExpr(_2671_iifeBody, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, ((_2676_valueOwned) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2674_name))))), mustOwn, out _out1590, out _out1591, out _out1592, out _out1593);
          _2681_bodyGen = _out1590;
          _2682_bodyOwned = _out1591;
          _2683_bodyErased = _out1592;
          _2684_bodyIdents = _out1593;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2684_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2674_name))));
          Dafny.ISequence<Dafny.Rune> _2685_eraseFn;
          _2685_eraseFn = ((_2676_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2674_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((_2676_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")))), _2680_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2675_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2681_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2682_bodyOwned;
          isErased = _2683_bodyErased;
        }
      } else if (_source22.is_Apply) {
        DAST._IExpression _2686___mcc_h194 = _source22.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2687___mcc_h195 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2688_args = _2687___mcc_h195;
        DAST._IExpression _2689_func = _2686___mcc_h194;
        {
          Dafny.ISequence<Dafny.Rune> _2690_funcString;
          bool _2691___v90;
          bool _2692_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2693_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1594;
          bool _out1595;
          bool _out1596;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1597;
          DCOMP.COMP.GenExpr(_2689_func, selfIdent, @params, false, out _out1594, out _out1595, out _out1596, out _out1597);
          _2690_funcString = _out1594;
          _2691___v90 = _out1595;
          _2692_funcErased = _out1596;
          _2693_recIdents = _out1597;
          readIdents = _2693_recIdents;
          Dafny.ISequence<Dafny.Rune> _2694_argString;
          _2694_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2695_i;
          _2695_i = BigInteger.Zero;
          while ((_2695_i) < (new BigInteger((_2688_args).Count))) {
            if ((_2695_i).Sign == 1) {
              _2694_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2694_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2696_argExpr;
            bool _2697_isOwned;
            bool _2698_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2699_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1598;
            bool _out1599;
            bool _out1600;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1601;
            DCOMP.COMP.GenExpr((_2688_args).Select(_2695_i), selfIdent, @params, false, out _out1598, out _out1599, out _out1600, out _out1601);
            _2696_argExpr = _out1598;
            _2697_isOwned = _out1599;
            _2698_argErased = _out1600;
            _2699_argIdents = _out1601;
            if (_2697_isOwned) {
              _2696_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2696_argExpr);
            }
            _2694_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2694_argString, _2696_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2699_argIdents);
            _2695_i = (_2695_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2690_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2694_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_TypeTest) {
        DAST._IExpression _2700___mcc_h196 = _source22.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2701___mcc_h197 = _source22.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2702___mcc_h198 = _source22.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2703_variant = _2702___mcc_h198;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2704_dType = _2701___mcc_h197;
        DAST._IExpression _2705_on = _2700___mcc_h196;
        {
          Dafny.ISequence<Dafny.Rune> _2706_exprGen;
          bool _2707___v91;
          bool _2708_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2709_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1602;
          bool _out1603;
          bool _out1604;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1605;
          DCOMP.COMP.GenExpr(_2705_on, selfIdent, @params, false, out _out1602, out _out1603, out _out1604, out _out1605);
          _2706_exprGen = _out1602;
          _2707___v91 = _out1603;
          _2708_exprErased = _out1604;
          _2709_recIdents = _out1605;
          Dafny.ISequence<Dafny.Rune> _2710_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1606;
          _out1606 = DCOMP.COMP.GenPath(_2704_dType);
          _2710_dTypePath = _out1606;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2706_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2710_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2703_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2709_recIdents;
        }
      } else {
        DAST._IType _2711___mcc_h199 = _source22.dtor_typ;
        DAST._IType _2712_typ = _2711___mcc_h199;
        {
          Dafny.ISequence<Dafny.Rune> _2713_typString;
          Dafny.ISequence<Dafny.Rune> _out1607;
          _out1607 = DCOMP.COMP.GenType(_2712_typ, false, false);
          _2713_typString = _out1607;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2713_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
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
      BigInteger _2714_i;
      _2714_i = BigInteger.Zero;
      while ((_2714_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2715_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1608;
        _out1608 = DCOMP.COMP.GenModule((p).Select(_2714_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2715_generated = _out1608;
        if ((_2714_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2715_generated);
        _2714_i = (_2714_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2716_i;
      _2716_i = BigInteger.Zero;
      while ((_2716_i) < (new BigInteger((fullName).Count))) {
        if ((_2716_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2716_i));
        _2716_i = (_2716_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

