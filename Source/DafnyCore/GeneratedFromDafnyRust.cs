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
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _276___mcc_h9 = _source15.dtor_lbl;
        DAST._IExpression _277___mcc_h10 = _source15.dtor_cond;
        Dafny.ISequence<DAST._IStatement> _278___mcc_h11 = _source15.dtor_body;
        Dafny.ISequence<DAST._IStatement> _279_body = _278___mcc_h11;
        DAST._IExpression _280_cond = _277___mcc_h10;
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _281_lbl = _276___mcc_h9;
        {
          Dafny.ISequence<Dafny.Rune> _282_condString;
          bool _283___v17;
          bool _284_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _285_recIdents;
          Dafny.ISequence<Dafny.Rune> _out97;
          bool _out98;
          bool _out99;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out100;
          DCOMP.COMP.GenExpr(_280_cond, selfIdent, @params, true, out _out97, out _out98, out _out99, out _out100);
          _282_condString = _out97;
          _283___v17 = _out98;
          _284_condErased = _out99;
          _285_recIdents = _out100;
          if (!(_284_condErased)) {
            _282_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase("), _282_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _285_recIdents;
          Dafny.ISequence<Dafny.Rune> _286_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _287_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out101;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out102;
          DCOMP.COMP.GenStmts(_279_body, selfIdent, @params, false, earlyReturn, out _out101, out _out102);
          _286_bodyString = _out101;
          _287_bodyIdents = _out102;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _287_bodyIdents);
          Dafny.ISequence<Dafny.Rune> _288_lblString;
          _288_lblString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source17 = _281_lbl;
          if (_source17.is_Some) {
            Dafny.ISequence<Dafny.Rune> _289___mcc_h21 = _source17.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _290_id = _289___mcc_h21;
            {
              _288_lblString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'label_"), _290_id), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "));
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_288_lblString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while ")), _282_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _286_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
        }
      } else if (_source15.is_Call) {
        DAST._IExpression _291___mcc_h12 = _source15.dtor_on;
        Dafny.ISequence<Dafny.Rune> _292___mcc_h13 = _source15.dtor_name;
        Dafny.ISequence<DAST._IType> _293___mcc_h14 = _source15.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _294___mcc_h15 = _source15.dtor_args;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _295___mcc_h16 = _source15.dtor_outs;
        DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _296_maybeOutVars = _295___mcc_h16;
        Dafny.ISequence<DAST._IExpression> _297_args = _294___mcc_h15;
        Dafny.ISequence<DAST._IType> _298_typeArgs = _293___mcc_h14;
        Dafny.ISequence<Dafny.Rune> _299_name = _292___mcc_h13;
        DAST._IExpression _300_on = _291___mcc_h12;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _301_typeArgString;
          _301_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_298_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _302_typeI;
            _302_typeI = BigInteger.Zero;
            _301_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_302_typeI) < (new BigInteger((_298_typeArgs).Count))) {
              if ((_302_typeI).Sign == 1) {
                _301_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_301_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _303_typeString;
              Dafny.ISequence<Dafny.Rune> _out103;
              _out103 = DCOMP.COMP.GenType((_298_typeArgs).Select(_302_typeI), false, false);
              _303_typeString = _out103;
              _301_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_301_typeArgString, _303_typeString);
              _302_typeI = (_302_typeI) + (BigInteger.One);
            }
            _301_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_301_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _304_argString;
          _304_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _305_i;
          _305_i = BigInteger.Zero;
          while ((_305_i) < (new BigInteger((_297_args).Count))) {
            if ((_305_i).Sign == 1) {
              _304_argString = Dafny.Sequence<Dafny.Rune>.Concat(_304_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _306_argExpr;
            bool _307_isOwned;
            bool _308_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _309_argIdents;
            Dafny.ISequence<Dafny.Rune> _out104;
            bool _out105;
            bool _out106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
            DCOMP.COMP.GenExpr((_297_args).Select(_305_i), selfIdent, @params, false, out _out104, out _out105, out _out106, out _out107);
            _306_argExpr = _out104;
            _307_isOwned = _out105;
            _308_argErased = _out106;
            _309_argIdents = _out107;
            if (_307_isOwned) {
              _306_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _306_argExpr);
            }
            _304_argString = Dafny.Sequence<Dafny.Rune>.Concat(_304_argString, _306_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _309_argIdents);
            _305_i = (_305_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _310_enclosingString;
          bool _311___v18;
          bool _312___v19;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _313_enclosingIdents;
          Dafny.ISequence<Dafny.Rune> _out108;
          bool _out109;
          bool _out110;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
          DCOMP.COMP.GenExpr(_300_on, selfIdent, @params, false, out _out108, out _out109, out _out110, out _out111);
          _310_enclosingString = _out108;
          _311___v18 = _out109;
          _312___v19 = _out110;
          _313_enclosingIdents = _out111;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _313_enclosingIdents);
          DAST._IExpression _source18 = _300_on;
          if (_source18.is_Literal) {
            DAST._ILiteral _314___mcc_h22 = _source18.dtor_Literal_a0;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _315___mcc_h24 = _source18.dtor_Ident_a0;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _316___mcc_h26 = _source18.dtor_Companion_a0;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_310_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source18.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _317___mcc_h28 = _source18.dtor_Tuple_a0;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _318___mcc_h30 = _source18.dtor_path;
            Dafny.ISequence<DAST._IExpression> _319___mcc_h31 = _source18.dtor_args;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _320___mcc_h34 = _source18.dtor_dims;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _321___mcc_h36 = _source18.dtor_path;
            Dafny.ISequence<Dafny.Rune> _322___mcc_h37 = _source18.dtor_variant;
            bool _323___mcc_h38 = _source18.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _324___mcc_h39 = _source18.dtor_contents;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Convert) {
            DAST._IExpression _325___mcc_h44 = _source18.dtor_value;
            DAST._IType _326___mcc_h45 = _source18.dtor_from;
            DAST._IType _327___mcc_h46 = _source18.dtor_typ;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _328___mcc_h50 = _source18.dtor_elements;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _329___mcc_h52 = _source18.dtor_elements;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_This) {
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Ite) {
            DAST._IExpression _330___mcc_h54 = _source18.dtor_cond;
            DAST._IExpression _331___mcc_h55 = _source18.dtor_thn;
            DAST._IExpression _332___mcc_h56 = _source18.dtor_els;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_UnOp) {
            DAST._IUnaryOp _333___mcc_h60 = _source18.dtor_unOp;
            DAST._IExpression _334___mcc_h61 = _source18.dtor_expr;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _335___mcc_h64 = _source18.dtor_op;
            DAST._IExpression _336___mcc_h65 = _source18.dtor_left;
            DAST._IExpression _337___mcc_h66 = _source18.dtor_right;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_ArrayLen) {
            DAST._IExpression _338___mcc_h70 = _source18.dtor_expr;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Select) {
            DAST._IExpression _339___mcc_h72 = _source18.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _340___mcc_h73 = _source18.dtor_field;
            bool _341___mcc_h74 = _source18.dtor_isConstant;
            bool _342___mcc_h75 = _source18.dtor_onDatatype;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_SelectFn) {
            DAST._IExpression _343___mcc_h80 = _source18.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _344___mcc_h81 = _source18.dtor_field;
            bool _345___mcc_h82 = _source18.dtor_onDatatype;
            bool _346___mcc_h83 = _source18.dtor_isStatic;
            BigInteger _347___mcc_h84 = _source18.dtor_arity;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Index) {
            DAST._IExpression _348___mcc_h90 = _source18.dtor_expr;
            DAST._IExpression _349___mcc_h91 = _source18.dtor_idx;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_TupleSelect) {
            DAST._IExpression _350___mcc_h94 = _source18.dtor_expr;
            BigInteger _351___mcc_h95 = _source18.dtor_index;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Call) {
            DAST._IExpression _352___mcc_h98 = _source18.dtor_on;
            Dafny.ISequence<Dafny.Rune> _353___mcc_h99 = _source18.dtor_name;
            Dafny.ISequence<DAST._IType> _354___mcc_h100 = _source18.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _355___mcc_h101 = _source18.dtor_args;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _356___mcc_h106 = _source18.dtor_params;
            DAST._IType _357___mcc_h107 = _source18.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _358___mcc_h108 = _source18.dtor_body;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _359___mcc_h112 = _source18.dtor_name;
            DAST._IType _360___mcc_h113 = _source18.dtor_typ;
            DAST._IExpression _361___mcc_h114 = _source18.dtor_value;
            DAST._IExpression _362___mcc_h115 = _source18.dtor_iifeBody;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_Apply) {
            DAST._IExpression _363___mcc_h120 = _source18.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _364___mcc_h121 = _source18.dtor_args;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source18.is_TypeTest) {
            DAST._IExpression _365___mcc_h124 = _source18.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _366___mcc_h125 = _source18.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _367___mcc_h126 = _source18.dtor_variant;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _368___mcc_h130 = _source18.dtor_typ;
            {
              _310_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _369_receiver;
          _369_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source19 = _296_maybeOutVars;
          if (_source19.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _370___mcc_h132 = _source19.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _371_outVars = _370___mcc_h132;
            {
              if ((new BigInteger((_371_outVars).Count)) > (BigInteger.One)) {
                _369_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _372_outI;
              _372_outI = BigInteger.Zero;
              while ((_372_outI) < (new BigInteger((_371_outVars).Count))) {
                if ((_372_outI).Sign == 1) {
                  _369_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_369_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _373_outVar;
                _373_outVar = (_371_outVars).Select(_372_outI);
                _369_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_369_receiver, (_373_outVar));
                _372_outI = (_372_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_371_outVars).Count)) > (BigInteger.One)) {
                _369_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_369_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_369_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_369_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _310_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _299_name), _301_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _304_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source15.is_Return) {
        DAST._IExpression _374___mcc_h17 = _source15.dtor_expr;
        DAST._IExpression _375_expr = _374___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _376_exprString;
          bool _377___v22;
          bool _378_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _379_recIdents;
          Dafny.ISequence<Dafny.Rune> _out112;
          bool _out113;
          bool _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          DCOMP.COMP.GenExpr(_375_expr, selfIdent, @params, true, out _out112, out _out113, out _out114, out _out115);
          _376_exprString = _out112;
          _377___v22 = _out113;
          _378_recErased = _out114;
          _379_recIdents = _out115;
          _376_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _376_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _379_recIdents;
          if (isLast) {
            generated = _376_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _376_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source15.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source15.is_Break) {
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _380___mcc_h18 = _source15.dtor_toLabel;
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _381_toLabel = _380___mcc_h18;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source20 = _381_toLabel;
          if (_source20.is_Some) {
            Dafny.ISequence<Dafny.Rune> _382___mcc_h133 = _source20.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _383_lbl = _382___mcc_h133;
            {
              generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break 'label_"), _383_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          } else {
            {
              generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source15.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _384___mcc_h19 = _source15.dtor_body;
        Dafny.ISequence<DAST._IStatement> _385_body = _384___mcc_h19;
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if (!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#_this = self.clone();\n"));
          }
          BigInteger _386_paramI;
          _386_paramI = BigInteger.Zero;
          while ((_386_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _387_param;
            _387_param = (@params).Select(_386_paramI);
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#")), _387_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _387_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
            _386_paramI = (_386_paramI) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _388_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _389_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
          DCOMP.COMP.GenStmts(_385_body, ((!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out116, out _out117);
          _388_bodyString = _out116;
          _389_bodyIdents = _out117;
          readIdents = _389_bodyIdents;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'TAIL_CALL_START: loop {\n")), _388_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
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
        DAST._IExpression _390___mcc_h20 = _source15.dtor_Print_a0;
        DAST._IExpression _391_e = _390___mcc_h20;
        {
          Dafny.ISequence<Dafny.Rune> _392_printedExpr;
          bool _393_isOwned;
          bool _394___v23;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _395_recIdents;
          Dafny.ISequence<Dafny.Rune> _out118;
          bool _out119;
          bool _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          DCOMP.COMP.GenExpr(_391_e, selfIdent, @params, false, out _out118, out _out119, out _out120, out _out121);
          _392_printedExpr = _out118;
          _393_isOwned = _out119;
          _394___v23 = _out120;
          _395_recIdents = _out121;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_393_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _392_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _395_recIdents;
        }
      }
    }
    public static void GenExpr(DAST._IExpression e, DAST._IOptional<Dafny.ISequence<Dafny.Rune>> selfIdent, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> @params, bool mustOwn, out Dafny.ISequence<Dafny.Rune> s, out bool isOwned, out bool isErased, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents) {
      s = Dafny.Sequence<Dafny.Rune>.Empty;
      isOwned = false;
      isErased = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source21 = e;
      if (_source21.is_Literal) {
        DAST._ILiteral _396___mcc_h0 = _source21.dtor_Literal_a0;
        DAST._ILiteral _source22 = _396___mcc_h0;
        if (_source22.is_BoolLiteral) {
          bool _397___mcc_h1 = _source22.dtor_BoolLiteral_a0;
          if ((_397___mcc_h1) == (false)) {
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
        } else if (_source22.is_IntLiteral) {
          Dafny.ISequence<Dafny.Rune> _398___mcc_h2 = _source22.dtor_IntLiteral_a0;
          DAST._IType _399___mcc_h3 = _source22.dtor_IntLiteral_a1;
          DAST._IType _400_t = _399___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _401_i = _398___mcc_h2;
          {
            DAST._IType _source23 = _400_t;
            if (_source23.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _402___mcc_h173 = _source23.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _403___mcc_h174 = _source23.dtor_typeArgs;
              DAST._IResolvedType _404___mcc_h175 = _source23.dtor_resolved;
              {
                s = _401_i;
              }
            } else if (_source23.is_Nullable) {
              DAST._IType _405___mcc_h179 = _source23.dtor_Nullable_a0;
              {
                s = _401_i;
              }
            } else if (_source23.is_Tuple) {
              Dafny.ISequence<DAST._IType> _406___mcc_h181 = _source23.dtor_Tuple_a0;
              {
                s = _401_i;
              }
            } else if (_source23.is_Array) {
              DAST._IType _407___mcc_h183 = _source23.dtor_element;
              {
                s = _401_i;
              }
            } else if (_source23.is_Seq) {
              DAST._IType _408___mcc_h185 = _source23.dtor_element;
              {
                s = _401_i;
              }
            } else if (_source23.is_Set) {
              DAST._IType _409___mcc_h187 = _source23.dtor_element;
              {
                s = _401_i;
              }
            } else if (_source23.is_Multiset) {
              DAST._IType _410___mcc_h189 = _source23.dtor_element;
              {
                s = _401_i;
              }
            } else if (_source23.is_Map) {
              DAST._IType _411___mcc_h191 = _source23.dtor_key;
              DAST._IType _412___mcc_h192 = _source23.dtor_value;
              {
                s = _401_i;
              }
            } else if (_source23.is_Arrow) {
              Dafny.ISequence<DAST._IType> _413___mcc_h195 = _source23.dtor_args;
              DAST._IType _414___mcc_h196 = _source23.dtor_result;
              {
                s = _401_i;
              }
            } else if (_source23.is_Primitive) {
              DAST._IPrimitive _415___mcc_h199 = _source23.dtor_Primitive_a0;
              DAST._IPrimitive _source24 = _415___mcc_h199;
              if (_source24.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _401_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source24.is_Real) {
                {
                  s = _401_i;
                }
              } else if (_source24.is_String) {
                {
                  s = _401_i;
                }
              } else if (_source24.is_Bool) {
                {
                  s = _401_i;
                }
              } else {
                {
                  s = _401_i;
                }
              }
            } else if (_source23.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _416___mcc_h201 = _source23.dtor_Passthrough_a0;
              {
                s = _401_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _417___mcc_h203 = _source23.dtor_TypeArg_a0;
              {
                s = _401_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source22.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _418___mcc_h4 = _source22.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _419___mcc_h5 = _source22.dtor_DecLiteral_a1;
          DAST._IType _420___mcc_h6 = _source22.dtor_DecLiteral_a2;
          DAST._IType _421_t = _420___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _422_d = _419___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _423_n = _418___mcc_h4;
          {
            DAST._IType _source25 = _421_t;
            if (_source25.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _424___mcc_h205 = _source25.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _425___mcc_h206 = _source25.dtor_typeArgs;
              DAST._IResolvedType _426___mcc_h207 = _source25.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Nullable) {
              DAST._IType _427___mcc_h211 = _source25.dtor_Nullable_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Tuple) {
              Dafny.ISequence<DAST._IType> _428___mcc_h213 = _source25.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Array) {
              DAST._IType _429___mcc_h215 = _source25.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Seq) {
              DAST._IType _430___mcc_h217 = _source25.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Set) {
              DAST._IType _431___mcc_h219 = _source25.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Multiset) {
              DAST._IType _432___mcc_h221 = _source25.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Map) {
              DAST._IType _433___mcc_h223 = _source25.dtor_key;
              DAST._IType _434___mcc_h224 = _source25.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Arrow) {
              Dafny.ISequence<DAST._IType> _435___mcc_h227 = _source25.dtor_args;
              DAST._IType _436___mcc_h228 = _source25.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source25.is_Primitive) {
              DAST._IPrimitive _437___mcc_h231 = _source25.dtor_Primitive_a0;
              DAST._IPrimitive _source26 = _437___mcc_h231;
              if (_source26.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source26.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _423_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source26.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source26.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source25.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _438___mcc_h233 = _source25.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _439___mcc_h235 = _source25.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_423_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _422_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source22.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _440___mcc_h7 = _source22.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _441_l = _440___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _441_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source22.is_CharLiteral) {
          Dafny.Rune _442___mcc_h8 = _source22.dtor_CharLiteral_a0;
          Dafny.Rune _443_c = _442___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_443_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
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
      } else if (_source21.is_Ident) {
        Dafny.ISequence<Dafny.Rune> _444___mcc_h9 = _source21.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _445_name = _444___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _445_name);
          if (!((@params).Contains(_445_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_445_name);
        }
      } else if (_source21.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _446___mcc_h10 = _source21.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _447_path = _446___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out122;
          _out122 = DCOMP.COMP.GenPath(_447_path);
          s = _out122;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source21.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _448___mcc_h11 = _source21.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _449_values = _448___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _450_i;
          _450_i = BigInteger.Zero;
          bool _451_allErased;
          _451_allErased = true;
          while ((_450_i) < (new BigInteger((_449_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _452___v26;
            bool _453___v27;
            bool _454_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _455___v28;
            Dafny.ISequence<Dafny.Rune> _out123;
            bool _out124;
            bool _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            DCOMP.COMP.GenExpr((_449_values).Select(_450_i), selfIdent, @params, true, out _out123, out _out124, out _out125, out _out126);
            _452___v26 = _out123;
            _453___v27 = _out124;
            _454_isErased = _out125;
            _455___v28 = _out126;
            _451_allErased = (_451_allErased) && (_454_isErased);
            _450_i = (_450_i) + (BigInteger.One);
          }
          _450_i = BigInteger.Zero;
          while ((_450_i) < (new BigInteger((_449_values).Count))) {
            if ((_450_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _456_recursiveGen;
            bool _457___v29;
            bool _458_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _459_recIdents;
            Dafny.ISequence<Dafny.Rune> _out127;
            bool _out128;
            bool _out129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
            DCOMP.COMP.GenExpr((_449_values).Select(_450_i), selfIdent, @params, true, out _out127, out _out128, out _out129, out _out130);
            _456_recursiveGen = _out127;
            _457___v29 = _out128;
            _458_isErased = _out129;
            _459_recIdents = _out130;
            if ((_458_isErased) && (!(_451_allErased))) {
              _456_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _456_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _456_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _459_recIdents);
            _450_i = (_450_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _451_allErased;
        }
      } else if (_source21.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _460___mcc_h12 = _source21.dtor_path;
        Dafny.ISequence<DAST._IExpression> _461___mcc_h13 = _source21.dtor_args;
        Dafny.ISequence<DAST._IExpression> _462_args = _461___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _463_path = _460___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _464_path;
          Dafny.ISequence<Dafny.Rune> _out131;
          _out131 = DCOMP.COMP.GenPath(_463_path);
          _464_path = _out131;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _464_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _465_i;
          _465_i = BigInteger.Zero;
          while ((_465_i) < (new BigInteger((_462_args).Count))) {
            if ((_465_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _466_recursiveGen;
            bool _467___v30;
            bool _468_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _469_recIdents;
            Dafny.ISequence<Dafny.Rune> _out132;
            bool _out133;
            bool _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            DCOMP.COMP.GenExpr((_462_args).Select(_465_i), selfIdent, @params, true, out _out132, out _out133, out _out134, out _out135);
            _466_recursiveGen = _out132;
            _467___v30 = _out133;
            _468_isErased = _out134;
            _469_recIdents = _out135;
            if (_468_isErased) {
              _466_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _466_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _466_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _469_recIdents);
            _465_i = (_465_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _470___mcc_h14 = _source21.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _471_dims = _470___mcc_h14;
        {
          BigInteger _472_i;
          _472_i = (new BigInteger((_471_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_472_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _473_recursiveGen;
            bool _474___v31;
            bool _475_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _476_recIdents;
            Dafny.ISequence<Dafny.Rune> _out136;
            bool _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP.COMP.GenExpr((_471_dims).Select(_472_i), selfIdent, @params, true, out _out136, out _out137, out _out138, out _out139);
            _473_recursiveGen = _out136;
            _474___v31 = _out137;
            _475_isErased = _out138;
            _476_recIdents = _out139;
            if (!(_475_isErased)) {
              _473_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _473_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _473_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _476_recIdents);
            _472_i = (_472_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _477___mcc_h15 = _source21.dtor_path;
        Dafny.ISequence<Dafny.Rune> _478___mcc_h16 = _source21.dtor_variant;
        bool _479___mcc_h17 = _source21.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _480___mcc_h18 = _source21.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _481_values = _480___mcc_h18;
        bool _482_isCo = _479___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _483_variant = _478___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _484_path = _477___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _485_path;
          Dafny.ISequence<Dafny.Rune> _out140;
          _out140 = DCOMP.COMP.GenPath(_484_path);
          _485_path = _out140;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _485_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _483_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _486_i;
          _486_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_486_i) < (new BigInteger((_481_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_481_values).Select(_486_i);
            Dafny.ISequence<Dafny.Rune> _487_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _488_value = _let_tmp_rhs0.dtor__1;
            if ((_486_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_482_isCo) {
              Dafny.ISequence<Dafny.Rune> _489_recursiveGen;
              bool _490___v32;
              bool _491_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _492_recIdents;
              Dafny.ISequence<Dafny.Rune> _out141;
              bool _out142;
              bool _out143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
              DCOMP.COMP.GenExpr(_488_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out141, out _out142, out _out143, out _out144);
              _489_recursiveGen = _out141;
              _490___v32 = _out142;
              _491_isErased = _out143;
              _492_recIdents = _out144;
              if (!(_491_isErased)) {
                _489_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _489_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _489_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _489_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _492_recIdents);
              Dafny.ISequence<Dafny.Rune> _493_allReadCloned;
              _493_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_492_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _494_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_492_recIdents).Elements) {
                  _494_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_492_recIdents).Contains(_494_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1160)");
              after__ASSIGN_SUCH_THAT_0:;
                _493_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_493_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _494_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _494_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _492_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_492_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_494_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _487_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _493_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _489_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _495_recursiveGen;
              bool _496___v33;
              bool _497_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _498_recIdents;
              Dafny.ISequence<Dafny.Rune> _out145;
              bool _out146;
              bool _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              DCOMP.COMP.GenExpr(_488_value, selfIdent, @params, true, out _out145, out _out146, out _out147, out _out148);
              _495_recursiveGen = _out145;
              _496___v33 = _out146;
              _497_isErased = _out147;
              _498_recIdents = _out148;
              if (!(_497_isErased)) {
                _495_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _495_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _495_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _495_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _487_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _495_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _498_recIdents);
            }
            _486_i = (_486_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_Convert) {
        DAST._IExpression _499___mcc_h19 = _source21.dtor_value;
        DAST._IType _500___mcc_h20 = _source21.dtor_from;
        DAST._IType _501___mcc_h21 = _source21.dtor_typ;
        DAST._IType _502_toTpe = _501___mcc_h21;
        DAST._IType _503_fromTpe = _500___mcc_h20;
        DAST._IExpression _504_expr = _499___mcc_h19;
        {
          if (object.Equals(_503_fromTpe, _502_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _505_recursiveGen;
            bool _506_recOwned;
            bool _507_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _508_recIdents;
            Dafny.ISequence<Dafny.Rune> _out149;
            bool _out150;
            bool _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out149, out _out150, out _out151, out _out152);
            _505_recursiveGen = _out149;
            _506_recOwned = _out150;
            _507_recErased = _out151;
            _508_recIdents = _out152;
            s = _505_recursiveGen;
            isOwned = _506_recOwned;
            isErased = _507_recErased;
            readIdents = _508_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source27 = _System.Tuple2<DAST._IType, DAST._IType>.create(_503_fromTpe, _502_toTpe);
            DAST._IType _509___mcc_h237 = _source27.dtor__0;
            DAST._IType _510___mcc_h238 = _source27.dtor__1;
            DAST._IType _source28 = _509___mcc_h237;
            if (_source28.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _511___mcc_h241 = _source28.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _512___mcc_h242 = _source28.dtor_typeArgs;
              DAST._IResolvedType _513___mcc_h243 = _source28.dtor_resolved;
              DAST._IResolvedType _source29 = _513___mcc_h243;
              if (_source29.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _514___mcc_h253 = _source29.dtor_path;
                DAST._IType _source30 = _510___mcc_h238;
                if (_source30.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _515___mcc_h257 = _source30.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _516___mcc_h258 = _source30.dtor_typeArgs;
                  DAST._IResolvedType _517___mcc_h259 = _source30.dtor_resolved;
                  DAST._IResolvedType _source31 = _517___mcc_h259;
                  if (_source31.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _518___mcc_h263 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _519_recursiveGen;
                      bool _520_recOwned;
                      bool _521_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _522_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out153;
                      bool _out154;
                      bool _out155;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out153, out _out154, out _out155, out _out156);
                      _519_recursiveGen = _out153;
                      _520_recOwned = _out154;
                      _521_recErased = _out155;
                      _522_recIdents = _out156;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _519_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _520_recOwned;
                      isErased = _521_recErased;
                      readIdents = _522_recIdents;
                    }
                  } else if (_source31.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _523___mcc_h265 = _source31.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _524_recursiveGen;
                      bool _525_recOwned;
                      bool _526_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _527_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out157;
                      bool _out158;
                      bool _out159;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out157, out _out158, out _out159, out _out160);
                      _524_recursiveGen = _out157;
                      _525_recOwned = _out158;
                      _526_recErased = _out159;
                      _527_recIdents = _out160;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _524_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _525_recOwned;
                      isErased = _526_recErased;
                      readIdents = _527_recIdents;
                    }
                  } else {
                    DAST._IType _528___mcc_h267 = _source31.dtor_Newtype_a0;
                    DAST._IType _529_b = _528___mcc_h267;
                    {
                      if (object.Equals(_503_fromTpe, _529_b)) {
                        Dafny.ISequence<Dafny.Rune> _530_recursiveGen;
                        bool _531_recOwned;
                        bool _532_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _533_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out161;
                        bool _out162;
                        bool _out163;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out161, out _out162, out _out163, out _out164);
                        _530_recursiveGen = _out161;
                        _531_recOwned = _out162;
                        _532_recErased = _out163;
                        _533_recIdents = _out164;
                        Dafny.ISequence<Dafny.Rune> _534_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out165;
                        _out165 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _534_rhsType = _out165;
                        Dafny.ISequence<Dafny.Rune> _535_uneraseFn;
                        _535_uneraseFn = ((_531_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _534_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _535_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _530_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _531_recOwned;
                        isErased = false;
                        readIdents = _533_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out166;
                        bool _out167;
                        bool _out168;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _529_b), _529_b, _502_toTpe), selfIdent, @params, mustOwn, out _out166, out _out167, out _out168, out _out169);
                        s = _out166;
                        isOwned = _out167;
                        isErased = _out168;
                        readIdents = _out169;
                      }
                    }
                  }
                } else if (_source30.is_Nullable) {
                  DAST._IType _536___mcc_h269 = _source30.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _537_recursiveGen;
                    bool _538_recOwned;
                    bool _539_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _540_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out170;
                    bool _out171;
                    bool _out172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out170, out _out171, out _out172, out _out173);
                    _537_recursiveGen = _out170;
                    _538_recOwned = _out171;
                    _539_recErased = _out172;
                    _540_recIdents = _out173;
                    if (!(_538_recOwned)) {
                      _537_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_537_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _537_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _539_recErased;
                    readIdents = _540_recIdents;
                  }
                } else if (_source30.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _541___mcc_h271 = _source30.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _542_recursiveGen;
                    bool _543_recOwned;
                    bool _544_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _545_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out174;
                    bool _out175;
                    bool _out176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out174, out _out175, out _out176, out _out177);
                    _542_recursiveGen = _out174;
                    _543_recOwned = _out175;
                    _544_recErased = _out176;
                    _545_recIdents = _out177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _542_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _543_recOwned;
                    isErased = _544_recErased;
                    readIdents = _545_recIdents;
                  }
                } else if (_source30.is_Array) {
                  DAST._IType _546___mcc_h273 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _547_recursiveGen;
                    bool _548_recOwned;
                    bool _549_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _550_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out178;
                    bool _out179;
                    bool _out180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out178, out _out179, out _out180, out _out181);
                    _547_recursiveGen = _out178;
                    _548_recOwned = _out179;
                    _549_recErased = _out180;
                    _550_recIdents = _out181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _547_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _548_recOwned;
                    isErased = _549_recErased;
                    readIdents = _550_recIdents;
                  }
                } else if (_source30.is_Seq) {
                  DAST._IType _551___mcc_h275 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _552_recursiveGen;
                    bool _553_recOwned;
                    bool _554_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _555_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out182;
                    bool _out183;
                    bool _out184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out182, out _out183, out _out184, out _out185);
                    _552_recursiveGen = _out182;
                    _553_recOwned = _out183;
                    _554_recErased = _out184;
                    _555_recIdents = _out185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _552_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _553_recOwned;
                    isErased = _554_recErased;
                    readIdents = _555_recIdents;
                  }
                } else if (_source30.is_Set) {
                  DAST._IType _556___mcc_h277 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _557_recursiveGen;
                    bool _558_recOwned;
                    bool _559_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _560_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out186;
                    bool _out187;
                    bool _out188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out186, out _out187, out _out188, out _out189);
                    _557_recursiveGen = _out186;
                    _558_recOwned = _out187;
                    _559_recErased = _out188;
                    _560_recIdents = _out189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _557_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _558_recOwned;
                    isErased = _559_recErased;
                    readIdents = _560_recIdents;
                  }
                } else if (_source30.is_Multiset) {
                  DAST._IType _561___mcc_h279 = _source30.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _562_recursiveGen;
                    bool _563_recOwned;
                    bool _564_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _565_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out190;
                    bool _out191;
                    bool _out192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out190, out _out191, out _out192, out _out193);
                    _562_recursiveGen = _out190;
                    _563_recOwned = _out191;
                    _564_recErased = _out192;
                    _565_recIdents = _out193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _562_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _563_recOwned;
                    isErased = _564_recErased;
                    readIdents = _565_recIdents;
                  }
                } else if (_source30.is_Map) {
                  DAST._IType _566___mcc_h281 = _source30.dtor_key;
                  DAST._IType _567___mcc_h282 = _source30.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _568_recursiveGen;
                    bool _569_recOwned;
                    bool _570_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _571_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out194;
                    bool _out195;
                    bool _out196;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out194, out _out195, out _out196, out _out197);
                    _568_recursiveGen = _out194;
                    _569_recOwned = _out195;
                    _570_recErased = _out196;
                    _571_recIdents = _out197;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _568_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _569_recOwned;
                    isErased = _570_recErased;
                    readIdents = _571_recIdents;
                  }
                } else if (_source30.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _572___mcc_h285 = _source30.dtor_args;
                  DAST._IType _573___mcc_h286 = _source30.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _574_recursiveGen;
                    bool _575_recOwned;
                    bool _576_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _577_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out198;
                    bool _out199;
                    bool _out200;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out198, out _out199, out _out200, out _out201);
                    _574_recursiveGen = _out198;
                    _575_recOwned = _out199;
                    _576_recErased = _out200;
                    _577_recIdents = _out201;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _574_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _575_recOwned;
                    isErased = _576_recErased;
                    readIdents = _577_recIdents;
                  }
                } else if (_source30.is_Primitive) {
                  DAST._IPrimitive _578___mcc_h289 = _source30.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _579_recursiveGen;
                    bool _580_recOwned;
                    bool _581_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _582_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out202;
                    bool _out203;
                    bool _out204;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out205;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out202, out _out203, out _out204, out _out205);
                    _579_recursiveGen = _out202;
                    _580_recOwned = _out203;
                    _581_recErased = _out204;
                    _582_recIdents = _out205;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _579_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _580_recOwned;
                    isErased = _581_recErased;
                    readIdents = _582_recIdents;
                  }
                } else if (_source30.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _583___mcc_h291 = _source30.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _584_recursiveGen;
                    bool _585_recOwned;
                    bool _586_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _587_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out206;
                    bool _out207;
                    bool _out208;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out206, out _out207, out _out208, out _out209);
                    _584_recursiveGen = _out206;
                    _585_recOwned = _out207;
                    _586_recErased = _out208;
                    _587_recIdents = _out209;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _584_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _585_recOwned;
                    isErased = _586_recErased;
                    readIdents = _587_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _588___mcc_h293 = _source30.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _589_recursiveGen;
                    bool _590_recOwned;
                    bool _591_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _592_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out210;
                    bool _out211;
                    bool _out212;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out210, out _out211, out _out212, out _out213);
                    _589_recursiveGen = _out210;
                    _590_recOwned = _out211;
                    _591_recErased = _out212;
                    _592_recIdents = _out213;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _589_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _590_recOwned;
                    isErased = _591_recErased;
                    readIdents = _592_recIdents;
                  }
                }
              } else if (_source29.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _593___mcc_h295 = _source29.dtor_path;
                DAST._IType _source32 = _510___mcc_h238;
                if (_source32.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _594___mcc_h299 = _source32.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _595___mcc_h300 = _source32.dtor_typeArgs;
                  DAST._IResolvedType _596___mcc_h301 = _source32.dtor_resolved;
                  DAST._IResolvedType _source33 = _596___mcc_h301;
                  if (_source33.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _597___mcc_h305 = _source33.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _598_recursiveGen;
                      bool _599_recOwned;
                      bool _600_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _601_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out214;
                      bool _out215;
                      bool _out216;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out214, out _out215, out _out216, out _out217);
                      _598_recursiveGen = _out214;
                      _599_recOwned = _out215;
                      _600_recErased = _out216;
                      _601_recIdents = _out217;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _598_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _599_recOwned;
                      isErased = _600_recErased;
                      readIdents = _601_recIdents;
                    }
                  } else if (_source33.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _602___mcc_h307 = _source33.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _603_recursiveGen;
                      bool _604_recOwned;
                      bool _605_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _606_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out218;
                      bool _out219;
                      bool _out220;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out221;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out218, out _out219, out _out220, out _out221);
                      _603_recursiveGen = _out218;
                      _604_recOwned = _out219;
                      _605_recErased = _out220;
                      _606_recIdents = _out221;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _603_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _604_recOwned;
                      isErased = _605_recErased;
                      readIdents = _606_recIdents;
                    }
                  } else {
                    DAST._IType _607___mcc_h309 = _source33.dtor_Newtype_a0;
                    DAST._IType _608_b = _607___mcc_h309;
                    {
                      if (object.Equals(_503_fromTpe, _608_b)) {
                        Dafny.ISequence<Dafny.Rune> _609_recursiveGen;
                        bool _610_recOwned;
                        bool _611_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _612_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out222;
                        bool _out223;
                        bool _out224;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out222, out _out223, out _out224, out _out225);
                        _609_recursiveGen = _out222;
                        _610_recOwned = _out223;
                        _611_recErased = _out224;
                        _612_recIdents = _out225;
                        Dafny.ISequence<Dafny.Rune> _613_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out226;
                        _out226 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _613_rhsType = _out226;
                        Dafny.ISequence<Dafny.Rune> _614_uneraseFn;
                        _614_uneraseFn = ((_610_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _613_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _614_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _609_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _610_recOwned;
                        isErased = false;
                        readIdents = _612_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out227;
                        bool _out228;
                        bool _out229;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _608_b), _608_b, _502_toTpe), selfIdent, @params, mustOwn, out _out227, out _out228, out _out229, out _out230);
                        s = _out227;
                        isOwned = _out228;
                        isErased = _out229;
                        readIdents = _out230;
                      }
                    }
                  }
                } else if (_source32.is_Nullable) {
                  DAST._IType _615___mcc_h311 = _source32.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _616_recursiveGen;
                    bool _617_recOwned;
                    bool _618_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _619_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out231;
                    bool _out232;
                    bool _out233;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out231, out _out232, out _out233, out _out234);
                    _616_recursiveGen = _out231;
                    _617_recOwned = _out232;
                    _618_recErased = _out233;
                    _619_recIdents = _out234;
                    if (!(_617_recOwned)) {
                      _616_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_616_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _616_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _618_recErased;
                    readIdents = _619_recIdents;
                  }
                } else if (_source32.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _620___mcc_h313 = _source32.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _621_recursiveGen;
                    bool _622_recOwned;
                    bool _623_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _624_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out235;
                    bool _out236;
                    bool _out237;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out235, out _out236, out _out237, out _out238);
                    _621_recursiveGen = _out235;
                    _622_recOwned = _out236;
                    _623_recErased = _out237;
                    _624_recIdents = _out238;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _621_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _622_recOwned;
                    isErased = _623_recErased;
                    readIdents = _624_recIdents;
                  }
                } else if (_source32.is_Array) {
                  DAST._IType _625___mcc_h315 = _source32.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _626_recursiveGen;
                    bool _627_recOwned;
                    bool _628_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _629_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out239;
                    bool _out240;
                    bool _out241;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out242;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out239, out _out240, out _out241, out _out242);
                    _626_recursiveGen = _out239;
                    _627_recOwned = _out240;
                    _628_recErased = _out241;
                    _629_recIdents = _out242;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _626_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _627_recOwned;
                    isErased = _628_recErased;
                    readIdents = _629_recIdents;
                  }
                } else if (_source32.is_Seq) {
                  DAST._IType _630___mcc_h317 = _source32.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _631_recursiveGen;
                    bool _632_recOwned;
                    bool _633_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _634_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out243;
                    bool _out244;
                    bool _out245;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out243, out _out244, out _out245, out _out246);
                    _631_recursiveGen = _out243;
                    _632_recOwned = _out244;
                    _633_recErased = _out245;
                    _634_recIdents = _out246;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _631_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _632_recOwned;
                    isErased = _633_recErased;
                    readIdents = _634_recIdents;
                  }
                } else if (_source32.is_Set) {
                  DAST._IType _635___mcc_h319 = _source32.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _636_recursiveGen;
                    bool _637_recOwned;
                    bool _638_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _639_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out247;
                    bool _out248;
                    bool _out249;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out247, out _out248, out _out249, out _out250);
                    _636_recursiveGen = _out247;
                    _637_recOwned = _out248;
                    _638_recErased = _out249;
                    _639_recIdents = _out250;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _636_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _637_recOwned;
                    isErased = _638_recErased;
                    readIdents = _639_recIdents;
                  }
                } else if (_source32.is_Multiset) {
                  DAST._IType _640___mcc_h321 = _source32.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _641_recursiveGen;
                    bool _642_recOwned;
                    bool _643_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _644_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out251;
                    bool _out252;
                    bool _out253;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out251, out _out252, out _out253, out _out254);
                    _641_recursiveGen = _out251;
                    _642_recOwned = _out252;
                    _643_recErased = _out253;
                    _644_recIdents = _out254;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _641_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _642_recOwned;
                    isErased = _643_recErased;
                    readIdents = _644_recIdents;
                  }
                } else if (_source32.is_Map) {
                  DAST._IType _645___mcc_h323 = _source32.dtor_key;
                  DAST._IType _646___mcc_h324 = _source32.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _647_recursiveGen;
                    bool _648_recOwned;
                    bool _649_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _650_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out255;
                    bool _out256;
                    bool _out257;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out255, out _out256, out _out257, out _out258);
                    _647_recursiveGen = _out255;
                    _648_recOwned = _out256;
                    _649_recErased = _out257;
                    _650_recIdents = _out258;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _647_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _648_recOwned;
                    isErased = _649_recErased;
                    readIdents = _650_recIdents;
                  }
                } else if (_source32.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _651___mcc_h327 = _source32.dtor_args;
                  DAST._IType _652___mcc_h328 = _source32.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _653_recursiveGen;
                    bool _654_recOwned;
                    bool _655_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _656_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out259;
                    bool _out260;
                    bool _out261;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out259, out _out260, out _out261, out _out262);
                    _653_recursiveGen = _out259;
                    _654_recOwned = _out260;
                    _655_recErased = _out261;
                    _656_recIdents = _out262;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _653_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _654_recOwned;
                    isErased = _655_recErased;
                    readIdents = _656_recIdents;
                  }
                } else if (_source32.is_Primitive) {
                  DAST._IPrimitive _657___mcc_h331 = _source32.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _658_recursiveGen;
                    bool _659_recOwned;
                    bool _660_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _661_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out263;
                    bool _out264;
                    bool _out265;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out263, out _out264, out _out265, out _out266);
                    _658_recursiveGen = _out263;
                    _659_recOwned = _out264;
                    _660_recErased = _out265;
                    _661_recIdents = _out266;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _658_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _659_recOwned;
                    isErased = _660_recErased;
                    readIdents = _661_recIdents;
                  }
                } else if (_source32.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _662___mcc_h333 = _source32.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _663_recursiveGen;
                    bool _664_recOwned;
                    bool _665_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _666_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out267;
                    bool _out268;
                    bool _out269;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out267, out _out268, out _out269, out _out270);
                    _663_recursiveGen = _out267;
                    _664_recOwned = _out268;
                    _665_recErased = _out269;
                    _666_recIdents = _out270;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _663_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _664_recOwned;
                    isErased = _665_recErased;
                    readIdents = _666_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _667___mcc_h335 = _source32.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _668_recursiveGen;
                    bool _669_recOwned;
                    bool _670_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _671_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out271;
                    bool _out272;
                    bool _out273;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out271, out _out272, out _out273, out _out274);
                    _668_recursiveGen = _out271;
                    _669_recOwned = _out272;
                    _670_recErased = _out273;
                    _671_recIdents = _out274;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _668_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _669_recOwned;
                    isErased = _670_recErased;
                    readIdents = _671_recIdents;
                  }
                }
              } else {
                DAST._IType _672___mcc_h337 = _source29.dtor_Newtype_a0;
                DAST._IType _source34 = _510___mcc_h238;
                if (_source34.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _673___mcc_h341 = _source34.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _674___mcc_h342 = _source34.dtor_typeArgs;
                  DAST._IResolvedType _675___mcc_h343 = _source34.dtor_resolved;
                  DAST._IResolvedType _source35 = _675___mcc_h343;
                  if (_source35.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _676___mcc_h350 = _source35.dtor_path;
                    DAST._IType _677_b = _672___mcc_h337;
                    {
                      if (object.Equals(_677_b, _502_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _678_recursiveGen;
                        bool _679_recOwned;
                        bool _680_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _681_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out275;
                        bool _out276;
                        bool _out277;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out275, out _out276, out _out277, out _out278);
                        _678_recursiveGen = _out275;
                        _679_recOwned = _out276;
                        _680_recErased = _out277;
                        _681_recIdents = _out278;
                        Dafny.ISequence<Dafny.Rune> _682_uneraseFn;
                        _682_uneraseFn = ((_679_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _682_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _678_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _679_recOwned;
                        isErased = true;
                        readIdents = _681_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out279;
                        bool _out280;
                        bool _out281;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _677_b), _677_b, _502_toTpe), selfIdent, @params, mustOwn, out _out279, out _out280, out _out281, out _out282);
                        s = _out279;
                        isOwned = _out280;
                        isErased = _out281;
                        readIdents = _out282;
                      }
                    }
                  } else if (_source35.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _683___mcc_h353 = _source35.dtor_path;
                    DAST._IType _684_b = _672___mcc_h337;
                    {
                      if (object.Equals(_684_b, _502_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _685_recursiveGen;
                        bool _686_recOwned;
                        bool _687_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _688_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out283;
                        bool _out284;
                        bool _out285;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out283, out _out284, out _out285, out _out286);
                        _685_recursiveGen = _out283;
                        _686_recOwned = _out284;
                        _687_recErased = _out285;
                        _688_recIdents = _out286;
                        Dafny.ISequence<Dafny.Rune> _689_uneraseFn;
                        _689_uneraseFn = ((_686_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _689_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _685_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _686_recOwned;
                        isErased = true;
                        readIdents = _688_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out287;
                        bool _out288;
                        bool _out289;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _684_b), _684_b, _502_toTpe), selfIdent, @params, mustOwn, out _out287, out _out288, out _out289, out _out290);
                        s = _out287;
                        isOwned = _out288;
                        isErased = _out289;
                        readIdents = _out290;
                      }
                    }
                  } else {
                    DAST._IType _690___mcc_h356 = _source35.dtor_Newtype_a0;
                    DAST._IType _691_b = _690___mcc_h356;
                    {
                      if (object.Equals(_503_fromTpe, _691_b)) {
                        Dafny.ISequence<Dafny.Rune> _692_recursiveGen;
                        bool _693_recOwned;
                        bool _694_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _695_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out291;
                        bool _out292;
                        bool _out293;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out291, out _out292, out _out293, out _out294);
                        _692_recursiveGen = _out291;
                        _693_recOwned = _out292;
                        _694_recErased = _out293;
                        _695_recIdents = _out294;
                        Dafny.ISequence<Dafny.Rune> _696_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out295;
                        _out295 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _696_rhsType = _out295;
                        Dafny.ISequence<Dafny.Rune> _697_uneraseFn;
                        _697_uneraseFn = ((_693_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _696_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _697_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _692_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _693_recOwned;
                        isErased = false;
                        readIdents = _695_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out296;
                        bool _out297;
                        bool _out298;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _691_b), _691_b, _502_toTpe), selfIdent, @params, mustOwn, out _out296, out _out297, out _out298, out _out299);
                        s = _out296;
                        isOwned = _out297;
                        isErased = _out298;
                        readIdents = _out299;
                      }
                    }
                  }
                } else if (_source34.is_Nullable) {
                  DAST._IType _698___mcc_h359 = _source34.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _699_recursiveGen;
                    bool _700_recOwned;
                    bool _701_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _702_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out300;
                    bool _out301;
                    bool _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out300, out _out301, out _out302, out _out303);
                    _699_recursiveGen = _out300;
                    _700_recOwned = _out301;
                    _701_recErased = _out302;
                    _702_recIdents = _out303;
                    if (!(_700_recOwned)) {
                      _699_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_699_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _699_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _701_recErased;
                    readIdents = _702_recIdents;
                  }
                } else if (_source34.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _703___mcc_h362 = _source34.dtor_Tuple_a0;
                  DAST._IType _704_b = _672___mcc_h337;
                  {
                    if (object.Equals(_704_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _705_recursiveGen;
                      bool _706_recOwned;
                      bool _707_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _708_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out304;
                      bool _out305;
                      bool _out306;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out304, out _out305, out _out306, out _out307);
                      _705_recursiveGen = _out304;
                      _706_recOwned = _out305;
                      _707_recErased = _out306;
                      _708_recIdents = _out307;
                      Dafny.ISequence<Dafny.Rune> _709_uneraseFn;
                      _709_uneraseFn = ((_706_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _709_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _705_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _706_recOwned;
                      isErased = true;
                      readIdents = _708_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out308;
                      bool _out309;
                      bool _out310;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _704_b), _704_b, _502_toTpe), selfIdent, @params, mustOwn, out _out308, out _out309, out _out310, out _out311);
                      s = _out308;
                      isOwned = _out309;
                      isErased = _out310;
                      readIdents = _out311;
                    }
                  }
                } else if (_source34.is_Array) {
                  DAST._IType _710___mcc_h365 = _source34.dtor_element;
                  DAST._IType _711_b = _672___mcc_h337;
                  {
                    if (object.Equals(_711_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _712_recursiveGen;
                      bool _713_recOwned;
                      bool _714_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _715_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out312;
                      bool _out313;
                      bool _out314;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out312, out _out313, out _out314, out _out315);
                      _712_recursiveGen = _out312;
                      _713_recOwned = _out313;
                      _714_recErased = _out314;
                      _715_recIdents = _out315;
                      Dafny.ISequence<Dafny.Rune> _716_uneraseFn;
                      _716_uneraseFn = ((_713_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _716_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _712_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _713_recOwned;
                      isErased = true;
                      readIdents = _715_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out316;
                      bool _out317;
                      bool _out318;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _711_b), _711_b, _502_toTpe), selfIdent, @params, mustOwn, out _out316, out _out317, out _out318, out _out319);
                      s = _out316;
                      isOwned = _out317;
                      isErased = _out318;
                      readIdents = _out319;
                    }
                  }
                } else if (_source34.is_Seq) {
                  DAST._IType _717___mcc_h368 = _source34.dtor_element;
                  DAST._IType _718_b = _672___mcc_h337;
                  {
                    if (object.Equals(_718_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _719_recursiveGen;
                      bool _720_recOwned;
                      bool _721_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _722_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out320;
                      bool _out321;
                      bool _out322;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out320, out _out321, out _out322, out _out323);
                      _719_recursiveGen = _out320;
                      _720_recOwned = _out321;
                      _721_recErased = _out322;
                      _722_recIdents = _out323;
                      Dafny.ISequence<Dafny.Rune> _723_uneraseFn;
                      _723_uneraseFn = ((_720_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _723_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _719_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _720_recOwned;
                      isErased = true;
                      readIdents = _722_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out324;
                      bool _out325;
                      bool _out326;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _718_b), _718_b, _502_toTpe), selfIdent, @params, mustOwn, out _out324, out _out325, out _out326, out _out327);
                      s = _out324;
                      isOwned = _out325;
                      isErased = _out326;
                      readIdents = _out327;
                    }
                  }
                } else if (_source34.is_Set) {
                  DAST._IType _724___mcc_h371 = _source34.dtor_element;
                  DAST._IType _725_b = _672___mcc_h337;
                  {
                    if (object.Equals(_725_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _726_recursiveGen;
                      bool _727_recOwned;
                      bool _728_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _729_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out328;
                      bool _out329;
                      bool _out330;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out328, out _out329, out _out330, out _out331);
                      _726_recursiveGen = _out328;
                      _727_recOwned = _out329;
                      _728_recErased = _out330;
                      _729_recIdents = _out331;
                      Dafny.ISequence<Dafny.Rune> _730_uneraseFn;
                      _730_uneraseFn = ((_727_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _730_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _726_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _727_recOwned;
                      isErased = true;
                      readIdents = _729_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out332;
                      bool _out333;
                      bool _out334;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _725_b), _725_b, _502_toTpe), selfIdent, @params, mustOwn, out _out332, out _out333, out _out334, out _out335);
                      s = _out332;
                      isOwned = _out333;
                      isErased = _out334;
                      readIdents = _out335;
                    }
                  }
                } else if (_source34.is_Multiset) {
                  DAST._IType _731___mcc_h374 = _source34.dtor_element;
                  DAST._IType _732_b = _672___mcc_h337;
                  {
                    if (object.Equals(_732_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _733_recursiveGen;
                      bool _734_recOwned;
                      bool _735_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _736_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out336;
                      bool _out337;
                      bool _out338;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out336, out _out337, out _out338, out _out339);
                      _733_recursiveGen = _out336;
                      _734_recOwned = _out337;
                      _735_recErased = _out338;
                      _736_recIdents = _out339;
                      Dafny.ISequence<Dafny.Rune> _737_uneraseFn;
                      _737_uneraseFn = ((_734_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _737_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _733_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _734_recOwned;
                      isErased = true;
                      readIdents = _736_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out340;
                      bool _out341;
                      bool _out342;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _732_b), _732_b, _502_toTpe), selfIdent, @params, mustOwn, out _out340, out _out341, out _out342, out _out343);
                      s = _out340;
                      isOwned = _out341;
                      isErased = _out342;
                      readIdents = _out343;
                    }
                  }
                } else if (_source34.is_Map) {
                  DAST._IType _738___mcc_h377 = _source34.dtor_key;
                  DAST._IType _739___mcc_h378 = _source34.dtor_value;
                  DAST._IType _740_b = _672___mcc_h337;
                  {
                    if (object.Equals(_740_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _741_recursiveGen;
                      bool _742_recOwned;
                      bool _743_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _744_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out344;
                      bool _out345;
                      bool _out346;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out347;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out344, out _out345, out _out346, out _out347);
                      _741_recursiveGen = _out344;
                      _742_recOwned = _out345;
                      _743_recErased = _out346;
                      _744_recIdents = _out347;
                      Dafny.ISequence<Dafny.Rune> _745_uneraseFn;
                      _745_uneraseFn = ((_742_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _745_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _741_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _742_recOwned;
                      isErased = true;
                      readIdents = _744_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out348;
                      bool _out349;
                      bool _out350;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _740_b), _740_b, _502_toTpe), selfIdent, @params, mustOwn, out _out348, out _out349, out _out350, out _out351);
                      s = _out348;
                      isOwned = _out349;
                      isErased = _out350;
                      readIdents = _out351;
                    }
                  }
                } else if (_source34.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _746___mcc_h383 = _source34.dtor_args;
                  DAST._IType _747___mcc_h384 = _source34.dtor_result;
                  DAST._IType _748_b = _672___mcc_h337;
                  {
                    if (object.Equals(_748_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _749_recursiveGen;
                      bool _750_recOwned;
                      bool _751_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _752_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out352;
                      bool _out353;
                      bool _out354;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out352, out _out353, out _out354, out _out355);
                      _749_recursiveGen = _out352;
                      _750_recOwned = _out353;
                      _751_recErased = _out354;
                      _752_recIdents = _out355;
                      Dafny.ISequence<Dafny.Rune> _753_uneraseFn;
                      _753_uneraseFn = ((_750_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _753_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _749_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _750_recOwned;
                      isErased = true;
                      readIdents = _752_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out356;
                      bool _out357;
                      bool _out358;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out359;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _748_b), _748_b, _502_toTpe), selfIdent, @params, mustOwn, out _out356, out _out357, out _out358, out _out359);
                      s = _out356;
                      isOwned = _out357;
                      isErased = _out358;
                      readIdents = _out359;
                    }
                  }
                } else if (_source34.is_Primitive) {
                  DAST._IPrimitive _754___mcc_h389 = _source34.dtor_Primitive_a0;
                  DAST._IType _755_b = _672___mcc_h337;
                  {
                    if (object.Equals(_755_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _756_recursiveGen;
                      bool _757_recOwned;
                      bool _758_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _759_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out360;
                      bool _out361;
                      bool _out362;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out360, out _out361, out _out362, out _out363);
                      _756_recursiveGen = _out360;
                      _757_recOwned = _out361;
                      _758_recErased = _out362;
                      _759_recIdents = _out363;
                      Dafny.ISequence<Dafny.Rune> _760_uneraseFn;
                      _760_uneraseFn = ((_757_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _760_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _756_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _757_recOwned;
                      isErased = true;
                      readIdents = _759_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out364;
                      bool _out365;
                      bool _out366;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _755_b), _755_b, _502_toTpe), selfIdent, @params, mustOwn, out _out364, out _out365, out _out366, out _out367);
                      s = _out364;
                      isOwned = _out365;
                      isErased = _out366;
                      readIdents = _out367;
                    }
                  }
                } else if (_source34.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _761___mcc_h392 = _source34.dtor_Passthrough_a0;
                  DAST._IType _762_b = _672___mcc_h337;
                  {
                    if (object.Equals(_762_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _763_recursiveGen;
                      bool _764_recOwned;
                      bool _765_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _766_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out368;
                      bool _out369;
                      bool _out370;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out368, out _out369, out _out370, out _out371);
                      _763_recursiveGen = _out368;
                      _764_recOwned = _out369;
                      _765_recErased = _out370;
                      _766_recIdents = _out371;
                      Dafny.ISequence<Dafny.Rune> _767_uneraseFn;
                      _767_uneraseFn = ((_764_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _767_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _763_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _764_recOwned;
                      isErased = true;
                      readIdents = _766_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out372;
                      bool _out373;
                      bool _out374;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _762_b), _762_b, _502_toTpe), selfIdent, @params, mustOwn, out _out372, out _out373, out _out374, out _out375);
                      s = _out372;
                      isOwned = _out373;
                      isErased = _out374;
                      readIdents = _out375;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _768___mcc_h395 = _source34.dtor_TypeArg_a0;
                  DAST._IType _769_b = _672___mcc_h337;
                  {
                    if (object.Equals(_769_b, _502_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _770_recursiveGen;
                      bool _771_recOwned;
                      bool _772_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _773_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out376;
                      bool _out377;
                      bool _out378;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out376, out _out377, out _out378, out _out379);
                      _770_recursiveGen = _out376;
                      _771_recOwned = _out377;
                      _772_recErased = _out378;
                      _773_recIdents = _out379;
                      Dafny.ISequence<Dafny.Rune> _774_uneraseFn;
                      _774_uneraseFn = ((_771_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _774_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _770_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _771_recOwned;
                      isErased = true;
                      readIdents = _773_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out380;
                      bool _out381;
                      bool _out382;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _769_b), _769_b, _502_toTpe), selfIdent, @params, mustOwn, out _out380, out _out381, out _out382, out _out383);
                      s = _out380;
                      isOwned = _out381;
                      isErased = _out382;
                      readIdents = _out383;
                    }
                  }
                }
              }
            } else if (_source28.is_Nullable) {
              DAST._IType _775___mcc_h398 = _source28.dtor_Nullable_a0;
              DAST._IType _source36 = _510___mcc_h238;
              if (_source36.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _776___mcc_h402 = _source36.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _777___mcc_h403 = _source36.dtor_typeArgs;
                DAST._IResolvedType _778___mcc_h404 = _source36.dtor_resolved;
                DAST._IResolvedType _source37 = _778___mcc_h404;
                if (_source37.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _779___mcc_h411 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _780_recursiveGen;
                    bool _781_recOwned;
                    bool _782_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _783_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out384;
                    bool _out385;
                    bool _out386;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out384, out _out385, out _out386, out _out387);
                    _780_recursiveGen = _out384;
                    _781_recOwned = _out385;
                    _782_recErased = _out386;
                    _783_recIdents = _out387;
                    if (!(_781_recOwned)) {
                      _780_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_780_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_780_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _781_recOwned;
                    isErased = _782_recErased;
                    readIdents = _783_recIdents;
                  }
                } else if (_source37.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _784___mcc_h414 = _source37.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _785_recursiveGen;
                    bool _786_recOwned;
                    bool _787_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _788_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out388;
                    bool _out389;
                    bool _out390;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out388, out _out389, out _out390, out _out391);
                    _785_recursiveGen = _out388;
                    _786_recOwned = _out389;
                    _787_recErased = _out390;
                    _788_recIdents = _out391;
                    if (!(_786_recOwned)) {
                      _785_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_785_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_785_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _786_recOwned;
                    isErased = _787_recErased;
                    readIdents = _788_recIdents;
                  }
                } else {
                  DAST._IType _789___mcc_h417 = _source37.dtor_Newtype_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _790_recursiveGen;
                    bool _791_recOwned;
                    bool _792_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _793_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out392;
                    bool _out393;
                    bool _out394;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out392, out _out393, out _out394, out _out395);
                    _790_recursiveGen = _out392;
                    _791_recOwned = _out393;
                    _792_recErased = _out394;
                    _793_recIdents = _out395;
                    if (!(_791_recOwned)) {
                      _790_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_790_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_790_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _791_recOwned;
                    isErased = _792_recErased;
                    readIdents = _793_recIdents;
                  }
                }
              } else if (_source36.is_Nullable) {
                DAST._IType _794___mcc_h420 = _source36.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _795_recursiveGen;
                  bool _796_recOwned;
                  bool _797_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _798_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out396;
                  bool _out397;
                  bool _out398;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out396, out _out397, out _out398, out _out399);
                  _795_recursiveGen = _out396;
                  _796_recOwned = _out397;
                  _797_recErased = _out398;
                  _798_recIdents = _out399;
                  if (!(_796_recOwned)) {
                    _795_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_795_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_795_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _796_recOwned;
                  isErased = _797_recErased;
                  readIdents = _798_recIdents;
                }
              } else if (_source36.is_Tuple) {
                Dafny.ISequence<DAST._IType> _799___mcc_h423 = _source36.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _800_recursiveGen;
                  bool _801_recOwned;
                  bool _802_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _803_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out400;
                  bool _out401;
                  bool _out402;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out400, out _out401, out _out402, out _out403);
                  _800_recursiveGen = _out400;
                  _801_recOwned = _out401;
                  _802_recErased = _out402;
                  _803_recIdents = _out403;
                  if (!(_801_recOwned)) {
                    _800_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_800_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_800_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _801_recOwned;
                  isErased = _802_recErased;
                  readIdents = _803_recIdents;
                }
              } else if (_source36.is_Array) {
                DAST._IType _804___mcc_h426 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _805_recursiveGen;
                  bool _806_recOwned;
                  bool _807_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _808_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out404;
                  bool _out405;
                  bool _out406;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out404, out _out405, out _out406, out _out407);
                  _805_recursiveGen = _out404;
                  _806_recOwned = _out405;
                  _807_recErased = _out406;
                  _808_recIdents = _out407;
                  if (!(_806_recOwned)) {
                    _805_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_805_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_805_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _806_recOwned;
                  isErased = _807_recErased;
                  readIdents = _808_recIdents;
                }
              } else if (_source36.is_Seq) {
                DAST._IType _809___mcc_h429 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _810_recursiveGen;
                  bool _811_recOwned;
                  bool _812_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _813_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out408;
                  bool _out409;
                  bool _out410;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out408, out _out409, out _out410, out _out411);
                  _810_recursiveGen = _out408;
                  _811_recOwned = _out409;
                  _812_recErased = _out410;
                  _813_recIdents = _out411;
                  if (!(_811_recOwned)) {
                    _810_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_810_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_810_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _811_recOwned;
                  isErased = _812_recErased;
                  readIdents = _813_recIdents;
                }
              } else if (_source36.is_Set) {
                DAST._IType _814___mcc_h432 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _815_recursiveGen;
                  bool _816_recOwned;
                  bool _817_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _818_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out412;
                  bool _out413;
                  bool _out414;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out412, out _out413, out _out414, out _out415);
                  _815_recursiveGen = _out412;
                  _816_recOwned = _out413;
                  _817_recErased = _out414;
                  _818_recIdents = _out415;
                  if (!(_816_recOwned)) {
                    _815_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_815_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_815_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _816_recOwned;
                  isErased = _817_recErased;
                  readIdents = _818_recIdents;
                }
              } else if (_source36.is_Multiset) {
                DAST._IType _819___mcc_h435 = _source36.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _820_recursiveGen;
                  bool _821_recOwned;
                  bool _822_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _823_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out416;
                  bool _out417;
                  bool _out418;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out416, out _out417, out _out418, out _out419);
                  _820_recursiveGen = _out416;
                  _821_recOwned = _out417;
                  _822_recErased = _out418;
                  _823_recIdents = _out419;
                  if (!(_821_recOwned)) {
                    _820_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_820_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_820_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _821_recOwned;
                  isErased = _822_recErased;
                  readIdents = _823_recIdents;
                }
              } else if (_source36.is_Map) {
                DAST._IType _824___mcc_h438 = _source36.dtor_key;
                DAST._IType _825___mcc_h439 = _source36.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _826_recursiveGen;
                  bool _827_recOwned;
                  bool _828_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _829_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out420;
                  bool _out421;
                  bool _out422;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out420, out _out421, out _out422, out _out423);
                  _826_recursiveGen = _out420;
                  _827_recOwned = _out421;
                  _828_recErased = _out422;
                  _829_recIdents = _out423;
                  if (!(_827_recOwned)) {
                    _826_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_826_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_826_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _827_recOwned;
                  isErased = _828_recErased;
                  readIdents = _829_recIdents;
                }
              } else if (_source36.is_Arrow) {
                Dafny.ISequence<DAST._IType> _830___mcc_h444 = _source36.dtor_args;
                DAST._IType _831___mcc_h445 = _source36.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _832_recursiveGen;
                  bool _833_recOwned;
                  bool _834_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _835_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out424;
                  bool _out425;
                  bool _out426;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out424, out _out425, out _out426, out _out427);
                  _832_recursiveGen = _out424;
                  _833_recOwned = _out425;
                  _834_recErased = _out426;
                  _835_recIdents = _out427;
                  if (!(_833_recOwned)) {
                    _832_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_832_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_832_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _833_recOwned;
                  isErased = _834_recErased;
                  readIdents = _835_recIdents;
                }
              } else if (_source36.is_Primitive) {
                DAST._IPrimitive _836___mcc_h450 = _source36.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _837_recursiveGen;
                  bool _838_recOwned;
                  bool _839_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _840_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out428;
                  bool _out429;
                  bool _out430;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out428, out _out429, out _out430, out _out431);
                  _837_recursiveGen = _out428;
                  _838_recOwned = _out429;
                  _839_recErased = _out430;
                  _840_recIdents = _out431;
                  if (!(_838_recOwned)) {
                    _837_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_837_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_837_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _838_recOwned;
                  isErased = _839_recErased;
                  readIdents = _840_recIdents;
                }
              } else if (_source36.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _841___mcc_h453 = _source36.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _842_recursiveGen;
                  bool _843_recOwned;
                  bool _844_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _845_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out432;
                  bool _out433;
                  bool _out434;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out432, out _out433, out _out434, out _out435);
                  _842_recursiveGen = _out432;
                  _843_recOwned = _out433;
                  _844_recErased = _out434;
                  _845_recIdents = _out435;
                  if (!(_843_recOwned)) {
                    _842_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_842_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_842_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _843_recOwned;
                  isErased = _844_recErased;
                  readIdents = _845_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _846___mcc_h456 = _source36.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _847_recursiveGen;
                  bool _848_recOwned;
                  bool _849_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _850_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out436;
                  bool _out437;
                  bool _out438;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out436, out _out437, out _out438, out _out439);
                  _847_recursiveGen = _out436;
                  _848_recOwned = _out437;
                  _849_recErased = _out438;
                  _850_recIdents = _out439;
                  if (!(_848_recOwned)) {
                    _847_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_847_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_847_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _848_recOwned;
                  isErased = _849_recErased;
                  readIdents = _850_recIdents;
                }
              }
            } else if (_source28.is_Tuple) {
              Dafny.ISequence<DAST._IType> _851___mcc_h459 = _source28.dtor_Tuple_a0;
              DAST._IType _source38 = _510___mcc_h238;
              if (_source38.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _852___mcc_h463 = _source38.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _853___mcc_h464 = _source38.dtor_typeArgs;
                DAST._IResolvedType _854___mcc_h465 = _source38.dtor_resolved;
                DAST._IResolvedType _source39 = _854___mcc_h465;
                if (_source39.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _855___mcc_h469 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _856_recursiveGen;
                    bool _857_recOwned;
                    bool _858_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _859_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out440;
                    bool _out441;
                    bool _out442;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out440, out _out441, out _out442, out _out443);
                    _856_recursiveGen = _out440;
                    _857_recOwned = _out441;
                    _858_recErased = _out442;
                    _859_recIdents = _out443;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _856_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _857_recOwned;
                    isErased = _858_recErased;
                    readIdents = _859_recIdents;
                  }
                } else if (_source39.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _860___mcc_h471 = _source39.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _861_recursiveGen;
                    bool _862_recOwned;
                    bool _863_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _864_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out444;
                    bool _out445;
                    bool _out446;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out444, out _out445, out _out446, out _out447);
                    _861_recursiveGen = _out444;
                    _862_recOwned = _out445;
                    _863_recErased = _out446;
                    _864_recIdents = _out447;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _861_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _862_recOwned;
                    isErased = _863_recErased;
                    readIdents = _864_recIdents;
                  }
                } else {
                  DAST._IType _865___mcc_h473 = _source39.dtor_Newtype_a0;
                  DAST._IType _866_b = _865___mcc_h473;
                  {
                    if (object.Equals(_503_fromTpe, _866_b)) {
                      Dafny.ISequence<Dafny.Rune> _867_recursiveGen;
                      bool _868_recOwned;
                      bool _869_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _870_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out448;
                      bool _out449;
                      bool _out450;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out448, out _out449, out _out450, out _out451);
                      _867_recursiveGen = _out448;
                      _868_recOwned = _out449;
                      _869_recErased = _out450;
                      _870_recIdents = _out451;
                      Dafny.ISequence<Dafny.Rune> _871_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out452;
                      _out452 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _871_rhsType = _out452;
                      Dafny.ISequence<Dafny.Rune> _872_uneraseFn;
                      _872_uneraseFn = ((_868_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _871_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _872_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _867_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _868_recOwned;
                      isErased = false;
                      readIdents = _870_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out453;
                      bool _out454;
                      bool _out455;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _866_b), _866_b, _502_toTpe), selfIdent, @params, mustOwn, out _out453, out _out454, out _out455, out _out456);
                      s = _out453;
                      isOwned = _out454;
                      isErased = _out455;
                      readIdents = _out456;
                    }
                  }
                }
              } else if (_source38.is_Nullable) {
                DAST._IType _873___mcc_h475 = _source38.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _874_recursiveGen;
                  bool _875_recOwned;
                  bool _876_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _877_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out457;
                  bool _out458;
                  bool _out459;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out457, out _out458, out _out459, out _out460);
                  _874_recursiveGen = _out457;
                  _875_recOwned = _out458;
                  _876_recErased = _out459;
                  _877_recIdents = _out460;
                  if (!(_875_recOwned)) {
                    _874_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_874_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _874_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _876_recErased;
                  readIdents = _877_recIdents;
                }
              } else if (_source38.is_Tuple) {
                Dafny.ISequence<DAST._IType> _878___mcc_h477 = _source38.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _879_recursiveGen;
                  bool _880_recOwned;
                  bool _881_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _882_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out461;
                  bool _out462;
                  bool _out463;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out461, out _out462, out _out463, out _out464);
                  _879_recursiveGen = _out461;
                  _880_recOwned = _out462;
                  _881_recErased = _out463;
                  _882_recIdents = _out464;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _879_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _880_recOwned;
                  isErased = _881_recErased;
                  readIdents = _882_recIdents;
                }
              } else if (_source38.is_Array) {
                DAST._IType _883___mcc_h479 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _884_recursiveGen;
                  bool _885_recOwned;
                  bool _886_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _887_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out465;
                  bool _out466;
                  bool _out467;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out465, out _out466, out _out467, out _out468);
                  _884_recursiveGen = _out465;
                  _885_recOwned = _out466;
                  _886_recErased = _out467;
                  _887_recIdents = _out468;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _884_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _885_recOwned;
                  isErased = _886_recErased;
                  readIdents = _887_recIdents;
                }
              } else if (_source38.is_Seq) {
                DAST._IType _888___mcc_h481 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _889_recursiveGen;
                  bool _890_recOwned;
                  bool _891_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _892_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out469;
                  bool _out470;
                  bool _out471;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out469, out _out470, out _out471, out _out472);
                  _889_recursiveGen = _out469;
                  _890_recOwned = _out470;
                  _891_recErased = _out471;
                  _892_recIdents = _out472;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _889_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _890_recOwned;
                  isErased = _891_recErased;
                  readIdents = _892_recIdents;
                }
              } else if (_source38.is_Set) {
                DAST._IType _893___mcc_h483 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _894_recursiveGen;
                  bool _895_recOwned;
                  bool _896_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _897_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out473;
                  bool _out474;
                  bool _out475;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out473, out _out474, out _out475, out _out476);
                  _894_recursiveGen = _out473;
                  _895_recOwned = _out474;
                  _896_recErased = _out475;
                  _897_recIdents = _out476;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _894_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _895_recOwned;
                  isErased = _896_recErased;
                  readIdents = _897_recIdents;
                }
              } else if (_source38.is_Multiset) {
                DAST._IType _898___mcc_h485 = _source38.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _899_recursiveGen;
                  bool _900_recOwned;
                  bool _901_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _902_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out477;
                  bool _out478;
                  bool _out479;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out477, out _out478, out _out479, out _out480);
                  _899_recursiveGen = _out477;
                  _900_recOwned = _out478;
                  _901_recErased = _out479;
                  _902_recIdents = _out480;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _899_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _900_recOwned;
                  isErased = _901_recErased;
                  readIdents = _902_recIdents;
                }
              } else if (_source38.is_Map) {
                DAST._IType _903___mcc_h487 = _source38.dtor_key;
                DAST._IType _904___mcc_h488 = _source38.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _905_recursiveGen;
                  bool _906_recOwned;
                  bool _907_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _908_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out481;
                  bool _out482;
                  bool _out483;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out481, out _out482, out _out483, out _out484);
                  _905_recursiveGen = _out481;
                  _906_recOwned = _out482;
                  _907_recErased = _out483;
                  _908_recIdents = _out484;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _905_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _906_recOwned;
                  isErased = _907_recErased;
                  readIdents = _908_recIdents;
                }
              } else if (_source38.is_Arrow) {
                Dafny.ISequence<DAST._IType> _909___mcc_h491 = _source38.dtor_args;
                DAST._IType _910___mcc_h492 = _source38.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _911_recursiveGen;
                  bool _912_recOwned;
                  bool _913_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _914_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out485;
                  bool _out486;
                  bool _out487;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out488;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out485, out _out486, out _out487, out _out488);
                  _911_recursiveGen = _out485;
                  _912_recOwned = _out486;
                  _913_recErased = _out487;
                  _914_recIdents = _out488;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _911_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _912_recOwned;
                  isErased = _913_recErased;
                  readIdents = _914_recIdents;
                }
              } else if (_source38.is_Primitive) {
                DAST._IPrimitive _915___mcc_h495 = _source38.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _916_recursiveGen;
                  bool _917_recOwned;
                  bool _918_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _919_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out489;
                  bool _out490;
                  bool _out491;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out489, out _out490, out _out491, out _out492);
                  _916_recursiveGen = _out489;
                  _917_recOwned = _out490;
                  _918_recErased = _out491;
                  _919_recIdents = _out492;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _916_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _917_recOwned;
                  isErased = _918_recErased;
                  readIdents = _919_recIdents;
                }
              } else if (_source38.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _920___mcc_h497 = _source38.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _921_recursiveGen;
                  bool _922_recOwned;
                  bool _923_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _924_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out493;
                  bool _out494;
                  bool _out495;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out493, out _out494, out _out495, out _out496);
                  _921_recursiveGen = _out493;
                  _922_recOwned = _out494;
                  _923_recErased = _out495;
                  _924_recIdents = _out496;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _921_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _922_recOwned;
                  isErased = _923_recErased;
                  readIdents = _924_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _925___mcc_h499 = _source38.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _926_recursiveGen;
                  bool _927_recOwned;
                  bool _928_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _929_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out497;
                  bool _out498;
                  bool _out499;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out497, out _out498, out _out499, out _out500);
                  _926_recursiveGen = _out497;
                  _927_recOwned = _out498;
                  _928_recErased = _out499;
                  _929_recIdents = _out500;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _926_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _927_recOwned;
                  isErased = _928_recErased;
                  readIdents = _929_recIdents;
                }
              }
            } else if (_source28.is_Array) {
              DAST._IType _930___mcc_h501 = _source28.dtor_element;
              DAST._IType _source40 = _510___mcc_h238;
              if (_source40.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _931___mcc_h505 = _source40.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _932___mcc_h506 = _source40.dtor_typeArgs;
                DAST._IResolvedType _933___mcc_h507 = _source40.dtor_resolved;
                DAST._IResolvedType _source41 = _933___mcc_h507;
                if (_source41.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _934___mcc_h511 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _935_recursiveGen;
                    bool _936_recOwned;
                    bool _937_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _938_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out501;
                    bool _out502;
                    bool _out503;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out501, out _out502, out _out503, out _out504);
                    _935_recursiveGen = _out501;
                    _936_recOwned = _out502;
                    _937_recErased = _out503;
                    _938_recIdents = _out504;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _935_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _936_recOwned;
                    isErased = _937_recErased;
                    readIdents = _938_recIdents;
                  }
                } else if (_source41.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _939___mcc_h513 = _source41.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _940_recursiveGen;
                    bool _941_recOwned;
                    bool _942_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _943_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out505;
                    bool _out506;
                    bool _out507;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out505, out _out506, out _out507, out _out508);
                    _940_recursiveGen = _out505;
                    _941_recOwned = _out506;
                    _942_recErased = _out507;
                    _943_recIdents = _out508;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _940_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _941_recOwned;
                    isErased = _942_recErased;
                    readIdents = _943_recIdents;
                  }
                } else {
                  DAST._IType _944___mcc_h515 = _source41.dtor_Newtype_a0;
                  DAST._IType _945_b = _944___mcc_h515;
                  {
                    if (object.Equals(_503_fromTpe, _945_b)) {
                      Dafny.ISequence<Dafny.Rune> _946_recursiveGen;
                      bool _947_recOwned;
                      bool _948_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _949_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out509;
                      bool _out510;
                      bool _out511;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out509, out _out510, out _out511, out _out512);
                      _946_recursiveGen = _out509;
                      _947_recOwned = _out510;
                      _948_recErased = _out511;
                      _949_recIdents = _out512;
                      Dafny.ISequence<Dafny.Rune> _950_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out513;
                      _out513 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _950_rhsType = _out513;
                      Dafny.ISequence<Dafny.Rune> _951_uneraseFn;
                      _951_uneraseFn = ((_947_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _950_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _951_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _946_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _947_recOwned;
                      isErased = false;
                      readIdents = _949_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out514;
                      bool _out515;
                      bool _out516;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _945_b), _945_b, _502_toTpe), selfIdent, @params, mustOwn, out _out514, out _out515, out _out516, out _out517);
                      s = _out514;
                      isOwned = _out515;
                      isErased = _out516;
                      readIdents = _out517;
                    }
                  }
                }
              } else if (_source40.is_Nullable) {
                DAST._IType _952___mcc_h517 = _source40.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _953_recursiveGen;
                  bool _954_recOwned;
                  bool _955_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _956_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out518;
                  bool _out519;
                  bool _out520;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out518, out _out519, out _out520, out _out521);
                  _953_recursiveGen = _out518;
                  _954_recOwned = _out519;
                  _955_recErased = _out520;
                  _956_recIdents = _out521;
                  if (!(_954_recOwned)) {
                    _953_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_953_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _953_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _955_recErased;
                  readIdents = _956_recIdents;
                }
              } else if (_source40.is_Tuple) {
                Dafny.ISequence<DAST._IType> _957___mcc_h519 = _source40.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _958_recursiveGen;
                  bool _959_recOwned;
                  bool _960_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _961_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out522;
                  bool _out523;
                  bool _out524;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out522, out _out523, out _out524, out _out525);
                  _958_recursiveGen = _out522;
                  _959_recOwned = _out523;
                  _960_recErased = _out524;
                  _961_recIdents = _out525;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _958_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _959_recOwned;
                  isErased = _960_recErased;
                  readIdents = _961_recIdents;
                }
              } else if (_source40.is_Array) {
                DAST._IType _962___mcc_h521 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _963_recursiveGen;
                  bool _964_recOwned;
                  bool _965_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _966_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out526;
                  bool _out527;
                  bool _out528;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out526, out _out527, out _out528, out _out529);
                  _963_recursiveGen = _out526;
                  _964_recOwned = _out527;
                  _965_recErased = _out528;
                  _966_recIdents = _out529;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _963_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _964_recOwned;
                  isErased = _965_recErased;
                  readIdents = _966_recIdents;
                }
              } else if (_source40.is_Seq) {
                DAST._IType _967___mcc_h523 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _968_recursiveGen;
                  bool _969_recOwned;
                  bool _970_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _971_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out530;
                  bool _out531;
                  bool _out532;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out530, out _out531, out _out532, out _out533);
                  _968_recursiveGen = _out530;
                  _969_recOwned = _out531;
                  _970_recErased = _out532;
                  _971_recIdents = _out533;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _968_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _969_recOwned;
                  isErased = _970_recErased;
                  readIdents = _971_recIdents;
                }
              } else if (_source40.is_Set) {
                DAST._IType _972___mcc_h525 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _973_recursiveGen;
                  bool _974_recOwned;
                  bool _975_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _976_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out534;
                  bool _out535;
                  bool _out536;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out537;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out534, out _out535, out _out536, out _out537);
                  _973_recursiveGen = _out534;
                  _974_recOwned = _out535;
                  _975_recErased = _out536;
                  _976_recIdents = _out537;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _973_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _974_recOwned;
                  isErased = _975_recErased;
                  readIdents = _976_recIdents;
                }
              } else if (_source40.is_Multiset) {
                DAST._IType _977___mcc_h527 = _source40.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _978_recursiveGen;
                  bool _979_recOwned;
                  bool _980_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _981_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out538;
                  bool _out539;
                  bool _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out538, out _out539, out _out540, out _out541);
                  _978_recursiveGen = _out538;
                  _979_recOwned = _out539;
                  _980_recErased = _out540;
                  _981_recIdents = _out541;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _978_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _979_recOwned;
                  isErased = _980_recErased;
                  readIdents = _981_recIdents;
                }
              } else if (_source40.is_Map) {
                DAST._IType _982___mcc_h529 = _source40.dtor_key;
                DAST._IType _983___mcc_h530 = _source40.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _984_recursiveGen;
                  bool _985_recOwned;
                  bool _986_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _987_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out542;
                  bool _out543;
                  bool _out544;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out542, out _out543, out _out544, out _out545);
                  _984_recursiveGen = _out542;
                  _985_recOwned = _out543;
                  _986_recErased = _out544;
                  _987_recIdents = _out545;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _984_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _985_recOwned;
                  isErased = _986_recErased;
                  readIdents = _987_recIdents;
                }
              } else if (_source40.is_Arrow) {
                Dafny.ISequence<DAST._IType> _988___mcc_h533 = _source40.dtor_args;
                DAST._IType _989___mcc_h534 = _source40.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _990_recursiveGen;
                  bool _991_recOwned;
                  bool _992_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _993_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out546;
                  bool _out547;
                  bool _out548;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out546, out _out547, out _out548, out _out549);
                  _990_recursiveGen = _out546;
                  _991_recOwned = _out547;
                  _992_recErased = _out548;
                  _993_recIdents = _out549;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _990_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _991_recOwned;
                  isErased = _992_recErased;
                  readIdents = _993_recIdents;
                }
              } else if (_source40.is_Primitive) {
                DAST._IPrimitive _994___mcc_h537 = _source40.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _995_recursiveGen;
                  bool _996_recOwned;
                  bool _997_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _998_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out550;
                  bool _out551;
                  bool _out552;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out550, out _out551, out _out552, out _out553);
                  _995_recursiveGen = _out550;
                  _996_recOwned = _out551;
                  _997_recErased = _out552;
                  _998_recIdents = _out553;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _995_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _996_recOwned;
                  isErased = _997_recErased;
                  readIdents = _998_recIdents;
                }
              } else if (_source40.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _999___mcc_h539 = _source40.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1000_recursiveGen;
                  bool _1001_recOwned;
                  bool _1002_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1003_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out554;
                  bool _out555;
                  bool _out556;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out554, out _out555, out _out556, out _out557);
                  _1000_recursiveGen = _out554;
                  _1001_recOwned = _out555;
                  _1002_recErased = _out556;
                  _1003_recIdents = _out557;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1000_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1001_recOwned;
                  isErased = _1002_recErased;
                  readIdents = _1003_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1004___mcc_h541 = _source40.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1005_recursiveGen;
                  bool _1006_recOwned;
                  bool _1007_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1008_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out558;
                  bool _out559;
                  bool _out560;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out561;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out558, out _out559, out _out560, out _out561);
                  _1005_recursiveGen = _out558;
                  _1006_recOwned = _out559;
                  _1007_recErased = _out560;
                  _1008_recIdents = _out561;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1005_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1006_recOwned;
                  isErased = _1007_recErased;
                  readIdents = _1008_recIdents;
                }
              }
            } else if (_source28.is_Seq) {
              DAST._IType _1009___mcc_h543 = _source28.dtor_element;
              DAST._IType _source42 = _510___mcc_h238;
              if (_source42.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1010___mcc_h547 = _source42.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1011___mcc_h548 = _source42.dtor_typeArgs;
                DAST._IResolvedType _1012___mcc_h549 = _source42.dtor_resolved;
                DAST._IResolvedType _source43 = _1012___mcc_h549;
                if (_source43.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1013___mcc_h553 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1014_recursiveGen;
                    bool _1015_recOwned;
                    bool _1016_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1017_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out562;
                    bool _out563;
                    bool _out564;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out562, out _out563, out _out564, out _out565);
                    _1014_recursiveGen = _out562;
                    _1015_recOwned = _out563;
                    _1016_recErased = _out564;
                    _1017_recIdents = _out565;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1014_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1015_recOwned;
                    isErased = _1016_recErased;
                    readIdents = _1017_recIdents;
                  }
                } else if (_source43.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1018___mcc_h555 = _source43.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1019_recursiveGen;
                    bool _1020_recOwned;
                    bool _1021_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1022_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out566;
                    bool _out567;
                    bool _out568;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out566, out _out567, out _out568, out _out569);
                    _1019_recursiveGen = _out566;
                    _1020_recOwned = _out567;
                    _1021_recErased = _out568;
                    _1022_recIdents = _out569;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1019_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1020_recOwned;
                    isErased = _1021_recErased;
                    readIdents = _1022_recIdents;
                  }
                } else {
                  DAST._IType _1023___mcc_h557 = _source43.dtor_Newtype_a0;
                  DAST._IType _1024_b = _1023___mcc_h557;
                  {
                    if (object.Equals(_503_fromTpe, _1024_b)) {
                      Dafny.ISequence<Dafny.Rune> _1025_recursiveGen;
                      bool _1026_recOwned;
                      bool _1027_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1028_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out570;
                      bool _out571;
                      bool _out572;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out573;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out570, out _out571, out _out572, out _out573);
                      _1025_recursiveGen = _out570;
                      _1026_recOwned = _out571;
                      _1027_recErased = _out572;
                      _1028_recIdents = _out573;
                      Dafny.ISequence<Dafny.Rune> _1029_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out574;
                      _out574 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1029_rhsType = _out574;
                      Dafny.ISequence<Dafny.Rune> _1030_uneraseFn;
                      _1030_uneraseFn = ((_1026_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1029_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1030_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1025_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1026_recOwned;
                      isErased = false;
                      readIdents = _1028_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out575;
                      bool _out576;
                      bool _out577;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1024_b), _1024_b, _502_toTpe), selfIdent, @params, mustOwn, out _out575, out _out576, out _out577, out _out578);
                      s = _out575;
                      isOwned = _out576;
                      isErased = _out577;
                      readIdents = _out578;
                    }
                  }
                }
              } else if (_source42.is_Nullable) {
                DAST._IType _1031___mcc_h559 = _source42.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1032_recursiveGen;
                  bool _1033_recOwned;
                  bool _1034_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1035_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out579;
                  bool _out580;
                  bool _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out579, out _out580, out _out581, out _out582);
                  _1032_recursiveGen = _out579;
                  _1033_recOwned = _out580;
                  _1034_recErased = _out581;
                  _1035_recIdents = _out582;
                  if (!(_1033_recOwned)) {
                    _1032_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1032_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1032_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1034_recErased;
                  readIdents = _1035_recIdents;
                }
              } else if (_source42.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1036___mcc_h561 = _source42.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1037_recursiveGen;
                  bool _1038_recOwned;
                  bool _1039_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1040_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out583;
                  bool _out584;
                  bool _out585;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out583, out _out584, out _out585, out _out586);
                  _1037_recursiveGen = _out583;
                  _1038_recOwned = _out584;
                  _1039_recErased = _out585;
                  _1040_recIdents = _out586;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1037_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1038_recOwned;
                  isErased = _1039_recErased;
                  readIdents = _1040_recIdents;
                }
              } else if (_source42.is_Array) {
                DAST._IType _1041___mcc_h563 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1042_recursiveGen;
                  bool _1043_recOwned;
                  bool _1044_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1045_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out587;
                  bool _out588;
                  bool _out589;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out587, out _out588, out _out589, out _out590);
                  _1042_recursiveGen = _out587;
                  _1043_recOwned = _out588;
                  _1044_recErased = _out589;
                  _1045_recIdents = _out590;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1042_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1043_recOwned;
                  isErased = _1044_recErased;
                  readIdents = _1045_recIdents;
                }
              } else if (_source42.is_Seq) {
                DAST._IType _1046___mcc_h565 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1047_recursiveGen;
                  bool _1048_recOwned;
                  bool _1049_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1050_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out591;
                  bool _out592;
                  bool _out593;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out591, out _out592, out _out593, out _out594);
                  _1047_recursiveGen = _out591;
                  _1048_recOwned = _out592;
                  _1049_recErased = _out593;
                  _1050_recIdents = _out594;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1047_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1048_recOwned;
                  isErased = _1049_recErased;
                  readIdents = _1050_recIdents;
                }
              } else if (_source42.is_Set) {
                DAST._IType _1051___mcc_h567 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1052_recursiveGen;
                  bool _1053_recOwned;
                  bool _1054_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1055_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out595;
                  bool _out596;
                  bool _out597;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out595, out _out596, out _out597, out _out598);
                  _1052_recursiveGen = _out595;
                  _1053_recOwned = _out596;
                  _1054_recErased = _out597;
                  _1055_recIdents = _out598;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1052_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1053_recOwned;
                  isErased = _1054_recErased;
                  readIdents = _1055_recIdents;
                }
              } else if (_source42.is_Multiset) {
                DAST._IType _1056___mcc_h569 = _source42.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1057_recursiveGen;
                  bool _1058_recOwned;
                  bool _1059_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1060_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out599;
                  bool _out600;
                  bool _out601;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out599, out _out600, out _out601, out _out602);
                  _1057_recursiveGen = _out599;
                  _1058_recOwned = _out600;
                  _1059_recErased = _out601;
                  _1060_recIdents = _out602;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1057_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1058_recOwned;
                  isErased = _1059_recErased;
                  readIdents = _1060_recIdents;
                }
              } else if (_source42.is_Map) {
                DAST._IType _1061___mcc_h571 = _source42.dtor_key;
                DAST._IType _1062___mcc_h572 = _source42.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1063_recursiveGen;
                  bool _1064_recOwned;
                  bool _1065_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1066_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out603;
                  bool _out604;
                  bool _out605;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out603, out _out604, out _out605, out _out606);
                  _1063_recursiveGen = _out603;
                  _1064_recOwned = _out604;
                  _1065_recErased = _out605;
                  _1066_recIdents = _out606;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1063_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1064_recOwned;
                  isErased = _1065_recErased;
                  readIdents = _1066_recIdents;
                }
              } else if (_source42.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1067___mcc_h575 = _source42.dtor_args;
                DAST._IType _1068___mcc_h576 = _source42.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1069_recursiveGen;
                  bool _1070_recOwned;
                  bool _1071_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1072_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out607;
                  bool _out608;
                  bool _out609;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out607, out _out608, out _out609, out _out610);
                  _1069_recursiveGen = _out607;
                  _1070_recOwned = _out608;
                  _1071_recErased = _out609;
                  _1072_recIdents = _out610;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1069_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1070_recOwned;
                  isErased = _1071_recErased;
                  readIdents = _1072_recIdents;
                }
              } else if (_source42.is_Primitive) {
                DAST._IPrimitive _1073___mcc_h579 = _source42.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1074_recursiveGen;
                  bool _1075_recOwned;
                  bool _1076_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1077_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out611;
                  bool _out612;
                  bool _out613;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out611, out _out612, out _out613, out _out614);
                  _1074_recursiveGen = _out611;
                  _1075_recOwned = _out612;
                  _1076_recErased = _out613;
                  _1077_recIdents = _out614;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1074_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1075_recOwned;
                  isErased = _1076_recErased;
                  readIdents = _1077_recIdents;
                }
              } else if (_source42.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1078___mcc_h581 = _source42.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1079_recursiveGen;
                  bool _1080_recOwned;
                  bool _1081_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1082_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out615;
                  bool _out616;
                  bool _out617;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out618;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out615, out _out616, out _out617, out _out618);
                  _1079_recursiveGen = _out615;
                  _1080_recOwned = _out616;
                  _1081_recErased = _out617;
                  _1082_recIdents = _out618;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1079_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1080_recOwned;
                  isErased = _1081_recErased;
                  readIdents = _1082_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1083___mcc_h583 = _source42.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1084_recursiveGen;
                  bool _1085_recOwned;
                  bool _1086_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1087_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out619;
                  bool _out620;
                  bool _out621;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out619, out _out620, out _out621, out _out622);
                  _1084_recursiveGen = _out619;
                  _1085_recOwned = _out620;
                  _1086_recErased = _out621;
                  _1087_recIdents = _out622;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1084_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1085_recOwned;
                  isErased = _1086_recErased;
                  readIdents = _1087_recIdents;
                }
              }
            } else if (_source28.is_Set) {
              DAST._IType _1088___mcc_h585 = _source28.dtor_element;
              DAST._IType _source44 = _510___mcc_h238;
              if (_source44.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1089___mcc_h589 = _source44.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1090___mcc_h590 = _source44.dtor_typeArgs;
                DAST._IResolvedType _1091___mcc_h591 = _source44.dtor_resolved;
                DAST._IResolvedType _source45 = _1091___mcc_h591;
                if (_source45.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1092___mcc_h595 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1093_recursiveGen;
                    bool _1094_recOwned;
                    bool _1095_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1096_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out623;
                    bool _out624;
                    bool _out625;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out626;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out623, out _out624, out _out625, out _out626);
                    _1093_recursiveGen = _out623;
                    _1094_recOwned = _out624;
                    _1095_recErased = _out625;
                    _1096_recIdents = _out626;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1093_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1094_recOwned;
                    isErased = _1095_recErased;
                    readIdents = _1096_recIdents;
                  }
                } else if (_source45.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1097___mcc_h597 = _source45.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1098_recursiveGen;
                    bool _1099_recOwned;
                    bool _1100_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1101_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out627;
                    bool _out628;
                    bool _out629;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out627, out _out628, out _out629, out _out630);
                    _1098_recursiveGen = _out627;
                    _1099_recOwned = _out628;
                    _1100_recErased = _out629;
                    _1101_recIdents = _out630;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1098_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1099_recOwned;
                    isErased = _1100_recErased;
                    readIdents = _1101_recIdents;
                  }
                } else {
                  DAST._IType _1102___mcc_h599 = _source45.dtor_Newtype_a0;
                  DAST._IType _1103_b = _1102___mcc_h599;
                  {
                    if (object.Equals(_503_fromTpe, _1103_b)) {
                      Dafny.ISequence<Dafny.Rune> _1104_recursiveGen;
                      bool _1105_recOwned;
                      bool _1106_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1107_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out631;
                      bool _out632;
                      bool _out633;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out631, out _out632, out _out633, out _out634);
                      _1104_recursiveGen = _out631;
                      _1105_recOwned = _out632;
                      _1106_recErased = _out633;
                      _1107_recIdents = _out634;
                      Dafny.ISequence<Dafny.Rune> _1108_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out635;
                      _out635 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1108_rhsType = _out635;
                      Dafny.ISequence<Dafny.Rune> _1109_uneraseFn;
                      _1109_uneraseFn = ((_1105_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1108_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1109_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1104_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1105_recOwned;
                      isErased = false;
                      readIdents = _1107_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out636;
                      bool _out637;
                      bool _out638;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1103_b), _1103_b, _502_toTpe), selfIdent, @params, mustOwn, out _out636, out _out637, out _out638, out _out639);
                      s = _out636;
                      isOwned = _out637;
                      isErased = _out638;
                      readIdents = _out639;
                    }
                  }
                }
              } else if (_source44.is_Nullable) {
                DAST._IType _1110___mcc_h601 = _source44.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1111_recursiveGen;
                  bool _1112_recOwned;
                  bool _1113_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1114_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out640;
                  bool _out641;
                  bool _out642;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out640, out _out641, out _out642, out _out643);
                  _1111_recursiveGen = _out640;
                  _1112_recOwned = _out641;
                  _1113_recErased = _out642;
                  _1114_recIdents = _out643;
                  if (!(_1112_recOwned)) {
                    _1111_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1111_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1111_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1113_recErased;
                  readIdents = _1114_recIdents;
                }
              } else if (_source44.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1115___mcc_h603 = _source44.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1116_recursiveGen;
                  bool _1117_recOwned;
                  bool _1118_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1119_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out644;
                  bool _out645;
                  bool _out646;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out644, out _out645, out _out646, out _out647);
                  _1116_recursiveGen = _out644;
                  _1117_recOwned = _out645;
                  _1118_recErased = _out646;
                  _1119_recIdents = _out647;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1116_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1117_recOwned;
                  isErased = _1118_recErased;
                  readIdents = _1119_recIdents;
                }
              } else if (_source44.is_Array) {
                DAST._IType _1120___mcc_h605 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1121_recursiveGen;
                  bool _1122_recOwned;
                  bool _1123_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1124_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out648;
                  bool _out649;
                  bool _out650;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out651;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out648, out _out649, out _out650, out _out651);
                  _1121_recursiveGen = _out648;
                  _1122_recOwned = _out649;
                  _1123_recErased = _out650;
                  _1124_recIdents = _out651;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1121_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1122_recOwned;
                  isErased = _1123_recErased;
                  readIdents = _1124_recIdents;
                }
              } else if (_source44.is_Seq) {
                DAST._IType _1125___mcc_h607 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1126_recursiveGen;
                  bool _1127_recOwned;
                  bool _1128_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1129_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out652;
                  bool _out653;
                  bool _out654;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out652, out _out653, out _out654, out _out655);
                  _1126_recursiveGen = _out652;
                  _1127_recOwned = _out653;
                  _1128_recErased = _out654;
                  _1129_recIdents = _out655;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1126_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1127_recOwned;
                  isErased = _1128_recErased;
                  readIdents = _1129_recIdents;
                }
              } else if (_source44.is_Set) {
                DAST._IType _1130___mcc_h609 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1131_recursiveGen;
                  bool _1132_recOwned;
                  bool _1133_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1134_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out656;
                  bool _out657;
                  bool _out658;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out659;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out656, out _out657, out _out658, out _out659);
                  _1131_recursiveGen = _out656;
                  _1132_recOwned = _out657;
                  _1133_recErased = _out658;
                  _1134_recIdents = _out659;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1131_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1132_recOwned;
                  isErased = _1133_recErased;
                  readIdents = _1134_recIdents;
                }
              } else if (_source44.is_Multiset) {
                DAST._IType _1135___mcc_h611 = _source44.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1136_recursiveGen;
                  bool _1137_recOwned;
                  bool _1138_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1139_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out660;
                  bool _out661;
                  bool _out662;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out660, out _out661, out _out662, out _out663);
                  _1136_recursiveGen = _out660;
                  _1137_recOwned = _out661;
                  _1138_recErased = _out662;
                  _1139_recIdents = _out663;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1136_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1137_recOwned;
                  isErased = _1138_recErased;
                  readIdents = _1139_recIdents;
                }
              } else if (_source44.is_Map) {
                DAST._IType _1140___mcc_h613 = _source44.dtor_key;
                DAST._IType _1141___mcc_h614 = _source44.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1142_recursiveGen;
                  bool _1143_recOwned;
                  bool _1144_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1145_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out664;
                  bool _out665;
                  bool _out666;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out664, out _out665, out _out666, out _out667);
                  _1142_recursiveGen = _out664;
                  _1143_recOwned = _out665;
                  _1144_recErased = _out666;
                  _1145_recIdents = _out667;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1142_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1143_recOwned;
                  isErased = _1144_recErased;
                  readIdents = _1145_recIdents;
                }
              } else if (_source44.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1146___mcc_h617 = _source44.dtor_args;
                DAST._IType _1147___mcc_h618 = _source44.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1148_recursiveGen;
                  bool _1149_recOwned;
                  bool _1150_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1151_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out668;
                  bool _out669;
                  bool _out670;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out671;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out668, out _out669, out _out670, out _out671);
                  _1148_recursiveGen = _out668;
                  _1149_recOwned = _out669;
                  _1150_recErased = _out670;
                  _1151_recIdents = _out671;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1148_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1149_recOwned;
                  isErased = _1150_recErased;
                  readIdents = _1151_recIdents;
                }
              } else if (_source44.is_Primitive) {
                DAST._IPrimitive _1152___mcc_h621 = _source44.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1153_recursiveGen;
                  bool _1154_recOwned;
                  bool _1155_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1156_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out672;
                  bool _out673;
                  bool _out674;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out675;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out672, out _out673, out _out674, out _out675);
                  _1153_recursiveGen = _out672;
                  _1154_recOwned = _out673;
                  _1155_recErased = _out674;
                  _1156_recIdents = _out675;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1153_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1154_recOwned;
                  isErased = _1155_recErased;
                  readIdents = _1156_recIdents;
                }
              } else if (_source44.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1157___mcc_h623 = _source44.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1158_recursiveGen;
                  bool _1159_recOwned;
                  bool _1160_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1161_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out676;
                  bool _out677;
                  bool _out678;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out676, out _out677, out _out678, out _out679);
                  _1158_recursiveGen = _out676;
                  _1159_recOwned = _out677;
                  _1160_recErased = _out678;
                  _1161_recIdents = _out679;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1158_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1159_recOwned;
                  isErased = _1160_recErased;
                  readIdents = _1161_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1162___mcc_h625 = _source44.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1163_recursiveGen;
                  bool _1164_recOwned;
                  bool _1165_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1166_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out680;
                  bool _out681;
                  bool _out682;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out683;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out680, out _out681, out _out682, out _out683);
                  _1163_recursiveGen = _out680;
                  _1164_recOwned = _out681;
                  _1165_recErased = _out682;
                  _1166_recIdents = _out683;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1163_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1164_recOwned;
                  isErased = _1165_recErased;
                  readIdents = _1166_recIdents;
                }
              }
            } else if (_source28.is_Multiset) {
              DAST._IType _1167___mcc_h627 = _source28.dtor_element;
              DAST._IType _source46 = _510___mcc_h238;
              if (_source46.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1168___mcc_h631 = _source46.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1169___mcc_h632 = _source46.dtor_typeArgs;
                DAST._IResolvedType _1170___mcc_h633 = _source46.dtor_resolved;
                DAST._IResolvedType _source47 = _1170___mcc_h633;
                if (_source47.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1171___mcc_h637 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1172_recursiveGen;
                    bool _1173_recOwned;
                    bool _1174_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1175_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out684;
                    bool _out685;
                    bool _out686;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out687;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out684, out _out685, out _out686, out _out687);
                    _1172_recursiveGen = _out684;
                    _1173_recOwned = _out685;
                    _1174_recErased = _out686;
                    _1175_recIdents = _out687;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1172_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1173_recOwned;
                    isErased = _1174_recErased;
                    readIdents = _1175_recIdents;
                  }
                } else if (_source47.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1176___mcc_h639 = _source47.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1177_recursiveGen;
                    bool _1178_recOwned;
                    bool _1179_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1180_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out688;
                    bool _out689;
                    bool _out690;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out688, out _out689, out _out690, out _out691);
                    _1177_recursiveGen = _out688;
                    _1178_recOwned = _out689;
                    _1179_recErased = _out690;
                    _1180_recIdents = _out691;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1177_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1178_recOwned;
                    isErased = _1179_recErased;
                    readIdents = _1180_recIdents;
                  }
                } else {
                  DAST._IType _1181___mcc_h641 = _source47.dtor_Newtype_a0;
                  DAST._IType _1182_b = _1181___mcc_h641;
                  {
                    if (object.Equals(_503_fromTpe, _1182_b)) {
                      Dafny.ISequence<Dafny.Rune> _1183_recursiveGen;
                      bool _1184_recOwned;
                      bool _1185_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1186_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out692;
                      bool _out693;
                      bool _out694;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out695;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out692, out _out693, out _out694, out _out695);
                      _1183_recursiveGen = _out692;
                      _1184_recOwned = _out693;
                      _1185_recErased = _out694;
                      _1186_recIdents = _out695;
                      Dafny.ISequence<Dafny.Rune> _1187_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out696;
                      _out696 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1187_rhsType = _out696;
                      Dafny.ISequence<Dafny.Rune> _1188_uneraseFn;
                      _1188_uneraseFn = ((_1184_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1187_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1188_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1183_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1184_recOwned;
                      isErased = false;
                      readIdents = _1186_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out697;
                      bool _out698;
                      bool _out699;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1182_b), _1182_b, _502_toTpe), selfIdent, @params, mustOwn, out _out697, out _out698, out _out699, out _out700);
                      s = _out697;
                      isOwned = _out698;
                      isErased = _out699;
                      readIdents = _out700;
                    }
                  }
                }
              } else if (_source46.is_Nullable) {
                DAST._IType _1189___mcc_h643 = _source46.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1190_recursiveGen;
                  bool _1191_recOwned;
                  bool _1192_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1193_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out701;
                  bool _out702;
                  bool _out703;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out704;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out701, out _out702, out _out703, out _out704);
                  _1190_recursiveGen = _out701;
                  _1191_recOwned = _out702;
                  _1192_recErased = _out703;
                  _1193_recIdents = _out704;
                  if (!(_1191_recOwned)) {
                    _1190_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1190_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1190_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1192_recErased;
                  readIdents = _1193_recIdents;
                }
              } else if (_source46.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1194___mcc_h645 = _source46.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1195_recursiveGen;
                  bool _1196_recOwned;
                  bool _1197_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1198_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out705;
                  bool _out706;
                  bool _out707;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out708;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out705, out _out706, out _out707, out _out708);
                  _1195_recursiveGen = _out705;
                  _1196_recOwned = _out706;
                  _1197_recErased = _out707;
                  _1198_recIdents = _out708;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1195_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1196_recOwned;
                  isErased = _1197_recErased;
                  readIdents = _1198_recIdents;
                }
              } else if (_source46.is_Array) {
                DAST._IType _1199___mcc_h647 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1200_recursiveGen;
                  bool _1201_recOwned;
                  bool _1202_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1203_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out709;
                  bool _out710;
                  bool _out711;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out709, out _out710, out _out711, out _out712);
                  _1200_recursiveGen = _out709;
                  _1201_recOwned = _out710;
                  _1202_recErased = _out711;
                  _1203_recIdents = _out712;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1200_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1201_recOwned;
                  isErased = _1202_recErased;
                  readIdents = _1203_recIdents;
                }
              } else if (_source46.is_Seq) {
                DAST._IType _1204___mcc_h649 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1205_recursiveGen;
                  bool _1206_recOwned;
                  bool _1207_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1208_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out713;
                  bool _out714;
                  bool _out715;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out716;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out713, out _out714, out _out715, out _out716);
                  _1205_recursiveGen = _out713;
                  _1206_recOwned = _out714;
                  _1207_recErased = _out715;
                  _1208_recIdents = _out716;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1205_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1206_recOwned;
                  isErased = _1207_recErased;
                  readIdents = _1208_recIdents;
                }
              } else if (_source46.is_Set) {
                DAST._IType _1209___mcc_h651 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1210_recursiveGen;
                  bool _1211_recOwned;
                  bool _1212_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1213_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out717;
                  bool _out718;
                  bool _out719;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out720;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out717, out _out718, out _out719, out _out720);
                  _1210_recursiveGen = _out717;
                  _1211_recOwned = _out718;
                  _1212_recErased = _out719;
                  _1213_recIdents = _out720;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1210_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1211_recOwned;
                  isErased = _1212_recErased;
                  readIdents = _1213_recIdents;
                }
              } else if (_source46.is_Multiset) {
                DAST._IType _1214___mcc_h653 = _source46.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1215_recursiveGen;
                  bool _1216_recOwned;
                  bool _1217_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1218_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out721;
                  bool _out722;
                  bool _out723;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out721, out _out722, out _out723, out _out724);
                  _1215_recursiveGen = _out721;
                  _1216_recOwned = _out722;
                  _1217_recErased = _out723;
                  _1218_recIdents = _out724;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1215_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1216_recOwned;
                  isErased = _1217_recErased;
                  readIdents = _1218_recIdents;
                }
              } else if (_source46.is_Map) {
                DAST._IType _1219___mcc_h655 = _source46.dtor_key;
                DAST._IType _1220___mcc_h656 = _source46.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1221_recursiveGen;
                  bool _1222_recOwned;
                  bool _1223_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1224_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out725;
                  bool _out726;
                  bool _out727;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out728;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out725, out _out726, out _out727, out _out728);
                  _1221_recursiveGen = _out725;
                  _1222_recOwned = _out726;
                  _1223_recErased = _out727;
                  _1224_recIdents = _out728;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1221_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1222_recOwned;
                  isErased = _1223_recErased;
                  readIdents = _1224_recIdents;
                }
              } else if (_source46.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1225___mcc_h659 = _source46.dtor_args;
                DAST._IType _1226___mcc_h660 = _source46.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1227_recursiveGen;
                  bool _1228_recOwned;
                  bool _1229_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1230_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out729;
                  bool _out730;
                  bool _out731;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out732;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out729, out _out730, out _out731, out _out732);
                  _1227_recursiveGen = _out729;
                  _1228_recOwned = _out730;
                  _1229_recErased = _out731;
                  _1230_recIdents = _out732;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1227_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1228_recOwned;
                  isErased = _1229_recErased;
                  readIdents = _1230_recIdents;
                }
              } else if (_source46.is_Primitive) {
                DAST._IPrimitive _1231___mcc_h663 = _source46.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1232_recursiveGen;
                  bool _1233_recOwned;
                  bool _1234_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1235_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out733;
                  bool _out734;
                  bool _out735;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out733, out _out734, out _out735, out _out736);
                  _1232_recursiveGen = _out733;
                  _1233_recOwned = _out734;
                  _1234_recErased = _out735;
                  _1235_recIdents = _out736;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1232_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1233_recOwned;
                  isErased = _1234_recErased;
                  readIdents = _1235_recIdents;
                }
              } else if (_source46.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1236___mcc_h665 = _source46.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1237_recursiveGen;
                  bool _1238_recOwned;
                  bool _1239_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1240_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out737;
                  bool _out738;
                  bool _out739;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out740;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out737, out _out738, out _out739, out _out740);
                  _1237_recursiveGen = _out737;
                  _1238_recOwned = _out738;
                  _1239_recErased = _out739;
                  _1240_recIdents = _out740;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1237_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1238_recOwned;
                  isErased = _1239_recErased;
                  readIdents = _1240_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1241___mcc_h667 = _source46.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1242_recursiveGen;
                  bool _1243_recOwned;
                  bool _1244_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1245_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out741;
                  bool _out742;
                  bool _out743;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out744;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out741, out _out742, out _out743, out _out744);
                  _1242_recursiveGen = _out741;
                  _1243_recOwned = _out742;
                  _1244_recErased = _out743;
                  _1245_recIdents = _out744;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1242_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1243_recOwned;
                  isErased = _1244_recErased;
                  readIdents = _1245_recIdents;
                }
              }
            } else if (_source28.is_Map) {
              DAST._IType _1246___mcc_h669 = _source28.dtor_key;
              DAST._IType _1247___mcc_h670 = _source28.dtor_value;
              DAST._IType _source48 = _510___mcc_h238;
              if (_source48.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1248___mcc_h677 = _source48.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1249___mcc_h678 = _source48.dtor_typeArgs;
                DAST._IResolvedType _1250___mcc_h679 = _source48.dtor_resolved;
                DAST._IResolvedType _source49 = _1250___mcc_h679;
                if (_source49.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1251___mcc_h683 = _source49.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1252_recursiveGen;
                    bool _1253_recOwned;
                    bool _1254_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1255_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out745;
                    bool _out746;
                    bool _out747;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out745, out _out746, out _out747, out _out748);
                    _1252_recursiveGen = _out745;
                    _1253_recOwned = _out746;
                    _1254_recErased = _out747;
                    _1255_recIdents = _out748;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1252_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1253_recOwned;
                    isErased = _1254_recErased;
                    readIdents = _1255_recIdents;
                  }
                } else if (_source49.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1256___mcc_h685 = _source49.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1257_recursiveGen;
                    bool _1258_recOwned;
                    bool _1259_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1260_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out749;
                    bool _out750;
                    bool _out751;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out752;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out749, out _out750, out _out751, out _out752);
                    _1257_recursiveGen = _out749;
                    _1258_recOwned = _out750;
                    _1259_recErased = _out751;
                    _1260_recIdents = _out752;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1257_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1258_recOwned;
                    isErased = _1259_recErased;
                    readIdents = _1260_recIdents;
                  }
                } else {
                  DAST._IType _1261___mcc_h687 = _source49.dtor_Newtype_a0;
                  DAST._IType _1262_b = _1261___mcc_h687;
                  {
                    if (object.Equals(_503_fromTpe, _1262_b)) {
                      Dafny.ISequence<Dafny.Rune> _1263_recursiveGen;
                      bool _1264_recOwned;
                      bool _1265_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1266_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out753;
                      bool _out754;
                      bool _out755;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out756;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out753, out _out754, out _out755, out _out756);
                      _1263_recursiveGen = _out753;
                      _1264_recOwned = _out754;
                      _1265_recErased = _out755;
                      _1266_recIdents = _out756;
                      Dafny.ISequence<Dafny.Rune> _1267_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out757;
                      _out757 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1267_rhsType = _out757;
                      Dafny.ISequence<Dafny.Rune> _1268_uneraseFn;
                      _1268_uneraseFn = ((_1264_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1267_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1268_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1263_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1264_recOwned;
                      isErased = false;
                      readIdents = _1266_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out758;
                      bool _out759;
                      bool _out760;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out761;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1262_b), _1262_b, _502_toTpe), selfIdent, @params, mustOwn, out _out758, out _out759, out _out760, out _out761);
                      s = _out758;
                      isOwned = _out759;
                      isErased = _out760;
                      readIdents = _out761;
                    }
                  }
                }
              } else if (_source48.is_Nullable) {
                DAST._IType _1269___mcc_h689 = _source48.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1270_recursiveGen;
                  bool _1271_recOwned;
                  bool _1272_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1273_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out762;
                  bool _out763;
                  bool _out764;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out762, out _out763, out _out764, out _out765);
                  _1270_recursiveGen = _out762;
                  _1271_recOwned = _out763;
                  _1272_recErased = _out764;
                  _1273_recIdents = _out765;
                  if (!(_1271_recOwned)) {
                    _1270_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1270_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1270_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1272_recErased;
                  readIdents = _1273_recIdents;
                }
              } else if (_source48.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1274___mcc_h691 = _source48.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1275_recursiveGen;
                  bool _1276_recOwned;
                  bool _1277_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1278_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out766;
                  bool _out767;
                  bool _out768;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out766, out _out767, out _out768, out _out769);
                  _1275_recursiveGen = _out766;
                  _1276_recOwned = _out767;
                  _1277_recErased = _out768;
                  _1278_recIdents = _out769;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1275_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1276_recOwned;
                  isErased = _1277_recErased;
                  readIdents = _1278_recIdents;
                }
              } else if (_source48.is_Array) {
                DAST._IType _1279___mcc_h693 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1280_recursiveGen;
                  bool _1281_recOwned;
                  bool _1282_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1283_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out770;
                  bool _out771;
                  bool _out772;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out773;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out770, out _out771, out _out772, out _out773);
                  _1280_recursiveGen = _out770;
                  _1281_recOwned = _out771;
                  _1282_recErased = _out772;
                  _1283_recIdents = _out773;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1280_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1281_recOwned;
                  isErased = _1282_recErased;
                  readIdents = _1283_recIdents;
                }
              } else if (_source48.is_Seq) {
                DAST._IType _1284___mcc_h695 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1285_recursiveGen;
                  bool _1286_recOwned;
                  bool _1287_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1288_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out774;
                  bool _out775;
                  bool _out776;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out777;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out774, out _out775, out _out776, out _out777);
                  _1285_recursiveGen = _out774;
                  _1286_recOwned = _out775;
                  _1287_recErased = _out776;
                  _1288_recIdents = _out777;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1285_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1286_recOwned;
                  isErased = _1287_recErased;
                  readIdents = _1288_recIdents;
                }
              } else if (_source48.is_Set) {
                DAST._IType _1289___mcc_h697 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1290_recursiveGen;
                  bool _1291_recOwned;
                  bool _1292_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1293_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out778;
                  bool _out779;
                  bool _out780;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out778, out _out779, out _out780, out _out781);
                  _1290_recursiveGen = _out778;
                  _1291_recOwned = _out779;
                  _1292_recErased = _out780;
                  _1293_recIdents = _out781;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1290_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1291_recOwned;
                  isErased = _1292_recErased;
                  readIdents = _1293_recIdents;
                }
              } else if (_source48.is_Multiset) {
                DAST._IType _1294___mcc_h699 = _source48.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1295_recursiveGen;
                  bool _1296_recOwned;
                  bool _1297_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1298_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out782;
                  bool _out783;
                  bool _out784;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out785;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out782, out _out783, out _out784, out _out785);
                  _1295_recursiveGen = _out782;
                  _1296_recOwned = _out783;
                  _1297_recErased = _out784;
                  _1298_recIdents = _out785;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1295_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1296_recOwned;
                  isErased = _1297_recErased;
                  readIdents = _1298_recIdents;
                }
              } else if (_source48.is_Map) {
                DAST._IType _1299___mcc_h701 = _source48.dtor_key;
                DAST._IType _1300___mcc_h702 = _source48.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1301_recursiveGen;
                  bool _1302_recOwned;
                  bool _1303_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1304_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out786;
                  bool _out787;
                  bool _out788;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out789;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out786, out _out787, out _out788, out _out789);
                  _1301_recursiveGen = _out786;
                  _1302_recOwned = _out787;
                  _1303_recErased = _out788;
                  _1304_recIdents = _out789;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1301_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1302_recOwned;
                  isErased = _1303_recErased;
                  readIdents = _1304_recIdents;
                }
              } else if (_source48.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1305___mcc_h705 = _source48.dtor_args;
                DAST._IType _1306___mcc_h706 = _source48.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1307_recursiveGen;
                  bool _1308_recOwned;
                  bool _1309_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1310_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out790;
                  bool _out791;
                  bool _out792;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out790, out _out791, out _out792, out _out793);
                  _1307_recursiveGen = _out790;
                  _1308_recOwned = _out791;
                  _1309_recErased = _out792;
                  _1310_recIdents = _out793;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1307_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1308_recOwned;
                  isErased = _1309_recErased;
                  readIdents = _1310_recIdents;
                }
              } else if (_source48.is_Primitive) {
                DAST._IPrimitive _1311___mcc_h709 = _source48.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1312_recursiveGen;
                  bool _1313_recOwned;
                  bool _1314_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1315_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out794;
                  bool _out795;
                  bool _out796;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out797;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out794, out _out795, out _out796, out _out797);
                  _1312_recursiveGen = _out794;
                  _1313_recOwned = _out795;
                  _1314_recErased = _out796;
                  _1315_recIdents = _out797;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1312_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1313_recOwned;
                  isErased = _1314_recErased;
                  readIdents = _1315_recIdents;
                }
              } else if (_source48.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1316___mcc_h711 = _source48.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1317_recursiveGen;
                  bool _1318_recOwned;
                  bool _1319_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1320_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out798;
                  bool _out799;
                  bool _out800;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out801;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out798, out _out799, out _out800, out _out801);
                  _1317_recursiveGen = _out798;
                  _1318_recOwned = _out799;
                  _1319_recErased = _out800;
                  _1320_recIdents = _out801;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1317_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1318_recOwned;
                  isErased = _1319_recErased;
                  readIdents = _1320_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1321___mcc_h713 = _source48.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1322_recursiveGen;
                  bool _1323_recOwned;
                  bool _1324_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1325_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out802;
                  bool _out803;
                  bool _out804;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out802, out _out803, out _out804, out _out805);
                  _1322_recursiveGen = _out802;
                  _1323_recOwned = _out803;
                  _1324_recErased = _out804;
                  _1325_recIdents = _out805;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1322_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1323_recOwned;
                  isErased = _1324_recErased;
                  readIdents = _1325_recIdents;
                }
              }
            } else if (_source28.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1326___mcc_h715 = _source28.dtor_args;
              DAST._IType _1327___mcc_h716 = _source28.dtor_result;
              DAST._IType _source50 = _510___mcc_h238;
              if (_source50.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1328___mcc_h723 = _source50.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1329___mcc_h724 = _source50.dtor_typeArgs;
                DAST._IResolvedType _1330___mcc_h725 = _source50.dtor_resolved;
                DAST._IResolvedType _source51 = _1330___mcc_h725;
                if (_source51.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1331___mcc_h729 = _source51.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1332_recursiveGen;
                    bool _1333_recOwned;
                    bool _1334_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1335_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out806;
                    bool _out807;
                    bool _out808;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out809;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out806, out _out807, out _out808, out _out809);
                    _1332_recursiveGen = _out806;
                    _1333_recOwned = _out807;
                    _1334_recErased = _out808;
                    _1335_recIdents = _out809;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1332_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1333_recOwned;
                    isErased = _1334_recErased;
                    readIdents = _1335_recIdents;
                  }
                } else if (_source51.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1336___mcc_h731 = _source51.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1337_recursiveGen;
                    bool _1338_recOwned;
                    bool _1339_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1340_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out810;
                    bool _out811;
                    bool _out812;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out813;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out810, out _out811, out _out812, out _out813);
                    _1337_recursiveGen = _out810;
                    _1338_recOwned = _out811;
                    _1339_recErased = _out812;
                    _1340_recIdents = _out813;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1337_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1338_recOwned;
                    isErased = _1339_recErased;
                    readIdents = _1340_recIdents;
                  }
                } else {
                  DAST._IType _1341___mcc_h733 = _source51.dtor_Newtype_a0;
                  DAST._IType _1342_b = _1341___mcc_h733;
                  {
                    if (object.Equals(_503_fromTpe, _1342_b)) {
                      Dafny.ISequence<Dafny.Rune> _1343_recursiveGen;
                      bool _1344_recOwned;
                      bool _1345_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1346_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out814;
                      bool _out815;
                      bool _out816;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out814, out _out815, out _out816, out _out817);
                      _1343_recursiveGen = _out814;
                      _1344_recOwned = _out815;
                      _1345_recErased = _out816;
                      _1346_recIdents = _out817;
                      Dafny.ISequence<Dafny.Rune> _1347_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out818;
                      _out818 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1347_rhsType = _out818;
                      Dafny.ISequence<Dafny.Rune> _1348_uneraseFn;
                      _1348_uneraseFn = ((_1344_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1347_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1348_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1343_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1344_recOwned;
                      isErased = false;
                      readIdents = _1346_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out819;
                      bool _out820;
                      bool _out821;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out822;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1342_b), _1342_b, _502_toTpe), selfIdent, @params, mustOwn, out _out819, out _out820, out _out821, out _out822);
                      s = _out819;
                      isOwned = _out820;
                      isErased = _out821;
                      readIdents = _out822;
                    }
                  }
                }
              } else if (_source50.is_Nullable) {
                DAST._IType _1349___mcc_h735 = _source50.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1350_recursiveGen;
                  bool _1351_recOwned;
                  bool _1352_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1353_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out823;
                  bool _out824;
                  bool _out825;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out823, out _out824, out _out825, out _out826);
                  _1350_recursiveGen = _out823;
                  _1351_recOwned = _out824;
                  _1352_recErased = _out825;
                  _1353_recIdents = _out826;
                  if (!(_1351_recOwned)) {
                    _1350_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1350_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1350_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1352_recErased;
                  readIdents = _1353_recIdents;
                }
              } else if (_source50.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1354___mcc_h737 = _source50.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1355_recursiveGen;
                  bool _1356_recOwned;
                  bool _1357_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1358_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out827;
                  bool _out828;
                  bool _out829;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out830;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out827, out _out828, out _out829, out _out830);
                  _1355_recursiveGen = _out827;
                  _1356_recOwned = _out828;
                  _1357_recErased = _out829;
                  _1358_recIdents = _out830;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1355_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1356_recOwned;
                  isErased = _1357_recErased;
                  readIdents = _1358_recIdents;
                }
              } else if (_source50.is_Array) {
                DAST._IType _1359___mcc_h739 = _source50.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1360_recursiveGen;
                  bool _1361_recOwned;
                  bool _1362_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1363_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out831;
                  bool _out832;
                  bool _out833;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out834;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out831, out _out832, out _out833, out _out834);
                  _1360_recursiveGen = _out831;
                  _1361_recOwned = _out832;
                  _1362_recErased = _out833;
                  _1363_recIdents = _out834;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1360_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1361_recOwned;
                  isErased = _1362_recErased;
                  readIdents = _1363_recIdents;
                }
              } else if (_source50.is_Seq) {
                DAST._IType _1364___mcc_h741 = _source50.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1365_recursiveGen;
                  bool _1366_recOwned;
                  bool _1367_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1368_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out835;
                  bool _out836;
                  bool _out837;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out835, out _out836, out _out837, out _out838);
                  _1365_recursiveGen = _out835;
                  _1366_recOwned = _out836;
                  _1367_recErased = _out837;
                  _1368_recIdents = _out838;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1365_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1366_recOwned;
                  isErased = _1367_recErased;
                  readIdents = _1368_recIdents;
                }
              } else if (_source50.is_Set) {
                DAST._IType _1369___mcc_h743 = _source50.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1370_recursiveGen;
                  bool _1371_recOwned;
                  bool _1372_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1373_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out839;
                  bool _out840;
                  bool _out841;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out842;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out839, out _out840, out _out841, out _out842);
                  _1370_recursiveGen = _out839;
                  _1371_recOwned = _out840;
                  _1372_recErased = _out841;
                  _1373_recIdents = _out842;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1370_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1371_recOwned;
                  isErased = _1372_recErased;
                  readIdents = _1373_recIdents;
                }
              } else if (_source50.is_Multiset) {
                DAST._IType _1374___mcc_h745 = _source50.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1375_recursiveGen;
                  bool _1376_recOwned;
                  bool _1377_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1378_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out843;
                  bool _out844;
                  bool _out845;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out846;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out843, out _out844, out _out845, out _out846);
                  _1375_recursiveGen = _out843;
                  _1376_recOwned = _out844;
                  _1377_recErased = _out845;
                  _1378_recIdents = _out846;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1375_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1376_recOwned;
                  isErased = _1377_recErased;
                  readIdents = _1378_recIdents;
                }
              } else if (_source50.is_Map) {
                DAST._IType _1379___mcc_h747 = _source50.dtor_key;
                DAST._IType _1380___mcc_h748 = _source50.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1381_recursiveGen;
                  bool _1382_recOwned;
                  bool _1383_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1384_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out847;
                  bool _out848;
                  bool _out849;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out847, out _out848, out _out849, out _out850);
                  _1381_recursiveGen = _out847;
                  _1382_recOwned = _out848;
                  _1383_recErased = _out849;
                  _1384_recIdents = _out850;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1381_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1382_recOwned;
                  isErased = _1383_recErased;
                  readIdents = _1384_recIdents;
                }
              } else if (_source50.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1385___mcc_h751 = _source50.dtor_args;
                DAST._IType _1386___mcc_h752 = _source50.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1387_recursiveGen;
                  bool _1388_recOwned;
                  bool _1389_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1390_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out851;
                  bool _out852;
                  bool _out853;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out854;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out851, out _out852, out _out853, out _out854);
                  _1387_recursiveGen = _out851;
                  _1388_recOwned = _out852;
                  _1389_recErased = _out853;
                  _1390_recIdents = _out854;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1387_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1388_recOwned;
                  isErased = _1389_recErased;
                  readIdents = _1390_recIdents;
                }
              } else if (_source50.is_Primitive) {
                DAST._IPrimitive _1391___mcc_h755 = _source50.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1392_recursiveGen;
                  bool _1393_recOwned;
                  bool _1394_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1395_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out855;
                  bool _out856;
                  bool _out857;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out858;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out855, out _out856, out _out857, out _out858);
                  _1392_recursiveGen = _out855;
                  _1393_recOwned = _out856;
                  _1394_recErased = _out857;
                  _1395_recIdents = _out858;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1392_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1393_recOwned;
                  isErased = _1394_recErased;
                  readIdents = _1395_recIdents;
                }
              } else if (_source50.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1396___mcc_h757 = _source50.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1397_recursiveGen;
                  bool _1398_recOwned;
                  bool _1399_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1400_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out859;
                  bool _out860;
                  bool _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out859, out _out860, out _out861, out _out862);
                  _1397_recursiveGen = _out859;
                  _1398_recOwned = _out860;
                  _1399_recErased = _out861;
                  _1400_recIdents = _out862;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1397_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1398_recOwned;
                  isErased = _1399_recErased;
                  readIdents = _1400_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1401___mcc_h759 = _source50.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1402_recursiveGen;
                  bool _1403_recOwned;
                  bool _1404_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1405_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out863;
                  bool _out864;
                  bool _out865;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out866;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out863, out _out864, out _out865, out _out866);
                  _1402_recursiveGen = _out863;
                  _1403_recOwned = _out864;
                  _1404_recErased = _out865;
                  _1405_recIdents = _out866;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1402_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1403_recOwned;
                  isErased = _1404_recErased;
                  readIdents = _1405_recIdents;
                }
              }
            } else if (_source28.is_Primitive) {
              DAST._IPrimitive _1406___mcc_h761 = _source28.dtor_Primitive_a0;
              DAST._IPrimitive _source52 = _1406___mcc_h761;
              if (_source52.is_Int) {
                DAST._IType _source53 = _510___mcc_h238;
                if (_source53.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1407___mcc_h765 = _source53.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1408___mcc_h766 = _source53.dtor_typeArgs;
                  DAST._IResolvedType _1409___mcc_h767 = _source53.dtor_resolved;
                  DAST._IResolvedType _source54 = _1409___mcc_h767;
                  if (_source54.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1410___mcc_h771 = _source54.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1411_recursiveGen;
                      bool _1412_recOwned;
                      bool _1413_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1414_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out867;
                      bool _out868;
                      bool _out869;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out870;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out867, out _out868, out _out869, out _out870);
                      _1411_recursiveGen = _out867;
                      _1412_recOwned = _out868;
                      _1413_recErased = _out869;
                      _1414_recIdents = _out870;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1411_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1412_recOwned;
                      isErased = _1413_recErased;
                      readIdents = _1414_recIdents;
                    }
                  } else if (_source54.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1415___mcc_h773 = _source54.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1416_recursiveGen;
                      bool _1417_recOwned;
                      bool _1418_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1419_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out871;
                      bool _out872;
                      bool _out873;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out871, out _out872, out _out873, out _out874);
                      _1416_recursiveGen = _out871;
                      _1417_recOwned = _out872;
                      _1418_recErased = _out873;
                      _1419_recIdents = _out874;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1416_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1417_recOwned;
                      isErased = _1418_recErased;
                      readIdents = _1419_recIdents;
                    }
                  } else {
                    DAST._IType _1420___mcc_h775 = _source54.dtor_Newtype_a0;
                    DAST._IType _1421_b = _1420___mcc_h775;
                    {
                      if (object.Equals(_503_fromTpe, _1421_b)) {
                        Dafny.ISequence<Dafny.Rune> _1422_recursiveGen;
                        bool _1423_recOwned;
                        bool _1424_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1425_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out875;
                        bool _out876;
                        bool _out877;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out878;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out875, out _out876, out _out877, out _out878);
                        _1422_recursiveGen = _out875;
                        _1423_recOwned = _out876;
                        _1424_recErased = _out877;
                        _1425_recIdents = _out878;
                        Dafny.ISequence<Dafny.Rune> _1426_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out879;
                        _out879 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _1426_rhsType = _out879;
                        Dafny.ISequence<Dafny.Rune> _1427_uneraseFn;
                        _1427_uneraseFn = ((_1423_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1426_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1427_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1422_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1423_recOwned;
                        isErased = false;
                        readIdents = _1425_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out880;
                        bool _out881;
                        bool _out882;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1421_b), _1421_b, _502_toTpe), selfIdent, @params, mustOwn, out _out880, out _out881, out _out882, out _out883);
                        s = _out880;
                        isOwned = _out881;
                        isErased = _out882;
                        readIdents = _out883;
                      }
                    }
                  }
                } else if (_source53.is_Nullable) {
                  DAST._IType _1428___mcc_h777 = _source53.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1429_recursiveGen;
                    bool _1430_recOwned;
                    bool _1431_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1432_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out884;
                    bool _out885;
                    bool _out886;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out887;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out884, out _out885, out _out886, out _out887);
                    _1429_recursiveGen = _out884;
                    _1430_recOwned = _out885;
                    _1431_recErased = _out886;
                    _1432_recIdents = _out887;
                    if (!(_1430_recOwned)) {
                      _1429_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1429_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1429_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1431_recErased;
                    readIdents = _1432_recIdents;
                  }
                } else if (_source53.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1433___mcc_h779 = _source53.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1434_recursiveGen;
                    bool _1435_recOwned;
                    bool _1436_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1437_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out888;
                    bool _out889;
                    bool _out890;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out891;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out888, out _out889, out _out890, out _out891);
                    _1434_recursiveGen = _out888;
                    _1435_recOwned = _out889;
                    _1436_recErased = _out890;
                    _1437_recIdents = _out891;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1434_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1435_recOwned;
                    isErased = _1436_recErased;
                    readIdents = _1437_recIdents;
                  }
                } else if (_source53.is_Array) {
                  DAST._IType _1438___mcc_h781 = _source53.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1439_recursiveGen;
                    bool _1440_recOwned;
                    bool _1441_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1442_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out892;
                    bool _out893;
                    bool _out894;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out892, out _out893, out _out894, out _out895);
                    _1439_recursiveGen = _out892;
                    _1440_recOwned = _out893;
                    _1441_recErased = _out894;
                    _1442_recIdents = _out895;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1439_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1440_recOwned;
                    isErased = _1441_recErased;
                    readIdents = _1442_recIdents;
                  }
                } else if (_source53.is_Seq) {
                  DAST._IType _1443___mcc_h783 = _source53.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1444_recursiveGen;
                    bool _1445_recOwned;
                    bool _1446_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1447_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out896;
                    bool _out897;
                    bool _out898;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out899;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out896, out _out897, out _out898, out _out899);
                    _1444_recursiveGen = _out896;
                    _1445_recOwned = _out897;
                    _1446_recErased = _out898;
                    _1447_recIdents = _out899;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1444_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1445_recOwned;
                    isErased = _1446_recErased;
                    readIdents = _1447_recIdents;
                  }
                } else if (_source53.is_Set) {
                  DAST._IType _1448___mcc_h785 = _source53.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1449_recursiveGen;
                    bool _1450_recOwned;
                    bool _1451_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1452_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out900;
                    bool _out901;
                    bool _out902;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out903;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out900, out _out901, out _out902, out _out903);
                    _1449_recursiveGen = _out900;
                    _1450_recOwned = _out901;
                    _1451_recErased = _out902;
                    _1452_recIdents = _out903;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1449_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1450_recOwned;
                    isErased = _1451_recErased;
                    readIdents = _1452_recIdents;
                  }
                } else if (_source53.is_Multiset) {
                  DAST._IType _1453___mcc_h787 = _source53.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1454_recursiveGen;
                    bool _1455_recOwned;
                    bool _1456_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1457_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out904;
                    bool _out905;
                    bool _out906;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out904, out _out905, out _out906, out _out907);
                    _1454_recursiveGen = _out904;
                    _1455_recOwned = _out905;
                    _1456_recErased = _out906;
                    _1457_recIdents = _out907;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1454_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1455_recOwned;
                    isErased = _1456_recErased;
                    readIdents = _1457_recIdents;
                  }
                } else if (_source53.is_Map) {
                  DAST._IType _1458___mcc_h789 = _source53.dtor_key;
                  DAST._IType _1459___mcc_h790 = _source53.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1460_recursiveGen;
                    bool _1461_recOwned;
                    bool _1462_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1463_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out908;
                    bool _out909;
                    bool _out910;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out911;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out908, out _out909, out _out910, out _out911);
                    _1460_recursiveGen = _out908;
                    _1461_recOwned = _out909;
                    _1462_recErased = _out910;
                    _1463_recIdents = _out911;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1460_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1461_recOwned;
                    isErased = _1462_recErased;
                    readIdents = _1463_recIdents;
                  }
                } else if (_source53.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1464___mcc_h793 = _source53.dtor_args;
                  DAST._IType _1465___mcc_h794 = _source53.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1466_recursiveGen;
                    bool _1467_recOwned;
                    bool _1468_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out912;
                    bool _out913;
                    bool _out914;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out915;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out912, out _out913, out _out914, out _out915);
                    _1466_recursiveGen = _out912;
                    _1467_recOwned = _out913;
                    _1468_recErased = _out914;
                    _1469_recIdents = _out915;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1466_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1467_recOwned;
                    isErased = _1468_recErased;
                    readIdents = _1469_recIdents;
                  }
                } else if (_source53.is_Primitive) {
                  DAST._IPrimitive _1470___mcc_h797 = _source53.dtor_Primitive_a0;
                  DAST._IPrimitive _source55 = _1470___mcc_h797;
                  if (_source55.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1471_recursiveGen;
                      bool _1472_recOwned;
                      bool _1473_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1474_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out916;
                      bool _out917;
                      bool _out918;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out916, out _out917, out _out918, out _out919);
                      _1471_recursiveGen = _out916;
                      _1472_recOwned = _out917;
                      _1473_recErased = _out918;
                      _1474_recIdents = _out919;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1471_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1472_recOwned;
                      isErased = _1473_recErased;
                      readIdents = _1474_recIdents;
                    }
                  } else if (_source55.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1475_recursiveGen;
                      bool _1476___v44;
                      bool _1477___v45;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1478_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out920;
                      bool _out921;
                      bool _out922;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out923;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, true, out _out920, out _out921, out _out922, out _out923);
                      _1475_recursiveGen = _out920;
                      _1476___v44 = _out921;
                      _1477___v45 = _out922;
                      _1478_recIdents = _out923;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1475_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1478_recIdents;
                    }
                  } else if (_source55.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1479_recursiveGen;
                      bool _1480_recOwned;
                      bool _1481_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1482_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out924;
                      bool _out925;
                      bool _out926;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out927;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out924, out _out925, out _out926, out _out927);
                      _1479_recursiveGen = _out924;
                      _1480_recOwned = _out925;
                      _1481_recErased = _out926;
                      _1482_recIdents = _out927;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1479_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1480_recOwned;
                      isErased = _1481_recErased;
                      readIdents = _1482_recIdents;
                    }
                  } else if (_source55.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1483_recursiveGen;
                      bool _1484_recOwned;
                      bool _1485_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1486_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out928;
                      bool _out929;
                      bool _out930;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out928, out _out929, out _out930, out _out931);
                      _1483_recursiveGen = _out928;
                      _1484_recOwned = _out929;
                      _1485_recErased = _out930;
                      _1486_recIdents = _out931;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1483_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1484_recOwned;
                      isErased = _1485_recErased;
                      readIdents = _1486_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1487_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out932;
                      _out932 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1487_rhsType = _out932;
                      Dafny.ISequence<Dafny.Rune> _1488_recursiveGen;
                      bool _1489___v54;
                      bool _1490___v55;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1491_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out933;
                      bool _out934;
                      bool _out935;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, true, out _out933, out _out934, out _out935, out _out936);
                      _1488_recursiveGen = _out933;
                      _1489___v54 = _out934;
                      _1490___v55 = _out935;
                      _1491_recIdents = _out936;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1488_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1491_recIdents;
                    }
                  }
                } else if (_source53.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1492___mcc_h799 = _source53.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1493_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out937;
                    _out937 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                    _1493_rhsType = _out937;
                    Dafny.ISequence<Dafny.Rune> _1494_recursiveGen;
                    bool _1495___v49;
                    bool _1496___v50;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1497_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out938;
                    bool _out939;
                    bool _out940;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out941;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, true, out _out938, out _out939, out _out940, out _out941);
                    _1494_recursiveGen = _out938;
                    _1495___v49 = _out939;
                    _1496___v50 = _out940;
                    _1497_recIdents = _out941;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1493_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1494_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1497_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1498___mcc_h801 = _source53.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1499_recursiveGen;
                    bool _1500_recOwned;
                    bool _1501_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1502_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out942;
                    bool _out943;
                    bool _out944;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out942, out _out943, out _out944, out _out945);
                    _1499_recursiveGen = _out942;
                    _1500_recOwned = _out943;
                    _1501_recErased = _out944;
                    _1502_recIdents = _out945;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1499_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1500_recOwned;
                    isErased = _1501_recErased;
                    readIdents = _1502_recIdents;
                  }
                }
              } else if (_source52.is_Real) {
                DAST._IType _source56 = _510___mcc_h238;
                if (_source56.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1503___mcc_h803 = _source56.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1504___mcc_h804 = _source56.dtor_typeArgs;
                  DAST._IResolvedType _1505___mcc_h805 = _source56.dtor_resolved;
                  DAST._IResolvedType _source57 = _1505___mcc_h805;
                  if (_source57.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1506___mcc_h809 = _source57.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1507_recursiveGen;
                      bool _1508_recOwned;
                      bool _1509_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out946;
                      bool _out947;
                      bool _out948;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out946, out _out947, out _out948, out _out949);
                      _1507_recursiveGen = _out946;
                      _1508_recOwned = _out947;
                      _1509_recErased = _out948;
                      _1510_recIdents = _out949;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1507_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1508_recOwned;
                      isErased = _1509_recErased;
                      readIdents = _1510_recIdents;
                    }
                  } else if (_source57.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1511___mcc_h811 = _source57.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1512_recursiveGen;
                      bool _1513_recOwned;
                      bool _1514_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1515_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out950;
                      bool _out951;
                      bool _out952;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out953;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out950, out _out951, out _out952, out _out953);
                      _1512_recursiveGen = _out950;
                      _1513_recOwned = _out951;
                      _1514_recErased = _out952;
                      _1515_recIdents = _out953;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1512_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1513_recOwned;
                      isErased = _1514_recErased;
                      readIdents = _1515_recIdents;
                    }
                  } else {
                    DAST._IType _1516___mcc_h813 = _source57.dtor_Newtype_a0;
                    DAST._IType _1517_b = _1516___mcc_h813;
                    {
                      if (object.Equals(_503_fromTpe, _1517_b)) {
                        Dafny.ISequence<Dafny.Rune> _1518_recursiveGen;
                        bool _1519_recOwned;
                        bool _1520_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1521_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out954;
                        bool _out955;
                        bool _out956;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out954, out _out955, out _out956, out _out957);
                        _1518_recursiveGen = _out954;
                        _1519_recOwned = _out955;
                        _1520_recErased = _out956;
                        _1521_recIdents = _out957;
                        Dafny.ISequence<Dafny.Rune> _1522_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out958;
                        _out958 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _1522_rhsType = _out958;
                        Dafny.ISequence<Dafny.Rune> _1523_uneraseFn;
                        _1523_uneraseFn = ((_1519_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1522_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1523_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1518_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1519_recOwned;
                        isErased = false;
                        readIdents = _1521_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out959;
                        bool _out960;
                        bool _out961;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out962;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1517_b), _1517_b, _502_toTpe), selfIdent, @params, mustOwn, out _out959, out _out960, out _out961, out _out962);
                        s = _out959;
                        isOwned = _out960;
                        isErased = _out961;
                        readIdents = _out962;
                      }
                    }
                  }
                } else if (_source56.is_Nullable) {
                  DAST._IType _1524___mcc_h815 = _source56.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1525_recursiveGen;
                    bool _1526_recOwned;
                    bool _1527_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1528_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out963;
                    bool _out964;
                    bool _out965;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out963, out _out964, out _out965, out _out966);
                    _1525_recursiveGen = _out963;
                    _1526_recOwned = _out964;
                    _1527_recErased = _out965;
                    _1528_recIdents = _out966;
                    if (!(_1526_recOwned)) {
                      _1525_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1525_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1525_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1527_recErased;
                    readIdents = _1528_recIdents;
                  }
                } else if (_source56.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1529___mcc_h817 = _source56.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1530_recursiveGen;
                    bool _1531_recOwned;
                    bool _1532_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1533_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out967;
                    bool _out968;
                    bool _out969;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out970;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out967, out _out968, out _out969, out _out970);
                    _1530_recursiveGen = _out967;
                    _1531_recOwned = _out968;
                    _1532_recErased = _out969;
                    _1533_recIdents = _out970;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1530_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1531_recOwned;
                    isErased = _1532_recErased;
                    readIdents = _1533_recIdents;
                  }
                } else if (_source56.is_Array) {
                  DAST._IType _1534___mcc_h819 = _source56.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1535_recursiveGen;
                    bool _1536_recOwned;
                    bool _1537_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1538_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out971;
                    bool _out972;
                    bool _out973;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out971, out _out972, out _out973, out _out974);
                    _1535_recursiveGen = _out971;
                    _1536_recOwned = _out972;
                    _1537_recErased = _out973;
                    _1538_recIdents = _out974;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1535_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1536_recOwned;
                    isErased = _1537_recErased;
                    readIdents = _1538_recIdents;
                  }
                } else if (_source56.is_Seq) {
                  DAST._IType _1539___mcc_h821 = _source56.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1540_recursiveGen;
                    bool _1541_recOwned;
                    bool _1542_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1543_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out975;
                    bool _out976;
                    bool _out977;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out978;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out975, out _out976, out _out977, out _out978);
                    _1540_recursiveGen = _out975;
                    _1541_recOwned = _out976;
                    _1542_recErased = _out977;
                    _1543_recIdents = _out978;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1540_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1541_recOwned;
                    isErased = _1542_recErased;
                    readIdents = _1543_recIdents;
                  }
                } else if (_source56.is_Set) {
                  DAST._IType _1544___mcc_h823 = _source56.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1545_recursiveGen;
                    bool _1546_recOwned;
                    bool _1547_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1548_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out979;
                    bool _out980;
                    bool _out981;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out979, out _out980, out _out981, out _out982);
                    _1545_recursiveGen = _out979;
                    _1546_recOwned = _out980;
                    _1547_recErased = _out981;
                    _1548_recIdents = _out982;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1545_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1546_recOwned;
                    isErased = _1547_recErased;
                    readIdents = _1548_recIdents;
                  }
                } else if (_source56.is_Multiset) {
                  DAST._IType _1549___mcc_h825 = _source56.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1550_recursiveGen;
                    bool _1551_recOwned;
                    bool _1552_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1553_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out983;
                    bool _out984;
                    bool _out985;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out986;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out983, out _out984, out _out985, out _out986);
                    _1550_recursiveGen = _out983;
                    _1551_recOwned = _out984;
                    _1552_recErased = _out985;
                    _1553_recIdents = _out986;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1550_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1551_recOwned;
                    isErased = _1552_recErased;
                    readIdents = _1553_recIdents;
                  }
                } else if (_source56.is_Map) {
                  DAST._IType _1554___mcc_h827 = _source56.dtor_key;
                  DAST._IType _1555___mcc_h828 = _source56.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1556_recursiveGen;
                    bool _1557_recOwned;
                    bool _1558_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out987;
                    bool _out988;
                    bool _out989;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out987, out _out988, out _out989, out _out990);
                    _1556_recursiveGen = _out987;
                    _1557_recOwned = _out988;
                    _1558_recErased = _out989;
                    _1559_recIdents = _out990;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1556_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1557_recOwned;
                    isErased = _1558_recErased;
                    readIdents = _1559_recIdents;
                  }
                } else if (_source56.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1560___mcc_h831 = _source56.dtor_args;
                  DAST._IType _1561___mcc_h832 = _source56.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1562_recursiveGen;
                    bool _1563_recOwned;
                    bool _1564_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1565_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out991;
                    bool _out992;
                    bool _out993;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out994;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out991, out _out992, out _out993, out _out994);
                    _1562_recursiveGen = _out991;
                    _1563_recOwned = _out992;
                    _1564_recErased = _out993;
                    _1565_recIdents = _out994;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1562_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1563_recOwned;
                    isErased = _1564_recErased;
                    readIdents = _1565_recIdents;
                  }
                } else if (_source56.is_Primitive) {
                  DAST._IPrimitive _1566___mcc_h835 = _source56.dtor_Primitive_a0;
                  DAST._IPrimitive _source58 = _1566___mcc_h835;
                  if (_source58.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1567_recursiveGen;
                      bool _1568___v46;
                      bool _1569___v47;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1570_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out995;
                      bool _out996;
                      bool _out997;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out998;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, false, out _out995, out _out996, out _out997, out _out998);
                      _1567_recursiveGen = _out995;
                      _1568___v46 = _out996;
                      _1569___v47 = _out997;
                      _1570_recIdents = _out998;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1567_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1570_recIdents;
                    }
                  } else if (_source58.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1571_recursiveGen;
                      bool _1572_recOwned;
                      bool _1573_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1574_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out999;
                      bool _out1000;
                      bool _out1001;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out999, out _out1000, out _out1001, out _out1002);
                      _1571_recursiveGen = _out999;
                      _1572_recOwned = _out1000;
                      _1573_recErased = _out1001;
                      _1574_recIdents = _out1002;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1571_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1572_recOwned;
                      isErased = _1573_recErased;
                      readIdents = _1574_recIdents;
                    }
                  } else if (_source58.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1575_recursiveGen;
                      bool _1576_recOwned;
                      bool _1577_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1578_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1003;
                      bool _out1004;
                      bool _out1005;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1006;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1003, out _out1004, out _out1005, out _out1006);
                      _1575_recursiveGen = _out1003;
                      _1576_recOwned = _out1004;
                      _1577_recErased = _out1005;
                      _1578_recIdents = _out1006;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1575_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1576_recOwned;
                      isErased = _1577_recErased;
                      readIdents = _1578_recIdents;
                    }
                  } else if (_source58.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1579_recursiveGen;
                      bool _1580_recOwned;
                      bool _1581_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1582_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1007;
                      bool _out1008;
                      bool _out1009;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1007, out _out1008, out _out1009, out _out1010);
                      _1579_recursiveGen = _out1007;
                      _1580_recOwned = _out1008;
                      _1581_recErased = _out1009;
                      _1582_recIdents = _out1010;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1579_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1580_recOwned;
                      isErased = _1581_recErased;
                      readIdents = _1582_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1583_recursiveGen;
                      bool _1584_recOwned;
                      bool _1585_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1586_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1011;
                      bool _out1012;
                      bool _out1013;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1011, out _out1012, out _out1013, out _out1014);
                      _1583_recursiveGen = _out1011;
                      _1584_recOwned = _out1012;
                      _1585_recErased = _out1013;
                      _1586_recIdents = _out1014;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1583_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1584_recOwned;
                      isErased = _1585_recErased;
                      readIdents = _1586_recIdents;
                    }
                  }
                } else if (_source56.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1587___mcc_h837 = _source56.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1588_recursiveGen;
                    bool _1589_recOwned;
                    bool _1590_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1591_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1015;
                    bool _out1016;
                    bool _out1017;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1018;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1015, out _out1016, out _out1017, out _out1018);
                    _1588_recursiveGen = _out1015;
                    _1589_recOwned = _out1016;
                    _1590_recErased = _out1017;
                    _1591_recIdents = _out1018;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1588_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1589_recOwned;
                    isErased = _1590_recErased;
                    readIdents = _1591_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1592___mcc_h839 = _source56.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1593_recursiveGen;
                    bool _1594_recOwned;
                    bool _1595_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1596_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1019;
                    bool _out1020;
                    bool _out1021;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1019, out _out1020, out _out1021, out _out1022);
                    _1593_recursiveGen = _out1019;
                    _1594_recOwned = _out1020;
                    _1595_recErased = _out1021;
                    _1596_recIdents = _out1022;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1593_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1594_recOwned;
                    isErased = _1595_recErased;
                    readIdents = _1596_recIdents;
                  }
                }
              } else if (_source52.is_String) {
                DAST._IType _source59 = _510___mcc_h238;
                if (_source59.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1597___mcc_h841 = _source59.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1598___mcc_h842 = _source59.dtor_typeArgs;
                  DAST._IResolvedType _1599___mcc_h843 = _source59.dtor_resolved;
                  DAST._IResolvedType _source60 = _1599___mcc_h843;
                  if (_source60.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1600___mcc_h847 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1601_recursiveGen;
                      bool _1602_recOwned;
                      bool _1603_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1604_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1023;
                      bool _out1024;
                      bool _out1025;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1023, out _out1024, out _out1025, out _out1026);
                      _1601_recursiveGen = _out1023;
                      _1602_recOwned = _out1024;
                      _1603_recErased = _out1025;
                      _1604_recIdents = _out1026;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1601_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1602_recOwned;
                      isErased = _1603_recErased;
                      readIdents = _1604_recIdents;
                    }
                  } else if (_source60.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1605___mcc_h849 = _source60.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1606_recursiveGen;
                      bool _1607_recOwned;
                      bool _1608_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1609_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1027;
                      bool _out1028;
                      bool _out1029;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1030;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1027, out _out1028, out _out1029, out _out1030);
                      _1606_recursiveGen = _out1027;
                      _1607_recOwned = _out1028;
                      _1608_recErased = _out1029;
                      _1609_recIdents = _out1030;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1606_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1607_recOwned;
                      isErased = _1608_recErased;
                      readIdents = _1609_recIdents;
                    }
                  } else {
                    DAST._IType _1610___mcc_h851 = _source60.dtor_Newtype_a0;
                    DAST._IType _1611_b = _1610___mcc_h851;
                    {
                      if (object.Equals(_503_fromTpe, _1611_b)) {
                        Dafny.ISequence<Dafny.Rune> _1612_recursiveGen;
                        bool _1613_recOwned;
                        bool _1614_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1615_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1031;
                        bool _out1032;
                        bool _out1033;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1031, out _out1032, out _out1033, out _out1034);
                        _1612_recursiveGen = _out1031;
                        _1613_recOwned = _out1032;
                        _1614_recErased = _out1033;
                        _1615_recIdents = _out1034;
                        Dafny.ISequence<Dafny.Rune> _1616_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1035;
                        _out1035 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _1616_rhsType = _out1035;
                        Dafny.ISequence<Dafny.Rune> _1617_uneraseFn;
                        _1617_uneraseFn = ((_1613_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1616_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1617_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1612_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1613_recOwned;
                        isErased = false;
                        readIdents = _1615_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1036;
                        bool _out1037;
                        bool _out1038;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1039;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1611_b), _1611_b, _502_toTpe), selfIdent, @params, mustOwn, out _out1036, out _out1037, out _out1038, out _out1039);
                        s = _out1036;
                        isOwned = _out1037;
                        isErased = _out1038;
                        readIdents = _out1039;
                      }
                    }
                  }
                } else if (_source59.is_Nullable) {
                  DAST._IType _1618___mcc_h853 = _source59.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1619_recursiveGen;
                    bool _1620_recOwned;
                    bool _1621_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1622_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1040;
                    bool _out1041;
                    bool _out1042;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1040, out _out1041, out _out1042, out _out1043);
                    _1619_recursiveGen = _out1040;
                    _1620_recOwned = _out1041;
                    _1621_recErased = _out1042;
                    _1622_recIdents = _out1043;
                    if (!(_1620_recOwned)) {
                      _1619_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1619_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1619_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1621_recErased;
                    readIdents = _1622_recIdents;
                  }
                } else if (_source59.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1623___mcc_h855 = _source59.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1624_recursiveGen;
                    bool _1625_recOwned;
                    bool _1626_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1627_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1044;
                    bool _out1045;
                    bool _out1046;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1047;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1044, out _out1045, out _out1046, out _out1047);
                    _1624_recursiveGen = _out1044;
                    _1625_recOwned = _out1045;
                    _1626_recErased = _out1046;
                    _1627_recIdents = _out1047;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1624_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1625_recOwned;
                    isErased = _1626_recErased;
                    readIdents = _1627_recIdents;
                  }
                } else if (_source59.is_Array) {
                  DAST._IType _1628___mcc_h857 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1629_recursiveGen;
                    bool _1630_recOwned;
                    bool _1631_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1632_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1048;
                    bool _out1049;
                    bool _out1050;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1051;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1048, out _out1049, out _out1050, out _out1051);
                    _1629_recursiveGen = _out1048;
                    _1630_recOwned = _out1049;
                    _1631_recErased = _out1050;
                    _1632_recIdents = _out1051;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1629_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1630_recOwned;
                    isErased = _1631_recErased;
                    readIdents = _1632_recIdents;
                  }
                } else if (_source59.is_Seq) {
                  DAST._IType _1633___mcc_h859 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1634_recursiveGen;
                    bool _1635_recOwned;
                    bool _1636_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1637_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1052;
                    bool _out1053;
                    bool _out1054;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1052, out _out1053, out _out1054, out _out1055);
                    _1634_recursiveGen = _out1052;
                    _1635_recOwned = _out1053;
                    _1636_recErased = _out1054;
                    _1637_recIdents = _out1055;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1634_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1635_recOwned;
                    isErased = _1636_recErased;
                    readIdents = _1637_recIdents;
                  }
                } else if (_source59.is_Set) {
                  DAST._IType _1638___mcc_h861 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1639_recursiveGen;
                    bool _1640_recOwned;
                    bool _1641_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1642_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1056;
                    bool _out1057;
                    bool _out1058;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1059;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1056, out _out1057, out _out1058, out _out1059);
                    _1639_recursiveGen = _out1056;
                    _1640_recOwned = _out1057;
                    _1641_recErased = _out1058;
                    _1642_recIdents = _out1059;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1639_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1640_recOwned;
                    isErased = _1641_recErased;
                    readIdents = _1642_recIdents;
                  }
                } else if (_source59.is_Multiset) {
                  DAST._IType _1643___mcc_h863 = _source59.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1644_recursiveGen;
                    bool _1645_recOwned;
                    bool _1646_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1647_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1060;
                    bool _out1061;
                    bool _out1062;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1063;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1060, out _out1061, out _out1062, out _out1063);
                    _1644_recursiveGen = _out1060;
                    _1645_recOwned = _out1061;
                    _1646_recErased = _out1062;
                    _1647_recIdents = _out1063;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1644_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1645_recOwned;
                    isErased = _1646_recErased;
                    readIdents = _1647_recIdents;
                  }
                } else if (_source59.is_Map) {
                  DAST._IType _1648___mcc_h865 = _source59.dtor_key;
                  DAST._IType _1649___mcc_h866 = _source59.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1650_recursiveGen;
                    bool _1651_recOwned;
                    bool _1652_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1653_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1064;
                    bool _out1065;
                    bool _out1066;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1064, out _out1065, out _out1066, out _out1067);
                    _1650_recursiveGen = _out1064;
                    _1651_recOwned = _out1065;
                    _1652_recErased = _out1066;
                    _1653_recIdents = _out1067;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1650_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1651_recOwned;
                    isErased = _1652_recErased;
                    readIdents = _1653_recIdents;
                  }
                } else if (_source59.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1654___mcc_h869 = _source59.dtor_args;
                  DAST._IType _1655___mcc_h870 = _source59.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1656_recursiveGen;
                    bool _1657_recOwned;
                    bool _1658_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1659_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1068;
                    bool _out1069;
                    bool _out1070;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1071;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1068, out _out1069, out _out1070, out _out1071);
                    _1656_recursiveGen = _out1068;
                    _1657_recOwned = _out1069;
                    _1658_recErased = _out1070;
                    _1659_recIdents = _out1071;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1656_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1657_recOwned;
                    isErased = _1658_recErased;
                    readIdents = _1659_recIdents;
                  }
                } else if (_source59.is_Primitive) {
                  DAST._IPrimitive _1660___mcc_h873 = _source59.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1661_recursiveGen;
                    bool _1662_recOwned;
                    bool _1663_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1664_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1072;
                    bool _out1073;
                    bool _out1074;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1075;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1072, out _out1073, out _out1074, out _out1075);
                    _1661_recursiveGen = _out1072;
                    _1662_recOwned = _out1073;
                    _1663_recErased = _out1074;
                    _1664_recIdents = _out1075;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1661_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1662_recOwned;
                    isErased = _1663_recErased;
                    readIdents = _1664_recIdents;
                  }
                } else if (_source59.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1665___mcc_h875 = _source59.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1666_recursiveGen;
                    bool _1667_recOwned;
                    bool _1668_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1076;
                    bool _out1077;
                    bool _out1078;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1076, out _out1077, out _out1078, out _out1079);
                    _1666_recursiveGen = _out1076;
                    _1667_recOwned = _out1077;
                    _1668_recErased = _out1078;
                    _1669_recIdents = _out1079;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1666_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1667_recOwned;
                    isErased = _1668_recErased;
                    readIdents = _1669_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1670___mcc_h877 = _source59.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1671_recursiveGen;
                    bool _1672_recOwned;
                    bool _1673_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1674_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1080;
                    bool _out1081;
                    bool _out1082;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1083;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1080, out _out1081, out _out1082, out _out1083);
                    _1671_recursiveGen = _out1080;
                    _1672_recOwned = _out1081;
                    _1673_recErased = _out1082;
                    _1674_recIdents = _out1083;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1671_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1672_recOwned;
                    isErased = _1673_recErased;
                    readIdents = _1674_recIdents;
                  }
                }
              } else if (_source52.is_Bool) {
                DAST._IType _source61 = _510___mcc_h238;
                if (_source61.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1675___mcc_h879 = _source61.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1676___mcc_h880 = _source61.dtor_typeArgs;
                  DAST._IResolvedType _1677___mcc_h881 = _source61.dtor_resolved;
                  DAST._IResolvedType _source62 = _1677___mcc_h881;
                  if (_source62.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1678___mcc_h885 = _source62.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1679_recursiveGen;
                      bool _1680_recOwned;
                      bool _1681_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1682_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1084;
                      bool _out1085;
                      bool _out1086;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1087;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1084, out _out1085, out _out1086, out _out1087);
                      _1679_recursiveGen = _out1084;
                      _1680_recOwned = _out1085;
                      _1681_recErased = _out1086;
                      _1682_recIdents = _out1087;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1679_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1680_recOwned;
                      isErased = _1681_recErased;
                      readIdents = _1682_recIdents;
                    }
                  } else if (_source62.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1683___mcc_h887 = _source62.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1684_recursiveGen;
                      bool _1685_recOwned;
                      bool _1686_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1687_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1088;
                      bool _out1089;
                      bool _out1090;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1088, out _out1089, out _out1090, out _out1091);
                      _1684_recursiveGen = _out1088;
                      _1685_recOwned = _out1089;
                      _1686_recErased = _out1090;
                      _1687_recIdents = _out1091;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1684_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1685_recOwned;
                      isErased = _1686_recErased;
                      readIdents = _1687_recIdents;
                    }
                  } else {
                    DAST._IType _1688___mcc_h889 = _source62.dtor_Newtype_a0;
                    DAST._IType _1689_b = _1688___mcc_h889;
                    {
                      if (object.Equals(_503_fromTpe, _1689_b)) {
                        Dafny.ISequence<Dafny.Rune> _1690_recursiveGen;
                        bool _1691_recOwned;
                        bool _1692_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1693_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1092;
                        bool _out1093;
                        bool _out1094;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1095;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1092, out _out1093, out _out1094, out _out1095);
                        _1690_recursiveGen = _out1092;
                        _1691_recOwned = _out1093;
                        _1692_recErased = _out1094;
                        _1693_recIdents = _out1095;
                        Dafny.ISequence<Dafny.Rune> _1694_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1096;
                        _out1096 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _1694_rhsType = _out1096;
                        Dafny.ISequence<Dafny.Rune> _1695_uneraseFn;
                        _1695_uneraseFn = ((_1691_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1694_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1695_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1690_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1691_recOwned;
                        isErased = false;
                        readIdents = _1693_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1097;
                        bool _out1098;
                        bool _out1099;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1689_b), _1689_b, _502_toTpe), selfIdent, @params, mustOwn, out _out1097, out _out1098, out _out1099, out _out1100);
                        s = _out1097;
                        isOwned = _out1098;
                        isErased = _out1099;
                        readIdents = _out1100;
                      }
                    }
                  }
                } else if (_source61.is_Nullable) {
                  DAST._IType _1696___mcc_h891 = _source61.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1697_recursiveGen;
                    bool _1698_recOwned;
                    bool _1699_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1700_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1101;
                    bool _out1102;
                    bool _out1103;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1104;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1101, out _out1102, out _out1103, out _out1104);
                    _1697_recursiveGen = _out1101;
                    _1698_recOwned = _out1102;
                    _1699_recErased = _out1103;
                    _1700_recIdents = _out1104;
                    if (!(_1698_recOwned)) {
                      _1697_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1697_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1697_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1699_recErased;
                    readIdents = _1700_recIdents;
                  }
                } else if (_source61.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1701___mcc_h893 = _source61.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1702_recursiveGen;
                    bool _1703_recOwned;
                    bool _1704_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1705_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1105;
                    bool _out1106;
                    bool _out1107;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1108;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1105, out _out1106, out _out1107, out _out1108);
                    _1702_recursiveGen = _out1105;
                    _1703_recOwned = _out1106;
                    _1704_recErased = _out1107;
                    _1705_recIdents = _out1108;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1702_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1703_recOwned;
                    isErased = _1704_recErased;
                    readIdents = _1705_recIdents;
                  }
                } else if (_source61.is_Array) {
                  DAST._IType _1706___mcc_h895 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1707_recursiveGen;
                    bool _1708_recOwned;
                    bool _1709_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1710_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1109;
                    bool _out1110;
                    bool _out1111;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1109, out _out1110, out _out1111, out _out1112);
                    _1707_recursiveGen = _out1109;
                    _1708_recOwned = _out1110;
                    _1709_recErased = _out1111;
                    _1710_recIdents = _out1112;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1707_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1708_recOwned;
                    isErased = _1709_recErased;
                    readIdents = _1710_recIdents;
                  }
                } else if (_source61.is_Seq) {
                  DAST._IType _1711___mcc_h897 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1712_recursiveGen;
                    bool _1713_recOwned;
                    bool _1714_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1715_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1113;
                    bool _out1114;
                    bool _out1115;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1116;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1113, out _out1114, out _out1115, out _out1116);
                    _1712_recursiveGen = _out1113;
                    _1713_recOwned = _out1114;
                    _1714_recErased = _out1115;
                    _1715_recIdents = _out1116;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1712_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1713_recOwned;
                    isErased = _1714_recErased;
                    readIdents = _1715_recIdents;
                  }
                } else if (_source61.is_Set) {
                  DAST._IType _1716___mcc_h899 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1717_recursiveGen;
                    bool _1718_recOwned;
                    bool _1719_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1720_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1117;
                    bool _out1118;
                    bool _out1119;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1120;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1117, out _out1118, out _out1119, out _out1120);
                    _1717_recursiveGen = _out1117;
                    _1718_recOwned = _out1118;
                    _1719_recErased = _out1119;
                    _1720_recIdents = _out1120;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1717_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1718_recOwned;
                    isErased = _1719_recErased;
                    readIdents = _1720_recIdents;
                  }
                } else if (_source61.is_Multiset) {
                  DAST._IType _1721___mcc_h901 = _source61.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1722_recursiveGen;
                    bool _1723_recOwned;
                    bool _1724_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1725_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1121;
                    bool _out1122;
                    bool _out1123;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1121, out _out1122, out _out1123, out _out1124);
                    _1722_recursiveGen = _out1121;
                    _1723_recOwned = _out1122;
                    _1724_recErased = _out1123;
                    _1725_recIdents = _out1124;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1722_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1723_recOwned;
                    isErased = _1724_recErased;
                    readIdents = _1725_recIdents;
                  }
                } else if (_source61.is_Map) {
                  DAST._IType _1726___mcc_h903 = _source61.dtor_key;
                  DAST._IType _1727___mcc_h904 = _source61.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1728_recursiveGen;
                    bool _1729_recOwned;
                    bool _1730_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1731_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1125;
                    bool _out1126;
                    bool _out1127;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1125, out _out1126, out _out1127, out _out1128);
                    _1728_recursiveGen = _out1125;
                    _1729_recOwned = _out1126;
                    _1730_recErased = _out1127;
                    _1731_recIdents = _out1128;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1728_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1729_recOwned;
                    isErased = _1730_recErased;
                    readIdents = _1731_recIdents;
                  }
                } else if (_source61.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1732___mcc_h907 = _source61.dtor_args;
                  DAST._IType _1733___mcc_h908 = _source61.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1734_recursiveGen;
                    bool _1735_recOwned;
                    bool _1736_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1737_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1129;
                    bool _out1130;
                    bool _out1131;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1132;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1129, out _out1130, out _out1131, out _out1132);
                    _1734_recursiveGen = _out1129;
                    _1735_recOwned = _out1130;
                    _1736_recErased = _out1131;
                    _1737_recIdents = _out1132;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1734_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1735_recOwned;
                    isErased = _1736_recErased;
                    readIdents = _1737_recIdents;
                  }
                } else if (_source61.is_Primitive) {
                  DAST._IPrimitive _1738___mcc_h911 = _source61.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1739_recursiveGen;
                    bool _1740_recOwned;
                    bool _1741_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1742_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1133;
                    bool _out1134;
                    bool _out1135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1133, out _out1134, out _out1135, out _out1136);
                    _1739_recursiveGen = _out1133;
                    _1740_recOwned = _out1134;
                    _1741_recErased = _out1135;
                    _1742_recIdents = _out1136;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1739_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1740_recOwned;
                    isErased = _1741_recErased;
                    readIdents = _1742_recIdents;
                  }
                } else if (_source61.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1743___mcc_h913 = _source61.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1744_recursiveGen;
                    bool _1745_recOwned;
                    bool _1746_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1137;
                    bool _out1138;
                    bool _out1139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1140;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1137, out _out1138, out _out1139, out _out1140);
                    _1744_recursiveGen = _out1137;
                    _1745_recOwned = _out1138;
                    _1746_recErased = _out1139;
                    _1747_recIdents = _out1140;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1744_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1745_recOwned;
                    isErased = _1746_recErased;
                    readIdents = _1747_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1748___mcc_h915 = _source61.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1749_recursiveGen;
                    bool _1750_recOwned;
                    bool _1751_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1752_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1141;
                    bool _out1142;
                    bool _out1143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1144;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1141, out _out1142, out _out1143, out _out1144);
                    _1749_recursiveGen = _out1141;
                    _1750_recOwned = _out1142;
                    _1751_recErased = _out1143;
                    _1752_recIdents = _out1144;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1749_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1750_recOwned;
                    isErased = _1751_recErased;
                    readIdents = _1752_recIdents;
                  }
                }
              } else {
                DAST._IType _source63 = _510___mcc_h238;
                if (_source63.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1753___mcc_h917 = _source63.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1754___mcc_h918 = _source63.dtor_typeArgs;
                  DAST._IResolvedType _1755___mcc_h919 = _source63.dtor_resolved;
                  DAST._IResolvedType _source64 = _1755___mcc_h919;
                  if (_source64.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1756___mcc_h923 = _source64.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1757_recursiveGen;
                      bool _1758_recOwned;
                      bool _1759_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1145;
                      bool _out1146;
                      bool _out1147;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1145, out _out1146, out _out1147, out _out1148);
                      _1757_recursiveGen = _out1145;
                      _1758_recOwned = _out1146;
                      _1759_recErased = _out1147;
                      _1760_recIdents = _out1148;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1757_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1758_recOwned;
                      isErased = _1759_recErased;
                      readIdents = _1760_recIdents;
                    }
                  } else if (_source64.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1761___mcc_h925 = _source64.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1762_recursiveGen;
                      bool _1763_recOwned;
                      bool _1764_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1765_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1149;
                      bool _out1150;
                      bool _out1151;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1152;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1149, out _out1150, out _out1151, out _out1152);
                      _1762_recursiveGen = _out1149;
                      _1763_recOwned = _out1150;
                      _1764_recErased = _out1151;
                      _1765_recIdents = _out1152;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1762_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1763_recOwned;
                      isErased = _1764_recErased;
                      readIdents = _1765_recIdents;
                    }
                  } else {
                    DAST._IType _1766___mcc_h927 = _source64.dtor_Newtype_a0;
                    DAST._IType _1767_b = _1766___mcc_h927;
                    {
                      if (object.Equals(_503_fromTpe, _1767_b)) {
                        Dafny.ISequence<Dafny.Rune> _1768_recursiveGen;
                        bool _1769_recOwned;
                        bool _1770_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1771_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1153;
                        bool _out1154;
                        bool _out1155;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1156;
                        DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1153, out _out1154, out _out1155, out _out1156);
                        _1768_recursiveGen = _out1153;
                        _1769_recOwned = _out1154;
                        _1770_recErased = _out1155;
                        _1771_recIdents = _out1156;
                        Dafny.ISequence<Dafny.Rune> _1772_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1157;
                        _out1157 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                        _1772_rhsType = _out1157;
                        Dafny.ISequence<Dafny.Rune> _1773_uneraseFn;
                        _1773_uneraseFn = ((_1769_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1772_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1773_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1768_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1769_recOwned;
                        isErased = false;
                        readIdents = _1771_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1158;
                        bool _out1159;
                        bool _out1160;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1161;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1767_b), _1767_b, _502_toTpe), selfIdent, @params, mustOwn, out _out1158, out _out1159, out _out1160, out _out1161);
                        s = _out1158;
                        isOwned = _out1159;
                        isErased = _out1160;
                        readIdents = _out1161;
                      }
                    }
                  }
                } else if (_source63.is_Nullable) {
                  DAST._IType _1774___mcc_h929 = _source63.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1775_recursiveGen;
                    bool _1776_recOwned;
                    bool _1777_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1162;
                    bool _out1163;
                    bool _out1164;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1165;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1162, out _out1163, out _out1164, out _out1165);
                    _1775_recursiveGen = _out1162;
                    _1776_recOwned = _out1163;
                    _1777_recErased = _out1164;
                    _1778_recIdents = _out1165;
                    if (!(_1776_recOwned)) {
                      _1775_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1775_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1775_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1777_recErased;
                    readIdents = _1778_recIdents;
                  }
                } else if (_source63.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1779___mcc_h931 = _source63.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1780_recursiveGen;
                    bool _1781_recOwned;
                    bool _1782_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1783_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1166;
                    bool _out1167;
                    bool _out1168;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1166, out _out1167, out _out1168, out _out1169);
                    _1780_recursiveGen = _out1166;
                    _1781_recOwned = _out1167;
                    _1782_recErased = _out1168;
                    _1783_recIdents = _out1169;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1780_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1781_recOwned;
                    isErased = _1782_recErased;
                    readIdents = _1783_recIdents;
                  }
                } else if (_source63.is_Array) {
                  DAST._IType _1784___mcc_h933 = _source63.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1785_recursiveGen;
                    bool _1786_recOwned;
                    bool _1787_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1170;
                    bool _out1171;
                    bool _out1172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1173;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1170, out _out1171, out _out1172, out _out1173);
                    _1785_recursiveGen = _out1170;
                    _1786_recOwned = _out1171;
                    _1787_recErased = _out1172;
                    _1788_recIdents = _out1173;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1785_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1786_recOwned;
                    isErased = _1787_recErased;
                    readIdents = _1788_recIdents;
                  }
                } else if (_source63.is_Seq) {
                  DAST._IType _1789___mcc_h935 = _source63.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1790_recursiveGen;
                    bool _1791_recOwned;
                    bool _1792_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1174;
                    bool _out1175;
                    bool _out1176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1177;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1174, out _out1175, out _out1176, out _out1177);
                    _1790_recursiveGen = _out1174;
                    _1791_recOwned = _out1175;
                    _1792_recErased = _out1176;
                    _1793_recIdents = _out1177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1790_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1791_recOwned;
                    isErased = _1792_recErased;
                    readIdents = _1793_recIdents;
                  }
                } else if (_source63.is_Set) {
                  DAST._IType _1794___mcc_h937 = _source63.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1795_recursiveGen;
                    bool _1796_recOwned;
                    bool _1797_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1798_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1178;
                    bool _out1179;
                    bool _out1180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1178, out _out1179, out _out1180, out _out1181);
                    _1795_recursiveGen = _out1178;
                    _1796_recOwned = _out1179;
                    _1797_recErased = _out1180;
                    _1798_recIdents = _out1181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1795_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1796_recOwned;
                    isErased = _1797_recErased;
                    readIdents = _1798_recIdents;
                  }
                } else if (_source63.is_Multiset) {
                  DAST._IType _1799___mcc_h939 = _source63.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1800_recursiveGen;
                    bool _1801_recOwned;
                    bool _1802_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1803_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1182;
                    bool _out1183;
                    bool _out1184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1185;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1182, out _out1183, out _out1184, out _out1185);
                    _1800_recursiveGen = _out1182;
                    _1801_recOwned = _out1183;
                    _1802_recErased = _out1184;
                    _1803_recIdents = _out1185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1800_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1801_recOwned;
                    isErased = _1802_recErased;
                    readIdents = _1803_recIdents;
                  }
                } else if (_source63.is_Map) {
                  DAST._IType _1804___mcc_h941 = _source63.dtor_key;
                  DAST._IType _1805___mcc_h942 = _source63.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1806_recursiveGen;
                    bool _1807_recOwned;
                    bool _1808_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1186;
                    bool _out1187;
                    bool _out1188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1189;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1186, out _out1187, out _out1188, out _out1189);
                    _1806_recursiveGen = _out1186;
                    _1807_recOwned = _out1187;
                    _1808_recErased = _out1188;
                    _1809_recIdents = _out1189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1806_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1807_recOwned;
                    isErased = _1808_recErased;
                    readIdents = _1809_recIdents;
                  }
                } else if (_source63.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1810___mcc_h945 = _source63.dtor_args;
                  DAST._IType _1811___mcc_h946 = _source63.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1812_recursiveGen;
                    bool _1813_recOwned;
                    bool _1814_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1190;
                    bool _out1191;
                    bool _out1192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1190, out _out1191, out _out1192, out _out1193);
                    _1812_recursiveGen = _out1190;
                    _1813_recOwned = _out1191;
                    _1814_recErased = _out1192;
                    _1815_recIdents = _out1193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1812_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1813_recOwned;
                    isErased = _1814_recErased;
                    readIdents = _1815_recIdents;
                  }
                } else if (_source63.is_Primitive) {
                  DAST._IPrimitive _1816___mcc_h949 = _source63.dtor_Primitive_a0;
                  DAST._IPrimitive _source65 = _1816___mcc_h949;
                  if (_source65.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1817_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1194;
                      _out1194 = DCOMP.COMP.GenType(_503_fromTpe, true, false);
                      _1817_rhsType = _out1194;
                      Dafny.ISequence<Dafny.Rune> _1818_recursiveGen;
                      bool _1819___v56;
                      bool _1820___v57;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1821_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1195;
                      bool _out1196;
                      bool _out1197;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1198;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, true, out _out1195, out _out1196, out _out1197, out _out1198);
                      _1818_recursiveGen = _out1195;
                      _1819___v56 = _out1196;
                      _1820___v57 = _out1197;
                      _1821_recIdents = _out1198;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1818_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1821_recIdents;
                    }
                  } else if (_source65.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1822_recursiveGen;
                      bool _1823_recOwned;
                      bool _1824_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1199;
                      bool _out1200;
                      bool _out1201;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1199, out _out1200, out _out1201, out _out1202);
                      _1822_recursiveGen = _out1199;
                      _1823_recOwned = _out1200;
                      _1824_recErased = _out1201;
                      _1825_recIdents = _out1202;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1822_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1823_recOwned;
                      isErased = _1824_recErased;
                      readIdents = _1825_recIdents;
                    }
                  } else if (_source65.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1826_recursiveGen;
                      bool _1827_recOwned;
                      bool _1828_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1829_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1203;
                      bool _out1204;
                      bool _out1205;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1206;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1203, out _out1204, out _out1205, out _out1206);
                      _1826_recursiveGen = _out1203;
                      _1827_recOwned = _out1204;
                      _1828_recErased = _out1205;
                      _1829_recIdents = _out1206;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1826_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1827_recOwned;
                      isErased = _1828_recErased;
                      readIdents = _1829_recIdents;
                    }
                  } else if (_source65.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1830_recursiveGen;
                      bool _1831_recOwned;
                      bool _1832_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1833_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1207;
                      bool _out1208;
                      bool _out1209;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1210;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1207, out _out1208, out _out1209, out _out1210);
                      _1830_recursiveGen = _out1207;
                      _1831_recOwned = _out1208;
                      _1832_recErased = _out1209;
                      _1833_recIdents = _out1210;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1830_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1831_recOwned;
                      isErased = _1832_recErased;
                      readIdents = _1833_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1834_recursiveGen;
                      bool _1835_recOwned;
                      bool _1836_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1837_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1211;
                      bool _out1212;
                      bool _out1213;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1211, out _out1212, out _out1213, out _out1214);
                      _1834_recursiveGen = _out1211;
                      _1835_recOwned = _out1212;
                      _1836_recErased = _out1213;
                      _1837_recIdents = _out1214;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1834_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1835_recOwned;
                      isErased = _1836_recErased;
                      readIdents = _1837_recIdents;
                    }
                  }
                } else if (_source63.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1838___mcc_h951 = _source63.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1839_recursiveGen;
                    bool _1840_recOwned;
                    bool _1841_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1842_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1215;
                    bool _out1216;
                    bool _out1217;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1218;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1215, out _out1216, out _out1217, out _out1218);
                    _1839_recursiveGen = _out1215;
                    _1840_recOwned = _out1216;
                    _1841_recErased = _out1217;
                    _1842_recIdents = _out1218;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1839_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1840_recOwned;
                    isErased = _1841_recErased;
                    readIdents = _1842_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1843___mcc_h953 = _source63.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1844_recursiveGen;
                    bool _1845_recOwned;
                    bool _1846_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1847_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1219;
                    bool _out1220;
                    bool _out1221;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1222;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1219, out _out1220, out _out1221, out _out1222);
                    _1844_recursiveGen = _out1219;
                    _1845_recOwned = _out1220;
                    _1846_recErased = _out1221;
                    _1847_recIdents = _out1222;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1844_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1845_recOwned;
                    isErased = _1846_recErased;
                    readIdents = _1847_recIdents;
                  }
                }
              }
            } else if (_source28.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1848___mcc_h955 = _source28.dtor_Passthrough_a0;
              DAST._IType _source66 = _510___mcc_h238;
              if (_source66.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1849___mcc_h959 = _source66.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1850___mcc_h960 = _source66.dtor_typeArgs;
                DAST._IResolvedType _1851___mcc_h961 = _source66.dtor_resolved;
                DAST._IResolvedType _source67 = _1851___mcc_h961;
                if (_source67.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1852___mcc_h965 = _source67.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1853_recursiveGen;
                    bool _1854_recOwned;
                    bool _1855_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1856_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1223;
                    bool _out1224;
                    bool _out1225;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1223, out _out1224, out _out1225, out _out1226);
                    _1853_recursiveGen = _out1223;
                    _1854_recOwned = _out1224;
                    _1855_recErased = _out1225;
                    _1856_recIdents = _out1226;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1853_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1854_recOwned;
                    isErased = _1855_recErased;
                    readIdents = _1856_recIdents;
                  }
                } else if (_source67.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1857___mcc_h967 = _source67.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1858_recursiveGen;
                    bool _1859_recOwned;
                    bool _1860_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1227;
                    bool _out1228;
                    bool _out1229;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1230;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1227, out _out1228, out _out1229, out _out1230);
                    _1858_recursiveGen = _out1227;
                    _1859_recOwned = _out1228;
                    _1860_recErased = _out1229;
                    _1861_recIdents = _out1230;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1858_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1859_recOwned;
                    isErased = _1860_recErased;
                    readIdents = _1861_recIdents;
                  }
                } else {
                  DAST._IType _1862___mcc_h969 = _source67.dtor_Newtype_a0;
                  DAST._IType _1863_b = _1862___mcc_h969;
                  {
                    if (object.Equals(_503_fromTpe, _1863_b)) {
                      Dafny.ISequence<Dafny.Rune> _1864_recursiveGen;
                      bool _1865_recOwned;
                      bool _1866_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1231;
                      bool _out1232;
                      bool _out1233;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1234;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1231, out _out1232, out _out1233, out _out1234);
                      _1864_recursiveGen = _out1231;
                      _1865_recOwned = _out1232;
                      _1866_recErased = _out1233;
                      _1867_recIdents = _out1234;
                      Dafny.ISequence<Dafny.Rune> _1868_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1235;
                      _out1235 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1868_rhsType = _out1235;
                      Dafny.ISequence<Dafny.Rune> _1869_uneraseFn;
                      _1869_uneraseFn = ((_1865_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1868_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1869_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1864_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1865_recOwned;
                      isErased = false;
                      readIdents = _1867_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1236;
                      bool _out1237;
                      bool _out1238;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1239;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1863_b), _1863_b, _502_toTpe), selfIdent, @params, mustOwn, out _out1236, out _out1237, out _out1238, out _out1239);
                      s = _out1236;
                      isOwned = _out1237;
                      isErased = _out1238;
                      readIdents = _out1239;
                    }
                  }
                }
              } else if (_source66.is_Nullable) {
                DAST._IType _1870___mcc_h971 = _source66.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1871_recursiveGen;
                  bool _1872_recOwned;
                  bool _1873_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1240;
                  bool _out1241;
                  bool _out1242;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1240, out _out1241, out _out1242, out _out1243);
                  _1871_recursiveGen = _out1240;
                  _1872_recOwned = _out1241;
                  _1873_recErased = _out1242;
                  _1874_recIdents = _out1243;
                  if (!(_1872_recOwned)) {
                    _1871_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1871_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1871_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1873_recErased;
                  readIdents = _1874_recIdents;
                }
              } else if (_source66.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1875___mcc_h973 = _source66.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1876_recursiveGen;
                  bool _1877_recOwned;
                  bool _1878_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1244;
                  bool _out1245;
                  bool _out1246;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1244, out _out1245, out _out1246, out _out1247);
                  _1876_recursiveGen = _out1244;
                  _1877_recOwned = _out1245;
                  _1878_recErased = _out1246;
                  _1879_recIdents = _out1247;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1876_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1877_recOwned;
                  isErased = _1878_recErased;
                  readIdents = _1879_recIdents;
                }
              } else if (_source66.is_Array) {
                DAST._IType _1880___mcc_h975 = _source66.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1881_recursiveGen;
                  bool _1882_recOwned;
                  bool _1883_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1248;
                  bool _out1249;
                  bool _out1250;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1248, out _out1249, out _out1250, out _out1251);
                  _1881_recursiveGen = _out1248;
                  _1882_recOwned = _out1249;
                  _1883_recErased = _out1250;
                  _1884_recIdents = _out1251;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1881_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1882_recOwned;
                  isErased = _1883_recErased;
                  readIdents = _1884_recIdents;
                }
              } else if (_source66.is_Seq) {
                DAST._IType _1885___mcc_h977 = _source66.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1886_recursiveGen;
                  bool _1887_recOwned;
                  bool _1888_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1889_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1252;
                  bool _out1253;
                  bool _out1254;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1255;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1252, out _out1253, out _out1254, out _out1255);
                  _1886_recursiveGen = _out1252;
                  _1887_recOwned = _out1253;
                  _1888_recErased = _out1254;
                  _1889_recIdents = _out1255;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1886_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1887_recOwned;
                  isErased = _1888_recErased;
                  readIdents = _1889_recIdents;
                }
              } else if (_source66.is_Set) {
                DAST._IType _1890___mcc_h979 = _source66.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1891_recursiveGen;
                  bool _1892_recOwned;
                  bool _1893_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1894_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1256;
                  bool _out1257;
                  bool _out1258;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1256, out _out1257, out _out1258, out _out1259);
                  _1891_recursiveGen = _out1256;
                  _1892_recOwned = _out1257;
                  _1893_recErased = _out1258;
                  _1894_recIdents = _out1259;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1891_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1892_recOwned;
                  isErased = _1893_recErased;
                  readIdents = _1894_recIdents;
                }
              } else if (_source66.is_Multiset) {
                DAST._IType _1895___mcc_h981 = _source66.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1896_recursiveGen;
                  bool _1897_recOwned;
                  bool _1898_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1899_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1260;
                  bool _out1261;
                  bool _out1262;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1263;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1260, out _out1261, out _out1262, out _out1263);
                  _1896_recursiveGen = _out1260;
                  _1897_recOwned = _out1261;
                  _1898_recErased = _out1262;
                  _1899_recIdents = _out1263;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1896_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1897_recOwned;
                  isErased = _1898_recErased;
                  readIdents = _1899_recIdents;
                }
              } else if (_source66.is_Map) {
                DAST._IType _1900___mcc_h983 = _source66.dtor_key;
                DAST._IType _1901___mcc_h984 = _source66.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1902_recursiveGen;
                  bool _1903_recOwned;
                  bool _1904_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1905_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1264;
                  bool _out1265;
                  bool _out1266;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1267;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1264, out _out1265, out _out1266, out _out1267);
                  _1902_recursiveGen = _out1264;
                  _1903_recOwned = _out1265;
                  _1904_recErased = _out1266;
                  _1905_recIdents = _out1267;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1902_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1903_recOwned;
                  isErased = _1904_recErased;
                  readIdents = _1905_recIdents;
                }
              } else if (_source66.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1906___mcc_h987 = _source66.dtor_args;
                DAST._IType _1907___mcc_h988 = _source66.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1908_recursiveGen;
                  bool _1909_recOwned;
                  bool _1910_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1911_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1268;
                  bool _out1269;
                  bool _out1270;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1268, out _out1269, out _out1270, out _out1271);
                  _1908_recursiveGen = _out1268;
                  _1909_recOwned = _out1269;
                  _1910_recErased = _out1270;
                  _1911_recIdents = _out1271;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1908_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1909_recOwned;
                  isErased = _1910_recErased;
                  readIdents = _1911_recIdents;
                }
              } else if (_source66.is_Primitive) {
                DAST._IPrimitive _1912___mcc_h991 = _source66.dtor_Primitive_a0;
                DAST._IPrimitive _source68 = _1912___mcc_h991;
                if (_source68.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1913_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1272;
                    _out1272 = DCOMP.COMP.GenType(_503_fromTpe, true, false);
                    _1913_rhsType = _out1272;
                    Dafny.ISequence<Dafny.Rune> _1914_recursiveGen;
                    bool _1915___v52;
                    bool _1916___v53;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1917_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1273;
                    bool _out1274;
                    bool _out1275;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1276;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, true, out _out1273, out _out1274, out _out1275, out _out1276);
                    _1914_recursiveGen = _out1273;
                    _1915___v52 = _out1274;
                    _1916___v53 = _out1275;
                    _1917_recIdents = _out1276;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1914_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1917_recIdents;
                  }
                } else if (_source68.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1918_recursiveGen;
                    bool _1919_recOwned;
                    bool _1920_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1921_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1277;
                    bool _out1278;
                    bool _out1279;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1277, out _out1278, out _out1279, out _out1280);
                    _1918_recursiveGen = _out1277;
                    _1919_recOwned = _out1278;
                    _1920_recErased = _out1279;
                    _1921_recIdents = _out1280;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1918_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1919_recOwned;
                    isErased = _1920_recErased;
                    readIdents = _1921_recIdents;
                  }
                } else if (_source68.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1922_recursiveGen;
                    bool _1923_recOwned;
                    bool _1924_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1925_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1281;
                    bool _out1282;
                    bool _out1283;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1281, out _out1282, out _out1283, out _out1284);
                    _1922_recursiveGen = _out1281;
                    _1923_recOwned = _out1282;
                    _1924_recErased = _out1283;
                    _1925_recIdents = _out1284;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1922_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1923_recOwned;
                    isErased = _1924_recErased;
                    readIdents = _1925_recIdents;
                  }
                } else if (_source68.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1926_recursiveGen;
                    bool _1927_recOwned;
                    bool _1928_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1929_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1285;
                    bool _out1286;
                    bool _out1287;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1288;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1285, out _out1286, out _out1287, out _out1288);
                    _1926_recursiveGen = _out1285;
                    _1927_recOwned = _out1286;
                    _1928_recErased = _out1287;
                    _1929_recIdents = _out1288;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1926_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1927_recOwned;
                    isErased = _1928_recErased;
                    readIdents = _1929_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _1930_recursiveGen;
                    bool _1931_recOwned;
                    bool _1932_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1933_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1289;
                    bool _out1290;
                    bool _out1291;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1289, out _out1290, out _out1291, out _out1292);
                    _1930_recursiveGen = _out1289;
                    _1931_recOwned = _out1290;
                    _1932_recErased = _out1291;
                    _1933_recIdents = _out1292;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1930_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1931_recOwned;
                    isErased = _1932_recErased;
                    readIdents = _1933_recIdents;
                  }
                }
              } else if (_source66.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1934___mcc_h993 = _source66.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1935_recursiveGen;
                  bool _1936___v60;
                  bool _1937___v61;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1938_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1293;
                  bool _out1294;
                  bool _out1295;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1296;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, true, out _out1293, out _out1294, out _out1295, out _out1296);
                  _1935_recursiveGen = _out1293;
                  _1936___v60 = _out1294;
                  _1937___v61 = _out1295;
                  _1938_recIdents = _out1296;
                  Dafny.ISequence<Dafny.Rune> _1939_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1297;
                  _out1297 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                  _1939_toTpeGen = _out1297;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _1935_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _1939_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _1938_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1940___mcc_h995 = _source66.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1941_recursiveGen;
                  bool _1942_recOwned;
                  bool _1943_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1298;
                  bool _out1299;
                  bool _out1300;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1298, out _out1299, out _out1300, out _out1301);
                  _1941_recursiveGen = _out1298;
                  _1942_recOwned = _out1299;
                  _1943_recErased = _out1300;
                  _1944_recIdents = _out1301;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1941_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1942_recOwned;
                  isErased = _1943_recErased;
                  readIdents = _1944_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _1945___mcc_h997 = _source28.dtor_TypeArg_a0;
              DAST._IType _source69 = _510___mcc_h238;
              if (_source69.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1946___mcc_h1001 = _source69.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1947___mcc_h1002 = _source69.dtor_typeArgs;
                DAST._IResolvedType _1948___mcc_h1003 = _source69.dtor_resolved;
                DAST._IResolvedType _source70 = _1948___mcc_h1003;
                if (_source70.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1949___mcc_h1007 = _source70.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1950_recursiveGen;
                    bool _1951_recOwned;
                    bool _1952_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1953_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1302;
                    bool _out1303;
                    bool _out1304;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1302, out _out1303, out _out1304, out _out1305);
                    _1950_recursiveGen = _out1302;
                    _1951_recOwned = _out1303;
                    _1952_recErased = _out1304;
                    _1953_recIdents = _out1305;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1950_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1951_recOwned;
                    isErased = _1952_recErased;
                    readIdents = _1953_recIdents;
                  }
                } else if (_source70.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1954___mcc_h1009 = _source70.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1955_recursiveGen;
                    bool _1956_recOwned;
                    bool _1957_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1958_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1306;
                    bool _out1307;
                    bool _out1308;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1309;
                    DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1306, out _out1307, out _out1308, out _out1309);
                    _1955_recursiveGen = _out1306;
                    _1956_recOwned = _out1307;
                    _1957_recErased = _out1308;
                    _1958_recIdents = _out1309;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1955_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1956_recOwned;
                    isErased = _1957_recErased;
                    readIdents = _1958_recIdents;
                  }
                } else {
                  DAST._IType _1959___mcc_h1011 = _source70.dtor_Newtype_a0;
                  DAST._IType _1960_b = _1959___mcc_h1011;
                  {
                    if (object.Equals(_503_fromTpe, _1960_b)) {
                      Dafny.ISequence<Dafny.Rune> _1961_recursiveGen;
                      bool _1962_recOwned;
                      bool _1963_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1310;
                      bool _out1311;
                      bool _out1312;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
                      DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1310, out _out1311, out _out1312, out _out1313);
                      _1961_recursiveGen = _out1310;
                      _1962_recOwned = _out1311;
                      _1963_recErased = _out1312;
                      _1964_recIdents = _out1313;
                      Dafny.ISequence<Dafny.Rune> _1965_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1314;
                      _out1314 = DCOMP.COMP.GenType(_502_toTpe, true, false);
                      _1965_rhsType = _out1314;
                      Dafny.ISequence<Dafny.Rune> _1966_uneraseFn;
                      _1966_uneraseFn = ((_1962_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1965_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1966_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1961_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1962_recOwned;
                      isErased = false;
                      readIdents = _1964_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1315;
                      bool _out1316;
                      bool _out1317;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1318;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_504_expr, _503_fromTpe, _1960_b), _1960_b, _502_toTpe), selfIdent, @params, mustOwn, out _out1315, out _out1316, out _out1317, out _out1318);
                      s = _out1315;
                      isOwned = _out1316;
                      isErased = _out1317;
                      readIdents = _out1318;
                    }
                  }
                }
              } else if (_source69.is_Nullable) {
                DAST._IType _1967___mcc_h1013 = _source69.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1968_recursiveGen;
                  bool _1969_recOwned;
                  bool _1970_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1971_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1319;
                  bool _out1320;
                  bool _out1321;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1319, out _out1320, out _out1321, out _out1322);
                  _1968_recursiveGen = _out1319;
                  _1969_recOwned = _out1320;
                  _1970_recErased = _out1321;
                  _1971_recIdents = _out1322;
                  if (!(_1969_recOwned)) {
                    _1968_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1968_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1968_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1970_recErased;
                  readIdents = _1971_recIdents;
                }
              } else if (_source69.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1972___mcc_h1015 = _source69.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1973_recursiveGen;
                  bool _1974_recOwned;
                  bool _1975_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1976_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1323;
                  bool _out1324;
                  bool _out1325;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1323, out _out1324, out _out1325, out _out1326);
                  _1973_recursiveGen = _out1323;
                  _1974_recOwned = _out1324;
                  _1975_recErased = _out1325;
                  _1976_recIdents = _out1326;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1973_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1974_recOwned;
                  isErased = _1975_recErased;
                  readIdents = _1976_recIdents;
                }
              } else if (_source69.is_Array) {
                DAST._IType _1977___mcc_h1017 = _source69.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1978_recursiveGen;
                  bool _1979_recOwned;
                  bool _1980_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1981_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1327;
                  bool _out1328;
                  bool _out1329;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1330;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1327, out _out1328, out _out1329, out _out1330);
                  _1978_recursiveGen = _out1327;
                  _1979_recOwned = _out1328;
                  _1980_recErased = _out1329;
                  _1981_recIdents = _out1330;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1978_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1979_recOwned;
                  isErased = _1980_recErased;
                  readIdents = _1981_recIdents;
                }
              } else if (_source69.is_Seq) {
                DAST._IType _1982___mcc_h1019 = _source69.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1983_recursiveGen;
                  bool _1984_recOwned;
                  bool _1985_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1986_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1331;
                  bool _out1332;
                  bool _out1333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1331, out _out1332, out _out1333, out _out1334);
                  _1983_recursiveGen = _out1331;
                  _1984_recOwned = _out1332;
                  _1985_recErased = _out1333;
                  _1986_recIdents = _out1334;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1983_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1984_recOwned;
                  isErased = _1985_recErased;
                  readIdents = _1986_recIdents;
                }
              } else if (_source69.is_Set) {
                DAST._IType _1987___mcc_h1021 = _source69.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1988_recursiveGen;
                  bool _1989_recOwned;
                  bool _1990_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1991_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1335;
                  bool _out1336;
                  bool _out1337;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1335, out _out1336, out _out1337, out _out1338);
                  _1988_recursiveGen = _out1335;
                  _1989_recOwned = _out1336;
                  _1990_recErased = _out1337;
                  _1991_recIdents = _out1338;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1988_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1989_recOwned;
                  isErased = _1990_recErased;
                  readIdents = _1991_recIdents;
                }
              } else if (_source69.is_Multiset) {
                DAST._IType _1992___mcc_h1023 = _source69.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1993_recursiveGen;
                  bool _1994_recOwned;
                  bool _1995_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1339;
                  bool _out1340;
                  bool _out1341;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1342;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1339, out _out1340, out _out1341, out _out1342);
                  _1993_recursiveGen = _out1339;
                  _1994_recOwned = _out1340;
                  _1995_recErased = _out1341;
                  _1996_recIdents = _out1342;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1993_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1994_recOwned;
                  isErased = _1995_recErased;
                  readIdents = _1996_recIdents;
                }
              } else if (_source69.is_Map) {
                DAST._IType _1997___mcc_h1025 = _source69.dtor_key;
                DAST._IType _1998___mcc_h1026 = _source69.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1999_recursiveGen;
                  bool _2000_recOwned;
                  bool _2001_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2002_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1343;
                  bool _out1344;
                  bool _out1345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1346;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1343, out _out1344, out _out1345, out _out1346);
                  _1999_recursiveGen = _out1343;
                  _2000_recOwned = _out1344;
                  _2001_recErased = _out1345;
                  _2002_recIdents = _out1346;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1999_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2000_recOwned;
                  isErased = _2001_recErased;
                  readIdents = _2002_recIdents;
                }
              } else if (_source69.is_Arrow) {
                Dafny.ISequence<DAST._IType> _2003___mcc_h1029 = _source69.dtor_args;
                DAST._IType _2004___mcc_h1030 = _source69.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _2005_recursiveGen;
                  bool _2006_recOwned;
                  bool _2007_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2008_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1347;
                  bool _out1348;
                  bool _out1349;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1350;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1347, out _out1348, out _out1349, out _out1350);
                  _2005_recursiveGen = _out1347;
                  _2006_recOwned = _out1348;
                  _2007_recErased = _out1349;
                  _2008_recIdents = _out1350;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2005_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2006_recOwned;
                  isErased = _2007_recErased;
                  readIdents = _2008_recIdents;
                }
              } else if (_source69.is_Primitive) {
                DAST._IPrimitive _2009___mcc_h1033 = _source69.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2010_recursiveGen;
                  bool _2011_recOwned;
                  bool _2012_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1351;
                  bool _out1352;
                  bool _out1353;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1351, out _out1352, out _out1353, out _out1354);
                  _2010_recursiveGen = _out1351;
                  _2011_recOwned = _out1352;
                  _2012_recErased = _out1353;
                  _2013_recIdents = _out1354;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2010_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2011_recOwned;
                  isErased = _2012_recErased;
                  readIdents = _2013_recIdents;
                }
              } else if (_source69.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _2014___mcc_h1035 = _source69.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2015_recursiveGen;
                  bool _2016_recOwned;
                  bool _2017_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2018_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1355;
                  bool _out1356;
                  bool _out1357;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1358;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1355, out _out1356, out _out1357, out _out1358);
                  _2015_recursiveGen = _out1355;
                  _2016_recOwned = _out1356;
                  _2017_recErased = _out1357;
                  _2018_recIdents = _out1358;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2015_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2016_recOwned;
                  isErased = _2017_recErased;
                  readIdents = _2018_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _2019___mcc_h1037 = _source69.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2020_recursiveGen;
                  bool _2021_recOwned;
                  bool _2022_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2023_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1359;
                  bool _out1360;
                  bool _out1361;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
                  DCOMP.COMP.GenExpr(_504_expr, selfIdent, @params, mustOwn, out _out1359, out _out1360, out _out1361, out _out1362);
                  _2020_recursiveGen = _out1359;
                  _2021_recOwned = _out1360;
                  _2022_recErased = _out1361;
                  _2023_recIdents = _out1362;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2020_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2021_recOwned;
                  isErased = _2022_recErased;
                  readIdents = _2023_recIdents;
                }
              }
            }
          }
        }
      } else if (_source21.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _2024___mcc_h22 = _source21.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2025_exprs = _2024___mcc_h22;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2026_generatedValues;
          _2026_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2027_i;
          _2027_i = BigInteger.Zero;
          bool _2028_allErased;
          _2028_allErased = true;
          while ((_2027_i) < (new BigInteger((_2025_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2029_recursiveGen;
            bool _2030___v63;
            bool _2031_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2032_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1363;
            bool _out1364;
            bool _out1365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1366;
            DCOMP.COMP.GenExpr((_2025_exprs).Select(_2027_i), selfIdent, @params, true, out _out1363, out _out1364, out _out1365, out _out1366);
            _2029_recursiveGen = _out1363;
            _2030___v63 = _out1364;
            _2031_isErased = _out1365;
            _2032_recIdents = _out1366;
            _2028_allErased = (_2028_allErased) && (_2031_isErased);
            _2026_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2026_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2029_recursiveGen, _2031_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2032_recIdents);
            _2027_i = (_2027_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2027_i = BigInteger.Zero;
          while ((_2027_i) < (new BigInteger((_2026_generatedValues).Count))) {
            if ((_2027_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2033_gen;
            _2033_gen = ((_2026_generatedValues).Select(_2027_i)).dtor__0;
            if ((((_2026_generatedValues).Select(_2027_i)).dtor__1) && (!(_2028_allErased))) {
              _2033_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2033_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2033_gen);
            _2027_i = (_2027_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _2028_allErased;
        }
      } else if (_source21.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _2034___mcc_h23 = _source21.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2035_exprs = _2034___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2036_generatedValues;
          _2036_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2037_i;
          _2037_i = BigInteger.Zero;
          bool _2038_allErased;
          _2038_allErased = true;
          while ((_2037_i) < (new BigInteger((_2035_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2039_recursiveGen;
            bool _2040___v64;
            bool _2041_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2042_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1367;
            bool _out1368;
            bool _out1369;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
            DCOMP.COMP.GenExpr((_2035_exprs).Select(_2037_i), selfIdent, @params, true, out _out1367, out _out1368, out _out1369, out _out1370);
            _2039_recursiveGen = _out1367;
            _2040___v64 = _out1368;
            _2041_isErased = _out1369;
            _2042_recIdents = _out1370;
            _2038_allErased = (_2038_allErased) && (_2041_isErased);
            _2036_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2036_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2039_recursiveGen, _2041_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2042_recIdents);
            _2037_i = (_2037_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2037_i = BigInteger.Zero;
          while ((_2037_i) < (new BigInteger((_2036_generatedValues).Count))) {
            if ((_2037_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2043_gen;
            _2043_gen = ((_2036_generatedValues).Select(_2037_i)).dtor__0;
            if ((((_2036_generatedValues).Select(_2037_i)).dtor__1) && (!(_2038_allErased))) {
              _2043_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2043_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2043_gen);
            _2037_i = (_2037_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashSet<_>>()"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_This) {
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source71 = selfIdent;
          if (_source71.is_Some) {
            Dafny.ISequence<Dafny.Rune> _2044___mcc_h1039 = _source71.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _2045_id = _2044___mcc_h1039;
            {
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(_2045_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                isOwned = true;
              } else {
                if ((_2045_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
                } else {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2045_id);
                }
                isOwned = false;
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2045_id);
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
      } else if (_source21.is_Ite) {
        DAST._IExpression _2046___mcc_h24 = _source21.dtor_cond;
        DAST._IExpression _2047___mcc_h25 = _source21.dtor_thn;
        DAST._IExpression _2048___mcc_h26 = _source21.dtor_els;
        DAST._IExpression _2049_f = _2048___mcc_h26;
        DAST._IExpression _2050_t = _2047___mcc_h25;
        DAST._IExpression _2051_cond = _2046___mcc_h24;
        {
          Dafny.ISequence<Dafny.Rune> _2052_condString;
          bool _2053___v65;
          bool _2054_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2055_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1371;
          bool _out1372;
          bool _out1373;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
          DCOMP.COMP.GenExpr(_2051_cond, selfIdent, @params, true, out _out1371, out _out1372, out _out1373, out _out1374);
          _2052_condString = _out1371;
          _2053___v65 = _out1372;
          _2054_condErased = _out1373;
          _2055_recIdentsCond = _out1374;
          if (!(_2054_condErased)) {
            _2052_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2052_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2056___v66;
          bool _2057_tHasToBeOwned;
          bool _2058___v67;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2059___v68;
          Dafny.ISequence<Dafny.Rune> _out1375;
          bool _out1376;
          bool _out1377;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1378;
          DCOMP.COMP.GenExpr(_2050_t, selfIdent, @params, mustOwn, out _out1375, out _out1376, out _out1377, out _out1378);
          _2056___v66 = _out1375;
          _2057_tHasToBeOwned = _out1376;
          _2058___v67 = _out1377;
          _2059___v68 = _out1378;
          Dafny.ISequence<Dafny.Rune> _2060_fString;
          bool _2061_fOwned;
          bool _2062_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2063_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1379;
          bool _out1380;
          bool _out1381;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1382;
          DCOMP.COMP.GenExpr(_2049_f, selfIdent, @params, _2057_tHasToBeOwned, out _out1379, out _out1380, out _out1381, out _out1382);
          _2060_fString = _out1379;
          _2061_fOwned = _out1380;
          _2062_fErased = _out1381;
          _2063_recIdentsF = _out1382;
          Dafny.ISequence<Dafny.Rune> _2064_tString;
          bool _2065___v69;
          bool _2066_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2067_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1383;
          bool _out1384;
          bool _out1385;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1386;
          DCOMP.COMP.GenExpr(_2050_t, selfIdent, @params, _2061_fOwned, out _out1383, out _out1384, out _out1385, out _out1386);
          _2064_tString = _out1383;
          _2065___v69 = _out1384;
          _2066_tErased = _out1385;
          _2067_recIdentsT = _out1386;
          if ((!(_2062_fErased)) || (!(_2066_tErased))) {
            if (_2062_fErased) {
              _2060_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2060_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2066_tErased) {
              _2064_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2064_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _2052_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2064_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _2060_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _2061_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2055_recIdentsCond, _2067_recIdentsT), _2063_recIdentsF);
          isErased = (_2062_fErased) || (_2066_tErased);
        }
      } else if (_source21.is_UnOp) {
        DAST._IUnaryOp _2068___mcc_h27 = _source21.dtor_unOp;
        DAST._IExpression _2069___mcc_h28 = _source21.dtor_expr;
        DAST._IUnaryOp _source72 = _2068___mcc_h27;
        if (_source72.is_Not) {
          DAST._IExpression _2070_e = _2069___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2071_recursiveGen;
            bool _2072___v70;
            bool _2073_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2074_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1387;
            bool _out1388;
            bool _out1389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1390;
            DCOMP.COMP.GenExpr(_2070_e, selfIdent, @params, true, out _out1387, out _out1388, out _out1389, out _out1390);
            _2071_recursiveGen = _out1387;
            _2072___v70 = _out1388;
            _2073_recErased = _out1389;
            _2074_recIdents = _out1390;
            if (!(_2073_recErased)) {
              _2071_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2071_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _2071_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2074_recIdents;
            isErased = true;
          }
        } else if (_source72.is_BitwiseNot) {
          DAST._IExpression _2075_e = _2069___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2076_recursiveGen;
            bool _2077___v71;
            bool _2078_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2079_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1391;
            bool _out1392;
            bool _out1393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
            DCOMP.COMP.GenExpr(_2075_e, selfIdent, @params, true, out _out1391, out _out1392, out _out1393, out _out1394);
            _2076_recursiveGen = _out1391;
            _2077___v71 = _out1392;
            _2078_recErased = _out1393;
            _2079_recIdents = _out1394;
            if (!(_2078_recErased)) {
              _2076_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2076_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _2076_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2079_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _2080_e = _2069___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2081_recursiveGen;
            bool _2082_recOwned;
            bool _2083_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2084_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1395;
            bool _out1396;
            bool _out1397;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1398;
            DCOMP.COMP.GenExpr(_2080_e, selfIdent, @params, false, out _out1395, out _out1396, out _out1397, out _out1398);
            _2081_recursiveGen = _out1395;
            _2082_recOwned = _out1396;
            _2083_recErased = _out1397;
            _2084_recIdents = _out1398;
            if (!(_2083_recErased)) {
              Dafny.ISequence<Dafny.Rune> _2085_eraseFn;
              _2085_eraseFn = ((_2082_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2081_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2085_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2081_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2081_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len())"));
            isOwned = true;
            readIdents = _2084_recIdents;
            isErased = true;
          }
        }
      } else if (_source21.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _2086___mcc_h29 = _source21.dtor_op;
        DAST._IExpression _2087___mcc_h30 = _source21.dtor_left;
        DAST._IExpression _2088___mcc_h31 = _source21.dtor_right;
        DAST._IExpression _2089_r = _2088___mcc_h31;
        DAST._IExpression _2090_l = _2087___mcc_h30;
        Dafny.ISequence<Dafny.Rune> _2091_op = _2086___mcc_h29;
        {
          Dafny.ISequence<Dafny.Rune> _2092_left;
          bool _2093___v72;
          bool _2094_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2095_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1399;
          bool _out1400;
          bool _out1401;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
          DCOMP.COMP.GenExpr(_2090_l, selfIdent, @params, true, out _out1399, out _out1400, out _out1401, out _out1402);
          _2092_left = _out1399;
          _2093___v72 = _out1400;
          _2094_leftErased = _out1401;
          _2095_recIdentsL = _out1402;
          Dafny.ISequence<Dafny.Rune> _2096_right;
          bool _2097___v73;
          bool _2098_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2099_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1403;
          bool _out1404;
          bool _out1405;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1406;
          DCOMP.COMP.GenExpr(_2089_r, selfIdent, @params, true, out _out1403, out _out1404, out _out1405, out _out1406);
          _2096_right = _out1403;
          _2097___v73 = _out1404;
          _2098_rightErased = _out1405;
          _2099_recIdentsR = _out1406;
          if (!(_2094_leftErased)) {
            _2092_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2092_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_2098_rightErased)) {
            _2096_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2096_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_2091_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _2092_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2096_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_2091_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _2092_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2096_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2092_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2091_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2096_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2095_recIdentsL, _2099_recIdentsR);
          isErased = true;
        }
      } else if (_source21.is_ArrayLen) {
        DAST._IExpression _2100___mcc_h32 = _source21.dtor_expr;
        DAST._IExpression _2101_expr = _2100___mcc_h32;
        {
          Dafny.ISequence<Dafny.Rune> _2102_recursiveGen;
          bool _2103___v74;
          bool _2104_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2105_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1407;
          bool _out1408;
          bool _out1409;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1410;
          DCOMP.COMP.GenExpr(_2101_expr, selfIdent, @params, true, out _out1407, out _out1408, out _out1409, out _out1410);
          _2102_recursiveGen = _out1407;
          _2103___v74 = _out1408;
          _2104_recErased = _out1409;
          _2105_recIdents = _out1410;
          if (!(_2104_recErased)) {
            _2102_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2102_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2102_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())"));
          isOwned = true;
          readIdents = _2105_recIdents;
          isErased = true;
        }
      } else if (_source21.is_Select) {
        DAST._IExpression _2106___mcc_h33 = _source21.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2107___mcc_h34 = _source21.dtor_field;
        bool _2108___mcc_h35 = _source21.dtor_isConstant;
        bool _2109___mcc_h36 = _source21.dtor_onDatatype;
        DAST._IExpression _source73 = _2106___mcc_h33;
        if (_source73.is_Literal) {
          DAST._ILiteral _2110___mcc_h37 = _source73.dtor_Literal_a0;
          bool _2111_isDatatype = _2109___mcc_h36;
          bool _2112_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2113_field = _2107___mcc_h34;
          DAST._IExpression _2114_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2115_onString;
            bool _2116_onOwned;
            bool _2117_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2118_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1411;
            bool _out1412;
            bool _out1413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1414;
            DCOMP.COMP.GenExpr(_2114_on, selfIdent, @params, false, out _out1411, out _out1412, out _out1413, out _out1414);
            _2115_onString = _out1411;
            _2116_onOwned = _out1412;
            _2117_onErased = _out1413;
            _2118_recIdents = _out1414;
            if (!(_2117_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2119_eraseFn;
              _2119_eraseFn = ((_2116_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2115_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2119_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2115_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2111_isDatatype) || (_2112_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2115_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2113_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2112_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2115_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2113_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2118_recIdents;
          }
        } else if (_source73.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2120___mcc_h39 = _source73.dtor_Ident_a0;
          bool _2121_isDatatype = _2109___mcc_h36;
          bool _2122_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2123_field = _2107___mcc_h34;
          DAST._IExpression _2124_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2125_onString;
            bool _2126_onOwned;
            bool _2127_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2128_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1415;
            bool _out1416;
            bool _out1417;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
            DCOMP.COMP.GenExpr(_2124_on, selfIdent, @params, false, out _out1415, out _out1416, out _out1417, out _out1418);
            _2125_onString = _out1415;
            _2126_onOwned = _out1416;
            _2127_onErased = _out1417;
            _2128_recIdents = _out1418;
            if (!(_2127_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2129_eraseFn;
              _2129_eraseFn = ((_2126_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2125_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2129_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2125_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2121_isDatatype) || (_2122_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2125_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2123_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2122_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2125_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2123_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2128_recIdents;
          }
        } else if (_source73.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2130___mcc_h41 = _source73.dtor_Companion_a0;
          bool _2131_isDatatype = _2109___mcc_h36;
          bool _2132_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2133_field = _2107___mcc_h34;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2134_c = _2130___mcc_h41;
          {
            Dafny.ISequence<Dafny.Rune> _2135_onString;
            bool _2136_onOwned;
            bool _2137_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2138_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1419;
            bool _out1420;
            bool _out1421;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1422;
            DCOMP.COMP.GenExpr(DAST.Expression.create_Companion(_2134_c), selfIdent, @params, false, out _out1419, out _out1420, out _out1421, out _out1422);
            _2135_onString = _out1419;
            _2136_onOwned = _out1420;
            _2137_onErased = _out1421;
            _2138_recIdents = _out1422;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2135_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2133_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            isOwned = true;
            isErased = false;
            readIdents = _2138_recIdents;
          }
        } else if (_source73.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2139___mcc_h43 = _source73.dtor_Tuple_a0;
          bool _2140_isDatatype = _2109___mcc_h36;
          bool _2141_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2142_field = _2107___mcc_h34;
          DAST._IExpression _2143_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2144_onString;
            bool _2145_onOwned;
            bool _2146_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2147_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1423;
            bool _out1424;
            bool _out1425;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1426;
            DCOMP.COMP.GenExpr(_2143_on, selfIdent, @params, false, out _out1423, out _out1424, out _out1425, out _out1426);
            _2144_onString = _out1423;
            _2145_onOwned = _out1424;
            _2146_onErased = _out1425;
            _2147_recIdents = _out1426;
            if (!(_2146_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2148_eraseFn;
              _2148_eraseFn = ((_2145_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2144_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2148_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2144_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2140_isDatatype) || (_2141_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2144_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2142_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2141_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2144_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2142_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2147_recIdents;
          }
        } else if (_source73.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2149___mcc_h45 = _source73.dtor_path;
          Dafny.ISequence<DAST._IExpression> _2150___mcc_h46 = _source73.dtor_args;
          bool _2151_isDatatype = _2109___mcc_h36;
          bool _2152_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2153_field = _2107___mcc_h34;
          DAST._IExpression _2154_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2155_onString;
            bool _2156_onOwned;
            bool _2157_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2158_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1427;
            bool _out1428;
            bool _out1429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1430;
            DCOMP.COMP.GenExpr(_2154_on, selfIdent, @params, false, out _out1427, out _out1428, out _out1429, out _out1430);
            _2155_onString = _out1427;
            _2156_onOwned = _out1428;
            _2157_onErased = _out1429;
            _2158_recIdents = _out1430;
            if (!(_2157_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2159_eraseFn;
              _2159_eraseFn = ((_2156_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2155_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2159_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2155_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2151_isDatatype) || (_2152_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2155_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2153_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2152_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2155_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2153_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2158_recIdents;
          }
        } else if (_source73.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _2160___mcc_h49 = _source73.dtor_dims;
          bool _2161_isDatatype = _2109___mcc_h36;
          bool _2162_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2163_field = _2107___mcc_h34;
          DAST._IExpression _2164_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2165_onString;
            bool _2166_onOwned;
            bool _2167_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2168_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1431;
            bool _out1432;
            bool _out1433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1434;
            DCOMP.COMP.GenExpr(_2164_on, selfIdent, @params, false, out _out1431, out _out1432, out _out1433, out _out1434);
            _2165_onString = _out1431;
            _2166_onOwned = _out1432;
            _2167_onErased = _out1433;
            _2168_recIdents = _out1434;
            if (!(_2167_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2169_eraseFn;
              _2169_eraseFn = ((_2166_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2165_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2169_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2165_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2161_isDatatype) || (_2162_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2165_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2163_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2162_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2165_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2163_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2168_recIdents;
          }
        } else if (_source73.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2170___mcc_h51 = _source73.dtor_path;
          Dafny.ISequence<Dafny.Rune> _2171___mcc_h52 = _source73.dtor_variant;
          bool _2172___mcc_h53 = _source73.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2173___mcc_h54 = _source73.dtor_contents;
          bool _2174_isDatatype = _2109___mcc_h36;
          bool _2175_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2176_field = _2107___mcc_h34;
          DAST._IExpression _2177_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2178_onString;
            bool _2179_onOwned;
            bool _2180_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2181_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1435;
            bool _out1436;
            bool _out1437;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1438;
            DCOMP.COMP.GenExpr(_2177_on, selfIdent, @params, false, out _out1435, out _out1436, out _out1437, out _out1438);
            _2178_onString = _out1435;
            _2179_onOwned = _out1436;
            _2180_onErased = _out1437;
            _2181_recIdents = _out1438;
            if (!(_2180_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2182_eraseFn;
              _2182_eraseFn = ((_2179_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2178_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2182_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2178_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2174_isDatatype) || (_2175_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2178_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2176_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2175_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2178_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2176_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2181_recIdents;
          }
        } else if (_source73.is_Convert) {
          DAST._IExpression _2183___mcc_h59 = _source73.dtor_value;
          DAST._IType _2184___mcc_h60 = _source73.dtor_from;
          DAST._IType _2185___mcc_h61 = _source73.dtor_typ;
          bool _2186_isDatatype = _2109___mcc_h36;
          bool _2187_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2188_field = _2107___mcc_h34;
          DAST._IExpression _2189_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2190_onString;
            bool _2191_onOwned;
            bool _2192_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2193_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1439;
            bool _out1440;
            bool _out1441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
            DCOMP.COMP.GenExpr(_2189_on, selfIdent, @params, false, out _out1439, out _out1440, out _out1441, out _out1442);
            _2190_onString = _out1439;
            _2191_onOwned = _out1440;
            _2192_onErased = _out1441;
            _2193_recIdents = _out1442;
            if (!(_2192_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2194_eraseFn;
              _2194_eraseFn = ((_2191_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2190_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2194_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2190_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2186_isDatatype) || (_2187_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2190_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2188_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2187_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2190_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2188_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2193_recIdents;
          }
        } else if (_source73.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2195___mcc_h65 = _source73.dtor_elements;
          bool _2196_isDatatype = _2109___mcc_h36;
          bool _2197_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2198_field = _2107___mcc_h34;
          DAST._IExpression _2199_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2200_onString;
            bool _2201_onOwned;
            bool _2202_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1443;
            bool _out1444;
            bool _out1445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1446;
            DCOMP.COMP.GenExpr(_2199_on, selfIdent, @params, false, out _out1443, out _out1444, out _out1445, out _out1446);
            _2200_onString = _out1443;
            _2201_onOwned = _out1444;
            _2202_onErased = _out1445;
            _2203_recIdents = _out1446;
            if (!(_2202_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2204_eraseFn;
              _2204_eraseFn = ((_2201_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2200_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2204_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2200_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2196_isDatatype) || (_2197_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2200_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2198_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2197_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2200_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2198_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2203_recIdents;
          }
        } else if (_source73.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2205___mcc_h67 = _source73.dtor_elements;
          bool _2206_isDatatype = _2109___mcc_h36;
          bool _2207_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2208_field = _2107___mcc_h34;
          DAST._IExpression _2209_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2210_onString;
            bool _2211_onOwned;
            bool _2212_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2213_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1447;
            bool _out1448;
            bool _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            DCOMP.COMP.GenExpr(_2209_on, selfIdent, @params, false, out _out1447, out _out1448, out _out1449, out _out1450);
            _2210_onString = _out1447;
            _2211_onOwned = _out1448;
            _2212_onErased = _out1449;
            _2213_recIdents = _out1450;
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
        } else if (_source73.is_This) {
          bool _2215_isDatatype = _2109___mcc_h36;
          bool _2216_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2217_field = _2107___mcc_h34;
          DAST._IExpression _2218_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2219_onString;
            bool _2220_onOwned;
            bool _2221_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2222_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1451;
            bool _out1452;
            bool _out1453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1454;
            DCOMP.COMP.GenExpr(_2218_on, selfIdent, @params, false, out _out1451, out _out1452, out _out1453, out _out1454);
            _2219_onString = _out1451;
            _2220_onOwned = _out1452;
            _2221_onErased = _out1453;
            _2222_recIdents = _out1454;
            if (!(_2221_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2223_eraseFn;
              _2223_eraseFn = ((_2220_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2219_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2223_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2219_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2215_isDatatype) || (_2216_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2219_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2217_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2216_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2219_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2217_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2222_recIdents;
          }
        } else if (_source73.is_Ite) {
          DAST._IExpression _2224___mcc_h69 = _source73.dtor_cond;
          DAST._IExpression _2225___mcc_h70 = _source73.dtor_thn;
          DAST._IExpression _2226___mcc_h71 = _source73.dtor_els;
          bool _2227_isDatatype = _2109___mcc_h36;
          bool _2228_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2229_field = _2107___mcc_h34;
          DAST._IExpression _2230_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2231_onString;
            bool _2232_onOwned;
            bool _2233_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2234_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1455;
            bool _out1456;
            bool _out1457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1458;
            DCOMP.COMP.GenExpr(_2230_on, selfIdent, @params, false, out _out1455, out _out1456, out _out1457, out _out1458);
            _2231_onString = _out1455;
            _2232_onOwned = _out1456;
            _2233_onErased = _out1457;
            _2234_recIdents = _out1458;
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
        } else if (_source73.is_UnOp) {
          DAST._IUnaryOp _2236___mcc_h75 = _source73.dtor_unOp;
          DAST._IExpression _2237___mcc_h76 = _source73.dtor_expr;
          bool _2238_isDatatype = _2109___mcc_h36;
          bool _2239_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2240_field = _2107___mcc_h34;
          DAST._IExpression _2241_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2242_onString;
            bool _2243_onOwned;
            bool _2244_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2245_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1459;
            bool _out1460;
            bool _out1461;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
            DCOMP.COMP.GenExpr(_2241_on, selfIdent, @params, false, out _out1459, out _out1460, out _out1461, out _out1462);
            _2242_onString = _out1459;
            _2243_onOwned = _out1460;
            _2244_onErased = _out1461;
            _2245_recIdents = _out1462;
            if (!(_2244_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2246_eraseFn;
              _2246_eraseFn = ((_2243_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2242_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2246_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2242_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2238_isDatatype) || (_2239_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2242_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2240_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2239_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2242_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2240_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2245_recIdents;
          }
        } else if (_source73.is_BinOp) {
          Dafny.ISequence<Dafny.Rune> _2247___mcc_h79 = _source73.dtor_op;
          DAST._IExpression _2248___mcc_h80 = _source73.dtor_left;
          DAST._IExpression _2249___mcc_h81 = _source73.dtor_right;
          bool _2250_isDatatype = _2109___mcc_h36;
          bool _2251_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2252_field = _2107___mcc_h34;
          DAST._IExpression _2253_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2254_onString;
            bool _2255_onOwned;
            bool _2256_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2257_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1463;
            bool _out1464;
            bool _out1465;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1466;
            DCOMP.COMP.GenExpr(_2253_on, selfIdent, @params, false, out _out1463, out _out1464, out _out1465, out _out1466);
            _2254_onString = _out1463;
            _2255_onOwned = _out1464;
            _2256_onErased = _out1465;
            _2257_recIdents = _out1466;
            if (!(_2256_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2258_eraseFn;
              _2258_eraseFn = ((_2255_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2254_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2258_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2254_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2250_isDatatype) || (_2251_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2254_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2252_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2251_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2254_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2252_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2257_recIdents;
          }
        } else if (_source73.is_ArrayLen) {
          DAST._IExpression _2259___mcc_h85 = _source73.dtor_expr;
          bool _2260_isDatatype = _2109___mcc_h36;
          bool _2261_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2262_field = _2107___mcc_h34;
          DAST._IExpression _2263_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2264_onString;
            bool _2265_onOwned;
            bool _2266_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2267_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1467;
            bool _out1468;
            bool _out1469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
            DCOMP.COMP.GenExpr(_2263_on, selfIdent, @params, false, out _out1467, out _out1468, out _out1469, out _out1470);
            _2264_onString = _out1467;
            _2265_onOwned = _out1468;
            _2266_onErased = _out1469;
            _2267_recIdents = _out1470;
            if (!(_2266_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2268_eraseFn;
              _2268_eraseFn = ((_2265_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2264_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2268_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2264_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2260_isDatatype) || (_2261_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2264_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2262_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2261_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2264_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2262_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2267_recIdents;
          }
        } else if (_source73.is_Select) {
          DAST._IExpression _2269___mcc_h87 = _source73.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2270___mcc_h88 = _source73.dtor_field;
          bool _2271___mcc_h89 = _source73.dtor_isConstant;
          bool _2272___mcc_h90 = _source73.dtor_onDatatype;
          bool _2273_isDatatype = _2109___mcc_h36;
          bool _2274_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2275_field = _2107___mcc_h34;
          DAST._IExpression _2276_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2277_onString;
            bool _2278_onOwned;
            bool _2279_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2280_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1471;
            bool _out1472;
            bool _out1473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1474;
            DCOMP.COMP.GenExpr(_2276_on, selfIdent, @params, false, out _out1471, out _out1472, out _out1473, out _out1474);
            _2277_onString = _out1471;
            _2278_onOwned = _out1472;
            _2279_onErased = _out1473;
            _2280_recIdents = _out1474;
            if (!(_2279_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2281_eraseFn;
              _2281_eraseFn = ((_2278_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2277_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2281_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2277_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2273_isDatatype) || (_2274_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2277_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2275_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2274_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2277_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2275_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2280_recIdents;
          }
        } else if (_source73.is_SelectFn) {
          DAST._IExpression _2282___mcc_h95 = _source73.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2283___mcc_h96 = _source73.dtor_field;
          bool _2284___mcc_h97 = _source73.dtor_onDatatype;
          bool _2285___mcc_h98 = _source73.dtor_isStatic;
          BigInteger _2286___mcc_h99 = _source73.dtor_arity;
          bool _2287_isDatatype = _2109___mcc_h36;
          bool _2288_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2289_field = _2107___mcc_h34;
          DAST._IExpression _2290_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2291_onString;
            bool _2292_onOwned;
            bool _2293_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2294_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1475;
            bool _out1476;
            bool _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            DCOMP.COMP.GenExpr(_2290_on, selfIdent, @params, false, out _out1475, out _out1476, out _out1477, out _out1478);
            _2291_onString = _out1475;
            _2292_onOwned = _out1476;
            _2293_onErased = _out1477;
            _2294_recIdents = _out1478;
            if (!(_2293_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2295_eraseFn;
              _2295_eraseFn = ((_2292_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2291_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2295_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2291_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2287_isDatatype) || (_2288_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2291_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2289_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2288_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2291_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2289_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2294_recIdents;
          }
        } else if (_source73.is_Index) {
          DAST._IExpression _2296___mcc_h105 = _source73.dtor_expr;
          DAST._IExpression _2297___mcc_h106 = _source73.dtor_idx;
          bool _2298_isDatatype = _2109___mcc_h36;
          bool _2299_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2300_field = _2107___mcc_h34;
          DAST._IExpression _2301_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2302_onString;
            bool _2303_onOwned;
            bool _2304_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2305_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1479;
            bool _out1480;
            bool _out1481;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1482;
            DCOMP.COMP.GenExpr(_2301_on, selfIdent, @params, false, out _out1479, out _out1480, out _out1481, out _out1482);
            _2302_onString = _out1479;
            _2303_onOwned = _out1480;
            _2304_onErased = _out1481;
            _2305_recIdents = _out1482;
            if (!(_2304_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2306_eraseFn;
              _2306_eraseFn = ((_2303_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2302_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2306_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2302_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2298_isDatatype) || (_2299_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2302_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2300_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2299_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2302_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2300_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2305_recIdents;
          }
        } else if (_source73.is_TupleSelect) {
          DAST._IExpression _2307___mcc_h109 = _source73.dtor_expr;
          BigInteger _2308___mcc_h110 = _source73.dtor_index;
          bool _2309_isDatatype = _2109___mcc_h36;
          bool _2310_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2311_field = _2107___mcc_h34;
          DAST._IExpression _2312_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2313_onString;
            bool _2314_onOwned;
            bool _2315_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2316_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1483;
            bool _out1484;
            bool _out1485;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
            DCOMP.COMP.GenExpr(_2312_on, selfIdent, @params, false, out _out1483, out _out1484, out _out1485, out _out1486);
            _2313_onString = _out1483;
            _2314_onOwned = _out1484;
            _2315_onErased = _out1485;
            _2316_recIdents = _out1486;
            if (!(_2315_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2317_eraseFn;
              _2317_eraseFn = ((_2314_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2313_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2317_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2313_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2309_isDatatype) || (_2310_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2313_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2311_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2310_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2313_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2311_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2316_recIdents;
          }
        } else if (_source73.is_Call) {
          DAST._IExpression _2318___mcc_h113 = _source73.dtor_on;
          Dafny.ISequence<Dafny.Rune> _2319___mcc_h114 = _source73.dtor_name;
          Dafny.ISequence<DAST._IType> _2320___mcc_h115 = _source73.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2321___mcc_h116 = _source73.dtor_args;
          bool _2322_isDatatype = _2109___mcc_h36;
          bool _2323_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2324_field = _2107___mcc_h34;
          DAST._IExpression _2325_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2326_onString;
            bool _2327_onOwned;
            bool _2328_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2329_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1487;
            bool _out1488;
            bool _out1489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1490;
            DCOMP.COMP.GenExpr(_2325_on, selfIdent, @params, false, out _out1487, out _out1488, out _out1489, out _out1490);
            _2326_onString = _out1487;
            _2327_onOwned = _out1488;
            _2328_onErased = _out1489;
            _2329_recIdents = _out1490;
            if (!(_2328_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2330_eraseFn;
              _2330_eraseFn = ((_2327_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2326_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2330_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2326_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2322_isDatatype) || (_2323_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2326_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2324_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2323_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2326_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2324_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2329_recIdents;
          }
        } else if (_source73.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2331___mcc_h121 = _source73.dtor_params;
          DAST._IType _2332___mcc_h122 = _source73.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2333___mcc_h123 = _source73.dtor_body;
          bool _2334_isDatatype = _2109___mcc_h36;
          bool _2335_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2336_field = _2107___mcc_h34;
          DAST._IExpression _2337_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2338_onString;
            bool _2339_onOwned;
            bool _2340_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2341_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1491;
            bool _out1492;
            bool _out1493;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1494;
            DCOMP.COMP.GenExpr(_2337_on, selfIdent, @params, false, out _out1491, out _out1492, out _out1493, out _out1494);
            _2338_onString = _out1491;
            _2339_onOwned = _out1492;
            _2340_onErased = _out1493;
            _2341_recIdents = _out1494;
            if (!(_2340_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2342_eraseFn;
              _2342_eraseFn = ((_2339_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2338_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2342_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2338_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2334_isDatatype) || (_2335_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2338_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2336_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2335_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2338_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2336_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2341_recIdents;
          }
        } else if (_source73.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2343___mcc_h127 = _source73.dtor_name;
          DAST._IType _2344___mcc_h128 = _source73.dtor_typ;
          DAST._IExpression _2345___mcc_h129 = _source73.dtor_value;
          DAST._IExpression _2346___mcc_h130 = _source73.dtor_iifeBody;
          bool _2347_isDatatype = _2109___mcc_h36;
          bool _2348_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2349_field = _2107___mcc_h34;
          DAST._IExpression _2350_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2351_onString;
            bool _2352_onOwned;
            bool _2353_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2354_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1495;
            bool _out1496;
            bool _out1497;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1498;
            DCOMP.COMP.GenExpr(_2350_on, selfIdent, @params, false, out _out1495, out _out1496, out _out1497, out _out1498);
            _2351_onString = _out1495;
            _2352_onOwned = _out1496;
            _2353_onErased = _out1497;
            _2354_recIdents = _out1498;
            if (!(_2353_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2355_eraseFn;
              _2355_eraseFn = ((_2352_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2351_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2355_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2351_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2347_isDatatype) || (_2348_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2351_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2349_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2348_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2351_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2349_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2354_recIdents;
          }
        } else if (_source73.is_Apply) {
          DAST._IExpression _2356___mcc_h135 = _source73.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2357___mcc_h136 = _source73.dtor_args;
          bool _2358_isDatatype = _2109___mcc_h36;
          bool _2359_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2360_field = _2107___mcc_h34;
          DAST._IExpression _2361_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2362_onString;
            bool _2363_onOwned;
            bool _2364_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2365_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1499;
            bool _out1500;
            bool _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            DCOMP.COMP.GenExpr(_2361_on, selfIdent, @params, false, out _out1499, out _out1500, out _out1501, out _out1502);
            _2362_onString = _out1499;
            _2363_onOwned = _out1500;
            _2364_onErased = _out1501;
            _2365_recIdents = _out1502;
            if (!(_2364_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2366_eraseFn;
              _2366_eraseFn = ((_2363_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2362_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2366_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2362_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2358_isDatatype) || (_2359_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2362_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2360_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2359_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2362_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2360_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2365_recIdents;
          }
        } else if (_source73.is_TypeTest) {
          DAST._IExpression _2367___mcc_h139 = _source73.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2368___mcc_h140 = _source73.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2369___mcc_h141 = _source73.dtor_variant;
          bool _2370_isDatatype = _2109___mcc_h36;
          bool _2371_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2372_field = _2107___mcc_h34;
          DAST._IExpression _2373_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2374_onString;
            bool _2375_onOwned;
            bool _2376_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2377_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1503;
            bool _out1504;
            bool _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            DCOMP.COMP.GenExpr(_2373_on, selfIdent, @params, false, out _out1503, out _out1504, out _out1505, out _out1506);
            _2374_onString = _out1503;
            _2375_onOwned = _out1504;
            _2376_onErased = _out1505;
            _2377_recIdents = _out1506;
            if (!(_2376_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2378_eraseFn;
              _2378_eraseFn = ((_2375_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2374_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2378_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2374_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2370_isDatatype) || (_2371_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2374_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2372_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2371_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2374_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2372_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2377_recIdents;
          }
        } else {
          DAST._IType _2379___mcc_h145 = _source73.dtor_typ;
          bool _2380_isDatatype = _2109___mcc_h36;
          bool _2381_isConstant = _2108___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2382_field = _2107___mcc_h34;
          DAST._IExpression _2383_on = _2106___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2384_onString;
            bool _2385_onOwned;
            bool _2386_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2387_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1507;
            bool _out1508;
            bool _out1509;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1510;
            DCOMP.COMP.GenExpr(_2383_on, selfIdent, @params, false, out _out1507, out _out1508, out _out1509, out _out1510);
            _2384_onString = _out1507;
            _2385_onOwned = _out1508;
            _2386_onErased = _out1509;
            _2387_recIdents = _out1510;
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
        }
      } else if (_source21.is_SelectFn) {
        DAST._IExpression _2389___mcc_h147 = _source21.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2390___mcc_h148 = _source21.dtor_field;
        bool _2391___mcc_h149 = _source21.dtor_onDatatype;
        bool _2392___mcc_h150 = _source21.dtor_isStatic;
        BigInteger _2393___mcc_h151 = _source21.dtor_arity;
        BigInteger _2394_arity = _2393___mcc_h151;
        bool _2395_isStatic = _2392___mcc_h150;
        bool _2396_isDatatype = _2391___mcc_h149;
        Dafny.ISequence<Dafny.Rune> _2397_field = _2390___mcc_h148;
        DAST._IExpression _2398_on = _2389___mcc_h147;
        {
          Dafny.ISequence<Dafny.Rune> _2399_onString;
          bool _2400_onOwned;
          bool _2401___v75;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2402_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1511;
          bool _out1512;
          bool _out1513;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1514;
          DCOMP.COMP.GenExpr(_2398_on, selfIdent, @params, false, out _out1511, out _out1512, out _out1513, out _out1514);
          _2399_onString = _out1511;
          _2400_onOwned = _out1512;
          _2401___v75 = _out1513;
          _2402_recIdents = _out1514;
          if (_2395_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2399_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2397_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2399_onString), ((_2400_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _2403_args;
            _2403_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _2404_i;
            _2404_i = BigInteger.Zero;
            while ((_2404_i) < (_2394_arity)) {
              if ((_2404_i).Sign == 1) {
                _2403_args = Dafny.Sequence<Dafny.Rune>.Concat(_2403_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2403_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2403_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_2404_i));
              _2404_i = (_2404_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2403_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _2397_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2403_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = true;
          readIdents = _2402_recIdents;
        }
      } else if (_source21.is_Index) {
        DAST._IExpression _2405___mcc_h152 = _source21.dtor_expr;
        DAST._IExpression _2406___mcc_h153 = _source21.dtor_idx;
        DAST._IExpression _2407_idx = _2406___mcc_h153;
        DAST._IExpression _2408_on = _2405___mcc_h152;
        {
          Dafny.ISequence<Dafny.Rune> _2409_onString;
          bool _2410_onOwned;
          bool _2411_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2412_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1515;
          bool _out1516;
          bool _out1517;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
          DCOMP.COMP.GenExpr(_2408_on, selfIdent, @params, false, out _out1515, out _out1516, out _out1517, out _out1518);
          _2409_onString = _out1515;
          _2410_onOwned = _out1516;
          _2411_onErased = _out1517;
          _2412_recIdents = _out1518;
          if (!(_2411_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2413_eraseFn;
            _2413_eraseFn = ((_2410_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2409_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2413_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2409_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2414_idxString;
          bool _2415___v76;
          bool _2416_idxErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2417_recIdentsIdx;
          Dafny.ISequence<Dafny.Rune> _out1519;
          bool _out1520;
          bool _out1521;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1522;
          DCOMP.COMP.GenExpr(_2407_idx, selfIdent, @params, true, out _out1519, out _out1520, out _out1521, out _out1522);
          _2414_idxString = _out1519;
          _2415___v76 = _out1520;
          _2416_idxErased = _out1521;
          _2417_recIdentsIdx = _out1522;
          if (!(_2416_idxErased)) {
            _2414_idxString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2414_idxString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2409_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[<usize as ::dafny_runtime::NumCast>::from(")), _2414_idxString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = false;
          }
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2412_recIdents, _2417_recIdentsIdx);
        }
      } else if (_source21.is_TupleSelect) {
        DAST._IExpression _2418___mcc_h154 = _source21.dtor_expr;
        BigInteger _2419___mcc_h155 = _source21.dtor_index;
        BigInteger _2420_idx = _2419___mcc_h155;
        DAST._IExpression _2421_on = _2418___mcc_h154;
        {
          Dafny.ISequence<Dafny.Rune> _2422_onString;
          bool _2423___v77;
          bool _2424_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2425_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1523;
          bool _out1524;
          bool _out1525;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1526;
          DCOMP.COMP.GenExpr(_2421_on, selfIdent, @params, false, out _out1523, out _out1524, out _out1525, out _out1526);
          _2422_onString = _out1523;
          _2423___v77 = _out1524;
          _2424_tupErased = _out1525;
          _2425_recIdents = _out1526;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2422_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_2420_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _2424_tupErased;
          readIdents = _2425_recIdents;
        }
      } else if (_source21.is_Call) {
        DAST._IExpression _2426___mcc_h156 = _source21.dtor_on;
        Dafny.ISequence<Dafny.Rune> _2427___mcc_h157 = _source21.dtor_name;
        Dafny.ISequence<DAST._IType> _2428___mcc_h158 = _source21.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2429___mcc_h159 = _source21.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2430_args = _2429___mcc_h159;
        Dafny.ISequence<DAST._IType> _2431_typeArgs = _2428___mcc_h158;
        Dafny.ISequence<Dafny.Rune> _2432_name = _2427___mcc_h157;
        DAST._IExpression _2433_on = _2426___mcc_h156;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2434_typeArgString;
          _2434_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2431_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2435_typeI;
            _2435_typeI = BigInteger.Zero;
            _2434_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_2435_typeI) < (new BigInteger((_2431_typeArgs).Count))) {
              if ((_2435_typeI).Sign == 1) {
                _2434_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2434_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _2436_typeString;
              Dafny.ISequence<Dafny.Rune> _out1527;
              _out1527 = DCOMP.COMP.GenType((_2431_typeArgs).Select(_2435_typeI), false, false);
              _2436_typeString = _out1527;
              _2434_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2434_typeArgString, _2436_typeString);
              _2435_typeI = (_2435_typeI) + (BigInteger.One);
            }
            _2434_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2434_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _2437_argString;
          _2437_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2438_i;
          _2438_i = BigInteger.Zero;
          while ((_2438_i) < (new BigInteger((_2430_args).Count))) {
            if ((_2438_i).Sign == 1) {
              _2437_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2437_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2439_argExpr;
            bool _2440_isOwned;
            bool _2441_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2442_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1528;
            bool _out1529;
            bool _out1530;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1531;
            DCOMP.COMP.GenExpr((_2430_args).Select(_2438_i), selfIdent, @params, false, out _out1528, out _out1529, out _out1530, out _out1531);
            _2439_argExpr = _out1528;
            _2440_isOwned = _out1529;
            _2441_argErased = _out1530;
            _2442_argIdents = _out1531;
            if (_2440_isOwned) {
              _2439_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2439_argExpr);
            }
            _2437_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2437_argString, _2439_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2442_argIdents);
            _2438_i = (_2438_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2443_enclosingString;
          bool _2444___v78;
          bool _2445___v79;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2446_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1532;
          bool _out1533;
          bool _out1534;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1535;
          DCOMP.COMP.GenExpr(_2433_on, selfIdent, @params, false, out _out1532, out _out1533, out _out1534, out _out1535);
          _2443_enclosingString = _out1532;
          _2444___v78 = _out1533;
          _2445___v79 = _out1534;
          _2446_recIdents = _out1535;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2446_recIdents);
          DAST._IExpression _source74 = _2433_on;
          if (_source74.is_Literal) {
            DAST._ILiteral _2447___mcc_h1040 = _source74.dtor_Literal_a0;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2448___mcc_h1042 = _source74.dtor_Ident_a0;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2449___mcc_h1044 = _source74.dtor_Companion_a0;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(_2443_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
            }
          } else if (_source74.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2450___mcc_h1046 = _source74.dtor_Tuple_a0;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2451___mcc_h1048 = _source74.dtor_path;
            Dafny.ISequence<DAST._IExpression> _2452___mcc_h1049 = _source74.dtor_args;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2453___mcc_h1052 = _source74.dtor_dims;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2454___mcc_h1054 = _source74.dtor_path;
            Dafny.ISequence<Dafny.Rune> _2455___mcc_h1055 = _source74.dtor_variant;
            bool _2456___mcc_h1056 = _source74.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2457___mcc_h1057 = _source74.dtor_contents;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Convert) {
            DAST._IExpression _2458___mcc_h1062 = _source74.dtor_value;
            DAST._IType _2459___mcc_h1063 = _source74.dtor_from;
            DAST._IType _2460___mcc_h1064 = _source74.dtor_typ;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2461___mcc_h1068 = _source74.dtor_elements;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2462___mcc_h1070 = _source74.dtor_elements;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_This) {
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Ite) {
            DAST._IExpression _2463___mcc_h1072 = _source74.dtor_cond;
            DAST._IExpression _2464___mcc_h1073 = _source74.dtor_thn;
            DAST._IExpression _2465___mcc_h1074 = _source74.dtor_els;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_UnOp) {
            DAST._IUnaryOp _2466___mcc_h1078 = _source74.dtor_unOp;
            DAST._IExpression _2467___mcc_h1079 = _source74.dtor_expr;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _2468___mcc_h1082 = _source74.dtor_op;
            DAST._IExpression _2469___mcc_h1083 = _source74.dtor_left;
            DAST._IExpression _2470___mcc_h1084 = _source74.dtor_right;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_ArrayLen) {
            DAST._IExpression _2471___mcc_h1088 = _source74.dtor_expr;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Select) {
            DAST._IExpression _2472___mcc_h1090 = _source74.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2473___mcc_h1091 = _source74.dtor_field;
            bool _2474___mcc_h1092 = _source74.dtor_isConstant;
            bool _2475___mcc_h1093 = _source74.dtor_onDatatype;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_SelectFn) {
            DAST._IExpression _2476___mcc_h1098 = _source74.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2477___mcc_h1099 = _source74.dtor_field;
            bool _2478___mcc_h1100 = _source74.dtor_onDatatype;
            bool _2479___mcc_h1101 = _source74.dtor_isStatic;
            BigInteger _2480___mcc_h1102 = _source74.dtor_arity;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Index) {
            DAST._IExpression _2481___mcc_h1108 = _source74.dtor_expr;
            DAST._IExpression _2482___mcc_h1109 = _source74.dtor_idx;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_TupleSelect) {
            DAST._IExpression _2483___mcc_h1112 = _source74.dtor_expr;
            BigInteger _2484___mcc_h1113 = _source74.dtor_index;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Call) {
            DAST._IExpression _2485___mcc_h1116 = _source74.dtor_on;
            Dafny.ISequence<Dafny.Rune> _2486___mcc_h1117 = _source74.dtor_name;
            Dafny.ISequence<DAST._IType> _2487___mcc_h1118 = _source74.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2488___mcc_h1119 = _source74.dtor_args;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2489___mcc_h1124 = _source74.dtor_params;
            DAST._IType _2490___mcc_h1125 = _source74.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2491___mcc_h1126 = _source74.dtor_body;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2492___mcc_h1130 = _source74.dtor_name;
            DAST._IType _2493___mcc_h1131 = _source74.dtor_typ;
            DAST._IExpression _2494___mcc_h1132 = _source74.dtor_value;
            DAST._IExpression _2495___mcc_h1133 = _source74.dtor_iifeBody;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_Apply) {
            DAST._IExpression _2496___mcc_h1138 = _source74.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2497___mcc_h1139 = _source74.dtor_args;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source74.is_TypeTest) {
            DAST._IExpression _2498___mcc_h1142 = _source74.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2499___mcc_h1143 = _source74.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2500___mcc_h1144 = _source74.dtor_variant;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _2501___mcc_h1148 = _source74.dtor_typ;
            {
              _2443_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2443_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2443_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), (_2432_name)), _2434_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2437_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source21.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2502___mcc_h160 = _source21.dtor_params;
        DAST._IType _2503___mcc_h161 = _source21.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2504___mcc_h162 = _source21.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2505_body = _2504___mcc_h162;
        DAST._IType _2506_retType = _2503___mcc_h161;
        Dafny.ISequence<DAST._IFormal> _2507_params = _2502___mcc_h160;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2508_paramNames;
          _2508_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2509_i;
          _2509_i = BigInteger.Zero;
          while ((_2509_i) < (new BigInteger((_2507_params).Count))) {
            _2508_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2508_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2507_params).Select(_2509_i)).dtor_name));
            _2509_i = (_2509_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2510_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2511_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1536;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1537;
          DCOMP.COMP.GenStmts(_2505_body, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), _2508_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1536, out _out1537);
          _2510_recursiveGen = _out1536;
          _2511_recIdents = _out1537;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2512_allReadCloned;
          _2512_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2511_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2513_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2511_recIdents).Elements) {
              _2513_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2511_recIdents).Contains(_2513_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1663)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2508_paramNames).Contains(_2513_next))) {
              _2512_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2512_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2513_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2513_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2513_next));
            }
            _2511_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2511_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2513_next));
          }
          Dafny.ISequence<Dafny.Rune> _2514_paramsString;
          _2514_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2509_i = BigInteger.Zero;
          while ((_2509_i) < (new BigInteger((_2507_params).Count))) {
            if ((_2509_i).Sign == 1) {
              _2514_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2514_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2515_typStr;
            Dafny.ISequence<Dafny.Rune> _out1538;
            _out1538 = DCOMP.COMP.GenType(((_2507_params).Select(_2509_i)).dtor_typ, false, true);
            _2515_typStr = _out1538;
            _2514_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2514_paramsString, ((_2507_params).Select(_2509_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2515_typStr);
            _2509_i = (_2509_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2516_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1539;
          _out1539 = DCOMP.COMP.GenType(_2506_retType, false, true);
          _2516_retTypeGen = _out1539;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper({\n"), _2512_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::boxed::Box::new(move |")), _2514_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2516_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2510_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source21.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2517___mcc_h163 = _source21.dtor_name;
        DAST._IType _2518___mcc_h164 = _source21.dtor_typ;
        DAST._IExpression _2519___mcc_h165 = _source21.dtor_value;
        DAST._IExpression _2520___mcc_h166 = _source21.dtor_iifeBody;
        DAST._IExpression _2521_iifeBody = _2520___mcc_h166;
        DAST._IExpression _2522_value = _2519___mcc_h165;
        DAST._IType _2523_tpe = _2518___mcc_h164;
        Dafny.ISequence<Dafny.Rune> _2524_name = _2517___mcc_h163;
        {
          Dafny.ISequence<Dafny.Rune> _2525_valueGen;
          bool _2526_valueOwned;
          bool _2527_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2528_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1540;
          bool _out1541;
          bool _out1542;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1543;
          DCOMP.COMP.GenExpr(_2522_value, selfIdent, @params, false, out _out1540, out _out1541, out _out1542, out _out1543);
          _2525_valueGen = _out1540;
          _2526_valueOwned = _out1541;
          _2527_valueErased = _out1542;
          _2528_recIdents = _out1543;
          if (_2527_valueErased) {
            Dafny.ISequence<Dafny.Rune> _2529_eraseFn;
            _2529_eraseFn = ((_2526_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
            _2525_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::"), _2529_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2525_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2528_recIdents;
          Dafny.ISequence<Dafny.Rune> _2530_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1544;
          _out1544 = DCOMP.COMP.GenType(_2523_tpe, false, true);
          _2530_valueTypeGen = _out1544;
          Dafny.ISequence<Dafny.Rune> _2531_bodyGen;
          bool _2532_bodyOwned;
          bool _2533_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2534_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1545;
          bool _out1546;
          bool _out1547;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1548;
          DCOMP.COMP.GenExpr(_2521_iifeBody, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, ((_2526_valueOwned) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2524_name))))), mustOwn, out _out1545, out _out1546, out _out1547, out _out1548);
          _2531_bodyGen = _out1545;
          _2532_bodyOwned = _out1546;
          _2533_bodyErased = _out1547;
          _2534_bodyIdents = _out1548;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2534_bodyIdents);
          Dafny.ISequence<Dafny.Rune> _2535_eraseFn;
          _2535_eraseFn = ((_2526_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2524_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((_2526_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")))), _2530_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2525_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2531_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2532_bodyOwned;
          isErased = _2533_bodyErased;
        }
      } else if (_source21.is_Apply) {
        DAST._IExpression _2536___mcc_h167 = _source21.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2537___mcc_h168 = _source21.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2538_args = _2537___mcc_h168;
        DAST._IExpression _2539_func = _2536___mcc_h167;
        {
          Dafny.ISequence<Dafny.Rune> _2540_funcString;
          bool _2541___v82;
          bool _2542_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2543_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1549;
          bool _out1550;
          bool _out1551;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1552;
          DCOMP.COMP.GenExpr(_2539_func, selfIdent, @params, false, out _out1549, out _out1550, out _out1551, out _out1552);
          _2540_funcString = _out1549;
          _2541___v82 = _out1550;
          _2542_funcErased = _out1551;
          _2543_recIdents = _out1552;
          readIdents = _2543_recIdents;
          Dafny.ISequence<Dafny.Rune> _2544_argString;
          _2544_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2545_i;
          _2545_i = BigInteger.Zero;
          while ((_2545_i) < (new BigInteger((_2538_args).Count))) {
            if ((_2545_i).Sign == 1) {
              _2544_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2544_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2546_argExpr;
            bool _2547_isOwned;
            bool _2548_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2549_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1553;
            bool _out1554;
            bool _out1555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1556;
            DCOMP.COMP.GenExpr((_2538_args).Select(_2545_i), selfIdent, @params, false, out _out1553, out _out1554, out _out1555, out _out1556);
            _2546_argExpr = _out1553;
            _2547_isOwned = _out1554;
            _2548_argErased = _out1555;
            _2549_argIdents = _out1556;
            if (_2547_isOwned) {
              _2546_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2546_argExpr);
            }
            _2544_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2544_argString, _2546_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2549_argIdents);
            _2545_i = (_2545_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2540_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2544_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source21.is_TypeTest) {
        DAST._IExpression _2550___mcc_h169 = _source21.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2551___mcc_h170 = _source21.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2552___mcc_h171 = _source21.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2553_variant = _2552___mcc_h171;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2554_dType = _2551___mcc_h170;
        DAST._IExpression _2555_on = _2550___mcc_h169;
        {
          Dafny.ISequence<Dafny.Rune> _2556_exprGen;
          bool _2557___v83;
          bool _2558_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2559_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1557;
          bool _out1558;
          bool _out1559;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1560;
          DCOMP.COMP.GenExpr(_2555_on, selfIdent, @params, false, out _out1557, out _out1558, out _out1559, out _out1560);
          _2556_exprGen = _out1557;
          _2557___v83 = _out1558;
          _2558_exprErased = _out1559;
          _2559_recIdents = _out1560;
          Dafny.ISequence<Dafny.Rune> _2560_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1561;
          _out1561 = DCOMP.COMP.GenPath(_2554_dType);
          _2560_dTypePath = _out1561;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2556_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2560_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2553_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2559_recIdents;
        }
      } else {
        DAST._IType _2561___mcc_h172 = _source21.dtor_typ;
        DAST._IType _2562_typ = _2561___mcc_h172;
        {
          Dafny.ISequence<Dafny.Rune> _2563_typString;
          Dafny.ISequence<Dafny.Rune> _out1562;
          _out1562 = DCOMP.COMP.GenType(_2562_typ, false, false);
          _2563_typString = _out1562;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2563_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
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
      BigInteger _2564_i;
      _2564_i = BigInteger.Zero;
      while ((_2564_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2565_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1563;
        _out1563 = DCOMP.COMP.GenModule((p).Select(_2564_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2565_generated = _out1563;
        if ((_2564_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2565_generated);
        _2564_i = (_2564_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2566_i;
      _2566_i = BigInteger.Zero;
      while ((_2566_i) < (new BigInteger((fullName).Count))) {
        if ((_2566_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2566_i));
        _2566_i = (_2566_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

