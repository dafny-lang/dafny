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
      hash = ((hash << 5) + hash) + 22;
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
      hash = ((hash << 5) + hash) + 23;
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
      hash = ((hash << 5) + hash) + 24;
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
      hash = ((hash << 5) + hash) + 25;
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
          } else if (_source19.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _387___mcc_h122 = _source19.dtor_name;
            DAST._IType _388___mcc_h123 = _source19.dtor_typ;
            DAST._IExpression _389___mcc_h124 = _source19.dtor_value;
            DAST._IExpression _390___mcc_h125 = _source19.dtor_iifeBody;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_Apply) {
            DAST._IExpression _391___mcc_h130 = _source19.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _392___mcc_h131 = _source19.dtor_args;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else if (_source19.is_TypeTest) {
            DAST._IExpression _393___mcc_h134 = _source19.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _394___mcc_h135 = _source19.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _395___mcc_h136 = _source19.dtor_variant;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          } else {
            DAST._IType _396___mcc_h140 = _source19.dtor_typ;
            {
              _333_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")."));
            }
          }
          Dafny.ISequence<Dafny.Rune> _397_receiver;
          _397_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          DAST._IOptional<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source20 = _319_maybeOutVars;
          if (_source20.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _398___mcc_h142 = _source20.dtor_Some_a0;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _399_outVars = _398___mcc_h142;
            {
              if ((new BigInteger((_399_outVars).Count)) > (BigInteger.One)) {
                _397_receiver = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
              }
              BigInteger _400_outI;
              _400_outI = BigInteger.Zero;
              while ((_400_outI) < (new BigInteger((_399_outVars).Count))) {
                if ((_400_outI).Sign == 1) {
                  _397_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_397_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                Dafny.ISequence<Dafny.Rune> _401_outVar;
                _401_outVar = (_399_outVars).Select(_400_outI);
                _397_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_397_receiver, (_401_outVar));
                _400_outI = (_400_outI) + (BigInteger.One);
              }
              if ((new BigInteger((_399_outVars).Count)) > (BigInteger.One)) {
                _397_receiver = Dafny.Sequence<Dafny.Rune>.Concat(_397_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
            }
          } else {
          }
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((!(_397_receiver).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_397_receiver, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _333_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _322_name), _324_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _327_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(");"));
        }
      } else if (_source16.is_Return) {
        DAST._IExpression _402___mcc_h17 = _source16.dtor_expr;
        DAST._IExpression _403_expr = _402___mcc_h17;
        {
          Dafny.ISequence<Dafny.Rune> _404_exprString;
          bool _405___v25;
          bool _406_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _407_recIdents;
          Dafny.ISequence<Dafny.Rune> _out112;
          bool _out113;
          bool _out114;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out115;
          DCOMP.COMP.GenExpr(_403_expr, selfIdent, @params, true, out _out112, out _out113, out _out114, out _out115);
          _404_exprString = _out112;
          _405___v25 = _out113;
          _406_recErased = _out114;
          _407_recIdents = _out115;
          _404_exprString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _404_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          readIdents = _407_recIdents;
          if (isLast) {
            generated = _404_exprString;
          } else {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return "), _404_exprString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
          }
        }
      } else if (_source16.is_EarlyReturn) {
        {
          generated = earlyReturn;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_Break) {
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _408___mcc_h18 = _source16.dtor_toLabel;
        DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _409_toLabel = _408___mcc_h18;
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source21 = _409_toLabel;
          if (_source21.is_Some) {
            Dafny.ISequence<Dafny.Rune> _410___mcc_h143 = _source21.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _411_lbl = _410___mcc_h143;
            {
              generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break 'label_"), _411_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          } else {
            {
              generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
            }
          }
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source16.is_TailRecursive) {
        Dafny.ISequence<DAST._IStatement> _412___mcc_h19 = _source16.dtor_body;
        Dafny.ISequence<DAST._IStatement> _413_body = _412___mcc_h19;
        {
          generated = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if (!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) {
            generated = Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#_this = self.clone();\n"));
          }
          BigInteger _414_paramI;
          _414_paramI = BigInteger.Zero;
          while ((_414_paramI) < (new BigInteger((@params).Count))) {
            Dafny.ISequence<Dafny.Rune> _415_param;
            _415_param = (@params).Select(_414_paramI);
            generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let mut r#")), _415_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _415_param), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
            _414_paramI = (_414_paramI) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _416_bodyString;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _417_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out116;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
          DCOMP.COMP.GenStmts(_413_body, ((!object.Equals(selfIdent, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())) ? (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"))) : (DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), false, earlyReturn, out _out116, out _out117);
          _416_bodyString = _out116;
          _417_bodyIdents = _out117;
          readIdents = _417_bodyIdents;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(generated, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'TAIL_CALL_START: loop {\n")), _416_bodyString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
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
        DAST._IExpression _418___mcc_h20 = _source16.dtor_Print_a0;
        DAST._IExpression _419_e = _418___mcc_h20;
        {
          Dafny.ISequence<Dafny.Rune> _420_printedExpr;
          bool _421_isOwned;
          bool _422___v26;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _423_recIdents;
          Dafny.ISequence<Dafny.Rune> _out118;
          bool _out119;
          bool _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          DCOMP.COMP.GenExpr(_419_e, selfIdent, @params, false, out _out118, out _out119, out _out120, out _out121);
          _420_printedExpr = _out118;
          _421_isOwned = _out119;
          _422___v26 = _out120;
          _423_recIdents = _out121;
          generated = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper("), ((_421_isOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _420_printedExpr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("));"));
          readIdents = _423_recIdents;
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
        DAST._ILiteral _424___mcc_h0 = _source22.dtor_Literal_a0;
        DAST._ILiteral _source23 = _424___mcc_h0;
        if (_source23.is_BoolLiteral) {
          bool _425___mcc_h1 = _source23.dtor_BoolLiteral_a0;
          if ((_425___mcc_h1) == (false)) {
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
          Dafny.ISequence<Dafny.Rune> _426___mcc_h2 = _source23.dtor_IntLiteral_a0;
          DAST._IType _427___mcc_h3 = _source23.dtor_IntLiteral_a1;
          DAST._IType _428_t = _427___mcc_h3;
          Dafny.ISequence<Dafny.Rune> _429_i = _426___mcc_h2;
          {
            DAST._IType _source24 = _428_t;
            if (_source24.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _430___mcc_h188 = _source24.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _431___mcc_h189 = _source24.dtor_typeArgs;
              DAST._IResolvedType _432___mcc_h190 = _source24.dtor_resolved;
              {
                s = _429_i;
              }
            } else if (_source24.is_Nullable) {
              DAST._IType _433___mcc_h194 = _source24.dtor_Nullable_a0;
              {
                s = _429_i;
              }
            } else if (_source24.is_Tuple) {
              Dafny.ISequence<DAST._IType> _434___mcc_h196 = _source24.dtor_Tuple_a0;
              {
                s = _429_i;
              }
            } else if (_source24.is_Array) {
              DAST._IType _435___mcc_h198 = _source24.dtor_element;
              {
                s = _429_i;
              }
            } else if (_source24.is_Seq) {
              DAST._IType _436___mcc_h200 = _source24.dtor_element;
              {
                s = _429_i;
              }
            } else if (_source24.is_Set) {
              DAST._IType _437___mcc_h202 = _source24.dtor_element;
              {
                s = _429_i;
              }
            } else if (_source24.is_Multiset) {
              DAST._IType _438___mcc_h204 = _source24.dtor_element;
              {
                s = _429_i;
              }
            } else if (_source24.is_Map) {
              DAST._IType _439___mcc_h206 = _source24.dtor_key;
              DAST._IType _440___mcc_h207 = _source24.dtor_value;
              {
                s = _429_i;
              }
            } else if (_source24.is_Arrow) {
              Dafny.ISequence<DAST._IType> _441___mcc_h210 = _source24.dtor_args;
              DAST._IType _442___mcc_h211 = _source24.dtor_result;
              {
                s = _429_i;
              }
            } else if (_source24.is_Primitive) {
              DAST._IPrimitive _443___mcc_h214 = _source24.dtor_Primitive_a0;
              DAST._IPrimitive _source25 = _443___mcc_h214;
              if (_source25.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::parse_bytes(b\""), _429_i), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap()"));
                }
              } else if (_source25.is_Real) {
                {
                  s = _429_i;
                }
              } else if (_source25.is_String) {
                {
                  s = _429_i;
                }
              } else if (_source25.is_Bool) {
                {
                  s = _429_i;
                }
              } else {
                {
                  s = _429_i;
                }
              }
            } else if (_source24.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _444___mcc_h216 = _source24.dtor_Passthrough_a0;
              {
                s = _429_i;
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _445___mcc_h218 = _source24.dtor_TypeArg_a0;
              {
                s = _429_i;
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_DecLiteral) {
          Dafny.ISequence<Dafny.Rune> _446___mcc_h4 = _source23.dtor_DecLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _447___mcc_h5 = _source23.dtor_DecLiteral_a1;
          DAST._IType _448___mcc_h6 = _source23.dtor_DecLiteral_a2;
          DAST._IType _449_t = _448___mcc_h6;
          Dafny.ISequence<Dafny.Rune> _450_d = _447___mcc_h5;
          Dafny.ISequence<Dafny.Rune> _451_n = _446___mcc_h4;
          {
            DAST._IType _source26 = _449_t;
            if (_source26.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _452___mcc_h220 = _source26.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _453___mcc_h221 = _source26.dtor_typeArgs;
              DAST._IResolvedType _454___mcc_h222 = _source26.dtor_resolved;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Nullable) {
              DAST._IType _455___mcc_h226 = _source26.dtor_Nullable_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Tuple) {
              Dafny.ISequence<DAST._IType> _456___mcc_h228 = _source26.dtor_Tuple_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Array) {
              DAST._IType _457___mcc_h230 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Seq) {
              DAST._IType _458___mcc_h232 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Set) {
              DAST._IType _459___mcc_h234 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Multiset) {
              DAST._IType _460___mcc_h236 = _source26.dtor_element;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Map) {
              DAST._IType _461___mcc_h238 = _source26.dtor_key;
              DAST._IType _462___mcc_h239 = _source26.dtor_value;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Arrow) {
              Dafny.ISequence<DAST._IType> _463___mcc_h242 = _source26.dtor_args;
              DAST._IType _464___mcc_h243 = _source26.dtor_result;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else if (_source26.is_Primitive) {
              DAST._IPrimitive _465___mcc_h246 = _source26.dtor_Primitive_a0;
              DAST._IPrimitive _source27 = _465___mcc_h246;
              if (_source27.is_Int) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source27.is_Real) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _451_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"));
                }
              } else if (_source27.is_String) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else if (_source27.is_Bool) {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              } else {
                {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
                }
              }
            } else if (_source26.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _466___mcc_h248 = _source26.dtor_Passthrough_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _467___mcc_h250 = _source26.dtor_TypeArg_a0;
              {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_451_n, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _450_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0"));
              }
            }
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_StringLiteral) {
          Dafny.ISequence<Dafny.Rune> _468___mcc_h7 = _source23.dtor_StringLiteral_a0;
          Dafny.ISequence<Dafny.Rune> _469_l = _468___mcc_h7;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\""), _469_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\".chars().collect::<Vec<char>>()"));
            isOwned = true;
            isErased = true;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
        } else if (_source23.is_CharLiteral) {
          Dafny.Rune _470___mcc_h8 = _source23.dtor_CharLiteral_a0;
          Dafny.Rune _471_c = _470___mcc_h8;
          {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::primitive::char::from_u32("), DCOMP.__default.natToString(new BigInteger((_471_c).Value))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
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
        Dafny.ISequence<Dafny.Rune> _472___mcc_h9 = _source22.dtor_Ident_a0;
        Dafny.ISequence<Dafny.Rune> _473_name = _472___mcc_h9;
        {
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), _473_name);
          if (!((@params).Contains(_473_name))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            isOwned = false;
          }
          isErased = false;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_473_name);
        }
      } else if (_source22.is_Companion) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _474___mcc_h10 = _source22.dtor_Companion_a0;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _475_path = _474___mcc_h10;
        {
          Dafny.ISequence<Dafny.Rune> _out122;
          _out122 = DCOMP.COMP.GenPath(_475_path);
          s = _out122;
          isOwned = true;
          isErased = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
        }
      } else if (_source22.is_Tuple) {
        Dafny.ISequence<DAST._IExpression> _476___mcc_h11 = _source22.dtor_Tuple_a0;
        Dafny.ISequence<DAST._IExpression> _477_values = _476___mcc_h11;
        {
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _478_i;
          _478_i = BigInteger.Zero;
          bool _479_allErased;
          _479_allErased = true;
          while ((_478_i) < (new BigInteger((_477_values).Count))) {
            Dafny.ISequence<Dafny.Rune> _480___v29;
            bool _481___v30;
            bool _482_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _483___v31;
            Dafny.ISequence<Dafny.Rune> _out123;
            bool _out124;
            bool _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            DCOMP.COMP.GenExpr((_477_values).Select(_478_i), selfIdent, @params, true, out _out123, out _out124, out _out125, out _out126);
            _480___v29 = _out123;
            _481___v30 = _out124;
            _482_isErased = _out125;
            _483___v31 = _out126;
            _479_allErased = (_479_allErased) && (_482_isErased);
            _478_i = (_478_i) + (BigInteger.One);
          }
          _478_i = BigInteger.Zero;
          while ((_478_i) < (new BigInteger((_477_values).Count))) {
            if ((_478_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
            }
            Dafny.ISequence<Dafny.Rune> _484_recursiveGen;
            bool _485___v32;
            bool _486_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _487_recIdents;
            Dafny.ISequence<Dafny.Rune> _out127;
            bool _out128;
            bool _out129;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
            DCOMP.COMP.GenExpr((_477_values).Select(_478_i), selfIdent, @params, true, out _out127, out _out128, out _out129, out _out130);
            _484_recursiveGen = _out127;
            _485___v32 = _out128;
            _486_isErased = _out129;
            _487_recIdents = _out130;
            if ((_486_isErased) && (!(_479_allErased))) {
              _484_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _484_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, _484_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _487_recIdents);
            _478_i = (_478_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = _479_allErased;
        }
      } else if (_source22.is_New) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _488___mcc_h12 = _source22.dtor_path;
        Dafny.ISequence<DAST._IExpression> _489___mcc_h13 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _490_args = _489___mcc_h13;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _491_path = _488___mcc_h12;
        {
          Dafny.ISequence<Dafny.Rune> _492_path;
          Dafny.ISequence<Dafny.Rune> _out131;
          _out131 = DCOMP.COMP.GenPath(_491_path);
          _492_path = _out131;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _492_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::new("));
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _493_i;
          _493_i = BigInteger.Zero;
          while ((_493_i) < (new BigInteger((_490_args).Count))) {
            if ((_493_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _494_recursiveGen;
            bool _495___v33;
            bool _496_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _497_recIdents;
            Dafny.ISequence<Dafny.Rune> _out132;
            bool _out133;
            bool _out134;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
            DCOMP.COMP.GenExpr((_490_args).Select(_493_i), selfIdent, @params, true, out _out132, out _out133, out _out134, out _out135);
            _494_recursiveGen = _out132;
            _495___v33 = _out133;
            _496_isErased = _out134;
            _497_recIdents = _out135;
            if (_496_isErased) {
              _494_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _494_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _494_recursiveGen);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _497_recIdents);
            _493_i = (_493_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_NewArray) {
        Dafny.ISequence<DAST._IExpression> _498___mcc_h14 = _source22.dtor_dims;
        Dafny.ISequence<DAST._IExpression> _499_dims = _498___mcc_h14;
        {
          BigInteger _500_i;
          _500_i = (new BigInteger((_499_dims).Count)) - (BigInteger.One);
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()");
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          while ((_500_i).Sign != -1) {
            Dafny.ISequence<Dafny.Rune> _501_recursiveGen;
            bool _502___v34;
            bool _503_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _504_recIdents;
            Dafny.ISequence<Dafny.Rune> _out136;
            bool _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP.COMP.GenExpr((_499_dims).Select(_500_i), selfIdent, @params, true, out _out136, out _out137, out _out138, out _out139);
            _501_recursiveGen = _out136;
            _502___v34 = _out137;
            _503_isErased = _out138;
            _504_recIdents = _out139;
            if (!(_503_isErased)) {
              _501_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _501_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new(::std::cell::RefCell::new(vec!["), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; <usize as ::dafny_runtime::NumCast>::from(")), _501_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]))"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _504_recIdents);
            _500_i = (_500_i) - (BigInteger.One);
          }
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_DatatypeValue) {
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _505___mcc_h15 = _source22.dtor_path;
        Dafny.ISequence<Dafny.Rune> _506___mcc_h16 = _source22.dtor_variant;
        bool _507___mcc_h17 = _source22.dtor_isCo;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _508___mcc_h18 = _source22.dtor_contents;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _509_values = _508___mcc_h18;
        bool _510_isCo = _507___mcc_h17;
        Dafny.ISequence<Dafny.Rune> _511_variant = _506___mcc_h16;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _512_path = _505___mcc_h15;
        {
          Dafny.ISequence<Dafny.Rune> _513_path;
          Dafny.ISequence<Dafny.Rune> _out140;
          _out140 = DCOMP.COMP.GenPath(_512_path);
          _513_path = _out140;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _513_path), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _511_variant);
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _514_i;
          _514_i = BigInteger.Zero;
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"));
          while ((_514_i) < (new BigInteger((_509_values).Count))) {
            _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs0 = (_509_values).Select(_514_i);
            Dafny.ISequence<Dafny.Rune> _515_name = _let_tmp_rhs0.dtor__0;
            DAST._IExpression _516_value = _let_tmp_rhs0.dtor__1;
            if ((_514_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            if (_510_isCo) {
              Dafny.ISequence<Dafny.Rune> _517_recursiveGen;
              bool _518___v35;
              bool _519_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _520_recIdents;
              Dafny.ISequence<Dafny.Rune> _out141;
              bool _out142;
              bool _out143;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
              DCOMP.COMP.GenExpr(_516_value, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), true, out _out141, out _out142, out _out143, out _out144);
              _517_recursiveGen = _out141;
              _518___v35 = _out142;
              _519_isErased = _out143;
              _520_recIdents = _out144;
              if (!(_519_isErased)) {
                _517_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _517_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _517_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _517_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _520_recIdents);
              Dafny.ISequence<Dafny.Rune> _521_allReadCloned;
              _521_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              while (!(_520_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                Dafny.ISequence<Dafny.Rune> _522_next;
                foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_0 in (_520_recIdents).Elements) {
                  _522_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_0;
                  if ((_520_recIdents).Contains(_522_next)) {
                    goto after__ASSIGN_SUCH_THAT_0;
                  }
                }
                throw new System.Exception("assign-such-that search produced no value (line 1185)");
              after__ASSIGN_SUCH_THAT_0:;
                _521_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_521_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _522_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _522_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                _520_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_520_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_522_next));
              }
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _515_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n")), _521_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), _517_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
            } else {
              Dafny.ISequence<Dafny.Rune> _523_recursiveGen;
              bool _524___v36;
              bool _525_isErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _526_recIdents;
              Dafny.ISequence<Dafny.Rune> _out145;
              bool _out146;
              bool _out147;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
              DCOMP.COMP.GenExpr(_516_value, selfIdent, @params, true, out _out145, out _out146, out _out147, out _out148);
              _523_recursiveGen = _out145;
              _524___v36 = _out146;
              _525_isErased = _out147;
              _526_recIdents = _out148;
              if (!(_525_isErased)) {
                _523_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _523_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _523_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _523_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")), _515_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _523_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _526_recIdents);
            }
            _514_i = (_514_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" })"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_Convert) {
        DAST._IExpression _527___mcc_h19 = _source22.dtor_value;
        DAST._IType _528___mcc_h20 = _source22.dtor_from;
        DAST._IType _529___mcc_h21 = _source22.dtor_typ;
        DAST._IType _530_toTpe = _529___mcc_h21;
        DAST._IType _531_fromTpe = _528___mcc_h20;
        DAST._IExpression _532_expr = _527___mcc_h19;
        {
          if (object.Equals(_531_fromTpe, _530_toTpe)) {
            Dafny.ISequence<Dafny.Rune> _533_recursiveGen;
            bool _534_recOwned;
            bool _535_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _536_recIdents;
            Dafny.ISequence<Dafny.Rune> _out149;
            bool _out150;
            bool _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out149, out _out150, out _out151, out _out152);
            _533_recursiveGen = _out149;
            _534_recOwned = _out150;
            _535_recErased = _out151;
            _536_recIdents = _out152;
            s = _533_recursiveGen;
            isOwned = _534_recOwned;
            isErased = _535_recErased;
            readIdents = _536_recIdents;
          } else {
            _System._ITuple2<DAST._IType, DAST._IType> _source28 = _System.Tuple2<DAST._IType, DAST._IType>.create(_531_fromTpe, _530_toTpe);
            DAST._IType _537___mcc_h252 = _source28.dtor__0;
            DAST._IType _538___mcc_h253 = _source28.dtor__1;
            DAST._IType _source29 = _537___mcc_h252;
            if (_source29.is_Path) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _539___mcc_h256 = _source29.dtor_Path_a0;
              Dafny.ISequence<DAST._IType> _540___mcc_h257 = _source29.dtor_typeArgs;
              DAST._IResolvedType _541___mcc_h258 = _source29.dtor_resolved;
              DAST._IResolvedType _source30 = _541___mcc_h258;
              if (_source30.is_Datatype) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _542___mcc_h268 = _source30.dtor_path;
                DAST._IType _source31 = _538___mcc_h253;
                if (_source31.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _543___mcc_h272 = _source31.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _544___mcc_h273 = _source31.dtor_typeArgs;
                  DAST._IResolvedType _545___mcc_h274 = _source31.dtor_resolved;
                  DAST._IResolvedType _source32 = _545___mcc_h274;
                  if (_source32.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _546___mcc_h278 = _source32.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _547_recursiveGen;
                      bool _548_recOwned;
                      bool _549_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _550_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out153;
                      bool _out154;
                      bool _out155;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out153, out _out154, out _out155, out _out156);
                      _547_recursiveGen = _out153;
                      _548_recOwned = _out154;
                      _549_recErased = _out155;
                      _550_recIdents = _out156;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _547_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _548_recOwned;
                      isErased = _549_recErased;
                      readIdents = _550_recIdents;
                    }
                  } else if (_source32.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _551___mcc_h280 = _source32.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _552_recursiveGen;
                      bool _553_recOwned;
                      bool _554_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _555_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out157;
                      bool _out158;
                      bool _out159;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out157, out _out158, out _out159, out _out160);
                      _552_recursiveGen = _out157;
                      _553_recOwned = _out158;
                      _554_recErased = _out159;
                      _555_recIdents = _out160;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _552_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _553_recOwned;
                      isErased = _554_recErased;
                      readIdents = _555_recIdents;
                    }
                  } else {
                    DAST._IType _556___mcc_h282 = _source32.dtor_Newtype_a0;
                    DAST._IType _557_b = _556___mcc_h282;
                    {
                      if (object.Equals(_531_fromTpe, _557_b)) {
                        Dafny.ISequence<Dafny.Rune> _558_recursiveGen;
                        bool _559_recOwned;
                        bool _560_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _561_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out161;
                        bool _out162;
                        bool _out163;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out161, out _out162, out _out163, out _out164);
                        _558_recursiveGen = _out161;
                        _559_recOwned = _out162;
                        _560_recErased = _out163;
                        _561_recIdents = _out164;
                        Dafny.ISequence<Dafny.Rune> _562_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out165;
                        _out165 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _562_rhsType = _out165;
                        Dafny.ISequence<Dafny.Rune> _563_uneraseFn;
                        _563_uneraseFn = ((_559_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _562_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _563_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _558_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _559_recOwned;
                        isErased = false;
                        readIdents = _561_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out166;
                        bool _out167;
                        bool _out168;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _557_b), _557_b, _530_toTpe), selfIdent, @params, mustOwn, out _out166, out _out167, out _out168, out _out169);
                        s = _out166;
                        isOwned = _out167;
                        isErased = _out168;
                        readIdents = _out169;
                      }
                    }
                  }
                } else if (_source31.is_Nullable) {
                  DAST._IType _564___mcc_h284 = _source31.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _565_recursiveGen;
                    bool _566_recOwned;
                    bool _567_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _568_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out170;
                    bool _out171;
                    bool _out172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out170, out _out171, out _out172, out _out173);
                    _565_recursiveGen = _out170;
                    _566_recOwned = _out171;
                    _567_recErased = _out172;
                    _568_recIdents = _out173;
                    if (!(_566_recOwned)) {
                      _565_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_565_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _565_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _567_recErased;
                    readIdents = _568_recIdents;
                  }
                } else if (_source31.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _569___mcc_h286 = _source31.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _570_recursiveGen;
                    bool _571_recOwned;
                    bool _572_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _573_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out174;
                    bool _out175;
                    bool _out176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out174, out _out175, out _out176, out _out177);
                    _570_recursiveGen = _out174;
                    _571_recOwned = _out175;
                    _572_recErased = _out176;
                    _573_recIdents = _out177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _570_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _571_recOwned;
                    isErased = _572_recErased;
                    readIdents = _573_recIdents;
                  }
                } else if (_source31.is_Array) {
                  DAST._IType _574___mcc_h288 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _575_recursiveGen;
                    bool _576_recOwned;
                    bool _577_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _578_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out178;
                    bool _out179;
                    bool _out180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out178, out _out179, out _out180, out _out181);
                    _575_recursiveGen = _out178;
                    _576_recOwned = _out179;
                    _577_recErased = _out180;
                    _578_recIdents = _out181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _575_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _576_recOwned;
                    isErased = _577_recErased;
                    readIdents = _578_recIdents;
                  }
                } else if (_source31.is_Seq) {
                  DAST._IType _579___mcc_h290 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _580_recursiveGen;
                    bool _581_recOwned;
                    bool _582_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _583_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out182;
                    bool _out183;
                    bool _out184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out182, out _out183, out _out184, out _out185);
                    _580_recursiveGen = _out182;
                    _581_recOwned = _out183;
                    _582_recErased = _out184;
                    _583_recIdents = _out185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _580_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _581_recOwned;
                    isErased = _582_recErased;
                    readIdents = _583_recIdents;
                  }
                } else if (_source31.is_Set) {
                  DAST._IType _584___mcc_h292 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _585_recursiveGen;
                    bool _586_recOwned;
                    bool _587_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _588_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out186;
                    bool _out187;
                    bool _out188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out186, out _out187, out _out188, out _out189);
                    _585_recursiveGen = _out186;
                    _586_recOwned = _out187;
                    _587_recErased = _out188;
                    _588_recIdents = _out189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _585_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _586_recOwned;
                    isErased = _587_recErased;
                    readIdents = _588_recIdents;
                  }
                } else if (_source31.is_Multiset) {
                  DAST._IType _589___mcc_h294 = _source31.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _590_recursiveGen;
                    bool _591_recOwned;
                    bool _592_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _593_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out190;
                    bool _out191;
                    bool _out192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out190, out _out191, out _out192, out _out193);
                    _590_recursiveGen = _out190;
                    _591_recOwned = _out191;
                    _592_recErased = _out192;
                    _593_recIdents = _out193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _590_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _591_recOwned;
                    isErased = _592_recErased;
                    readIdents = _593_recIdents;
                  }
                } else if (_source31.is_Map) {
                  DAST._IType _594___mcc_h296 = _source31.dtor_key;
                  DAST._IType _595___mcc_h297 = _source31.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _596_recursiveGen;
                    bool _597_recOwned;
                    bool _598_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _599_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out194;
                    bool _out195;
                    bool _out196;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out194, out _out195, out _out196, out _out197);
                    _596_recursiveGen = _out194;
                    _597_recOwned = _out195;
                    _598_recErased = _out196;
                    _599_recIdents = _out197;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _596_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _597_recOwned;
                    isErased = _598_recErased;
                    readIdents = _599_recIdents;
                  }
                } else if (_source31.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _600___mcc_h300 = _source31.dtor_args;
                  DAST._IType _601___mcc_h301 = _source31.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _602_recursiveGen;
                    bool _603_recOwned;
                    bool _604_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _605_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out198;
                    bool _out199;
                    bool _out200;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out198, out _out199, out _out200, out _out201);
                    _602_recursiveGen = _out198;
                    _603_recOwned = _out199;
                    _604_recErased = _out200;
                    _605_recIdents = _out201;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _602_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _603_recOwned;
                    isErased = _604_recErased;
                    readIdents = _605_recIdents;
                  }
                } else if (_source31.is_Primitive) {
                  DAST._IPrimitive _606___mcc_h304 = _source31.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _607_recursiveGen;
                    bool _608_recOwned;
                    bool _609_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _610_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out202;
                    bool _out203;
                    bool _out204;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out205;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out202, out _out203, out _out204, out _out205);
                    _607_recursiveGen = _out202;
                    _608_recOwned = _out203;
                    _609_recErased = _out204;
                    _610_recIdents = _out205;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _607_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _608_recOwned;
                    isErased = _609_recErased;
                    readIdents = _610_recIdents;
                  }
                } else if (_source31.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _611___mcc_h306 = _source31.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _612_recursiveGen;
                    bool _613_recOwned;
                    bool _614_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _615_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out206;
                    bool _out207;
                    bool _out208;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out209;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out206, out _out207, out _out208, out _out209);
                    _612_recursiveGen = _out206;
                    _613_recOwned = _out207;
                    _614_recErased = _out208;
                    _615_recIdents = _out209;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _612_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _613_recOwned;
                    isErased = _614_recErased;
                    readIdents = _615_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _616___mcc_h308 = _source31.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _617_recursiveGen;
                    bool _618_recOwned;
                    bool _619_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _620_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out210;
                    bool _out211;
                    bool _out212;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out213;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out210, out _out211, out _out212, out _out213);
                    _617_recursiveGen = _out210;
                    _618_recOwned = _out211;
                    _619_recErased = _out212;
                    _620_recIdents = _out213;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _617_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _618_recOwned;
                    isErased = _619_recErased;
                    readIdents = _620_recIdents;
                  }
                }
              } else if (_source30.is_Trait) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _621___mcc_h310 = _source30.dtor_path;
                DAST._IType _source33 = _538___mcc_h253;
                if (_source33.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _622___mcc_h314 = _source33.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _623___mcc_h315 = _source33.dtor_typeArgs;
                  DAST._IResolvedType _624___mcc_h316 = _source33.dtor_resolved;
                  DAST._IResolvedType _source34 = _624___mcc_h316;
                  if (_source34.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _625___mcc_h320 = _source34.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _626_recursiveGen;
                      bool _627_recOwned;
                      bool _628_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _629_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out214;
                      bool _out215;
                      bool _out216;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out217;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out214, out _out215, out _out216, out _out217);
                      _626_recursiveGen = _out214;
                      _627_recOwned = _out215;
                      _628_recErased = _out216;
                      _629_recIdents = _out217;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _626_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _627_recOwned;
                      isErased = _628_recErased;
                      readIdents = _629_recIdents;
                    }
                  } else if (_source34.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _630___mcc_h322 = _source34.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _631_recursiveGen;
                      bool _632_recOwned;
                      bool _633_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _634_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out218;
                      bool _out219;
                      bool _out220;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out221;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out218, out _out219, out _out220, out _out221);
                      _631_recursiveGen = _out218;
                      _632_recOwned = _out219;
                      _633_recErased = _out220;
                      _634_recIdents = _out221;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _631_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _632_recOwned;
                      isErased = _633_recErased;
                      readIdents = _634_recIdents;
                    }
                  } else {
                    DAST._IType _635___mcc_h324 = _source34.dtor_Newtype_a0;
                    DAST._IType _636_b = _635___mcc_h324;
                    {
                      if (object.Equals(_531_fromTpe, _636_b)) {
                        Dafny.ISequence<Dafny.Rune> _637_recursiveGen;
                        bool _638_recOwned;
                        bool _639_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _640_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out222;
                        bool _out223;
                        bool _out224;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out222, out _out223, out _out224, out _out225);
                        _637_recursiveGen = _out222;
                        _638_recOwned = _out223;
                        _639_recErased = _out224;
                        _640_recIdents = _out225;
                        Dafny.ISequence<Dafny.Rune> _641_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out226;
                        _out226 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _641_rhsType = _out226;
                        Dafny.ISequence<Dafny.Rune> _642_uneraseFn;
                        _642_uneraseFn = ((_638_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _641_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _642_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _637_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _638_recOwned;
                        isErased = false;
                        readIdents = _640_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out227;
                        bool _out228;
                        bool _out229;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _636_b), _636_b, _530_toTpe), selfIdent, @params, mustOwn, out _out227, out _out228, out _out229, out _out230);
                        s = _out227;
                        isOwned = _out228;
                        isErased = _out229;
                        readIdents = _out230;
                      }
                    }
                  }
                } else if (_source33.is_Nullable) {
                  DAST._IType _643___mcc_h326 = _source33.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _644_recursiveGen;
                    bool _645_recOwned;
                    bool _646_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _647_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out231;
                    bool _out232;
                    bool _out233;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out234;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out231, out _out232, out _out233, out _out234);
                    _644_recursiveGen = _out231;
                    _645_recOwned = _out232;
                    _646_recErased = _out233;
                    _647_recIdents = _out234;
                    if (!(_645_recOwned)) {
                      _644_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_644_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _644_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _646_recErased;
                    readIdents = _647_recIdents;
                  }
                } else if (_source33.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _648___mcc_h328 = _source33.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _649_recursiveGen;
                    bool _650_recOwned;
                    bool _651_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _652_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out235;
                    bool _out236;
                    bool _out237;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out238;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out235, out _out236, out _out237, out _out238);
                    _649_recursiveGen = _out235;
                    _650_recOwned = _out236;
                    _651_recErased = _out237;
                    _652_recIdents = _out238;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _649_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _650_recOwned;
                    isErased = _651_recErased;
                    readIdents = _652_recIdents;
                  }
                } else if (_source33.is_Array) {
                  DAST._IType _653___mcc_h330 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _654_recursiveGen;
                    bool _655_recOwned;
                    bool _656_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _657_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out239;
                    bool _out240;
                    bool _out241;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out242;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out239, out _out240, out _out241, out _out242);
                    _654_recursiveGen = _out239;
                    _655_recOwned = _out240;
                    _656_recErased = _out241;
                    _657_recIdents = _out242;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _654_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _655_recOwned;
                    isErased = _656_recErased;
                    readIdents = _657_recIdents;
                  }
                } else if (_source33.is_Seq) {
                  DAST._IType _658___mcc_h332 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _659_recursiveGen;
                    bool _660_recOwned;
                    bool _661_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _662_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out243;
                    bool _out244;
                    bool _out245;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out243, out _out244, out _out245, out _out246);
                    _659_recursiveGen = _out243;
                    _660_recOwned = _out244;
                    _661_recErased = _out245;
                    _662_recIdents = _out246;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _659_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _660_recOwned;
                    isErased = _661_recErased;
                    readIdents = _662_recIdents;
                  }
                } else if (_source33.is_Set) {
                  DAST._IType _663___mcc_h334 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _664_recursiveGen;
                    bool _665_recOwned;
                    bool _666_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _667_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out247;
                    bool _out248;
                    bool _out249;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out247, out _out248, out _out249, out _out250);
                    _664_recursiveGen = _out247;
                    _665_recOwned = _out248;
                    _666_recErased = _out249;
                    _667_recIdents = _out250;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _664_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _665_recOwned;
                    isErased = _666_recErased;
                    readIdents = _667_recIdents;
                  }
                } else if (_source33.is_Multiset) {
                  DAST._IType _668___mcc_h336 = _source33.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _669_recursiveGen;
                    bool _670_recOwned;
                    bool _671_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _672_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out251;
                    bool _out252;
                    bool _out253;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out251, out _out252, out _out253, out _out254);
                    _669_recursiveGen = _out251;
                    _670_recOwned = _out252;
                    _671_recErased = _out253;
                    _672_recIdents = _out254;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _669_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _670_recOwned;
                    isErased = _671_recErased;
                    readIdents = _672_recIdents;
                  }
                } else if (_source33.is_Map) {
                  DAST._IType _673___mcc_h338 = _source33.dtor_key;
                  DAST._IType _674___mcc_h339 = _source33.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _675_recursiveGen;
                    bool _676_recOwned;
                    bool _677_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _678_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out255;
                    bool _out256;
                    bool _out257;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out258;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out255, out _out256, out _out257, out _out258);
                    _675_recursiveGen = _out255;
                    _676_recOwned = _out256;
                    _677_recErased = _out257;
                    _678_recIdents = _out258;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _675_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _676_recOwned;
                    isErased = _677_recErased;
                    readIdents = _678_recIdents;
                  }
                } else if (_source33.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _679___mcc_h342 = _source33.dtor_args;
                  DAST._IType _680___mcc_h343 = _source33.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _681_recursiveGen;
                    bool _682_recOwned;
                    bool _683_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _684_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out259;
                    bool _out260;
                    bool _out261;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out259, out _out260, out _out261, out _out262);
                    _681_recursiveGen = _out259;
                    _682_recOwned = _out260;
                    _683_recErased = _out261;
                    _684_recIdents = _out262;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _681_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _682_recOwned;
                    isErased = _683_recErased;
                    readIdents = _684_recIdents;
                  }
                } else if (_source33.is_Primitive) {
                  DAST._IPrimitive _685___mcc_h346 = _source33.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _686_recursiveGen;
                    bool _687_recOwned;
                    bool _688_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _689_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out263;
                    bool _out264;
                    bool _out265;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out263, out _out264, out _out265, out _out266);
                    _686_recursiveGen = _out263;
                    _687_recOwned = _out264;
                    _688_recErased = _out265;
                    _689_recIdents = _out266;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _686_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _687_recOwned;
                    isErased = _688_recErased;
                    readIdents = _689_recIdents;
                  }
                } else if (_source33.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _690___mcc_h348 = _source33.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _691_recursiveGen;
                    bool _692_recOwned;
                    bool _693_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _694_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out267;
                    bool _out268;
                    bool _out269;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out267, out _out268, out _out269, out _out270);
                    _691_recursiveGen = _out267;
                    _692_recOwned = _out268;
                    _693_recErased = _out269;
                    _694_recIdents = _out270;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _691_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _692_recOwned;
                    isErased = _693_recErased;
                    readIdents = _694_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _695___mcc_h350 = _source33.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _696_recursiveGen;
                    bool _697_recOwned;
                    bool _698_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _699_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out271;
                    bool _out272;
                    bool _out273;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out271, out _out272, out _out273, out _out274);
                    _696_recursiveGen = _out271;
                    _697_recOwned = _out272;
                    _698_recErased = _out273;
                    _699_recIdents = _out274;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _696_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _697_recOwned;
                    isErased = _698_recErased;
                    readIdents = _699_recIdents;
                  }
                }
              } else {
                DAST._IType _700___mcc_h352 = _source30.dtor_Newtype_a0;
                DAST._IType _source35 = _538___mcc_h253;
                if (_source35.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _701___mcc_h356 = _source35.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _702___mcc_h357 = _source35.dtor_typeArgs;
                  DAST._IResolvedType _703___mcc_h358 = _source35.dtor_resolved;
                  DAST._IResolvedType _source36 = _703___mcc_h358;
                  if (_source36.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _704___mcc_h365 = _source36.dtor_path;
                    DAST._IType _705_b = _700___mcc_h352;
                    {
                      if (object.Equals(_705_b, _530_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _706_recursiveGen;
                        bool _707_recOwned;
                        bool _708_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _709_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out275;
                        bool _out276;
                        bool _out277;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out278;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out275, out _out276, out _out277, out _out278);
                        _706_recursiveGen = _out275;
                        _707_recOwned = _out276;
                        _708_recErased = _out277;
                        _709_recIdents = _out278;
                        Dafny.ISequence<Dafny.Rune> _710_uneraseFn;
                        _710_uneraseFn = ((_707_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _710_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _706_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _707_recOwned;
                        isErased = true;
                        readIdents = _709_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out279;
                        bool _out280;
                        bool _out281;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _705_b), _705_b, _530_toTpe), selfIdent, @params, mustOwn, out _out279, out _out280, out _out281, out _out282);
                        s = _out279;
                        isOwned = _out280;
                        isErased = _out281;
                        readIdents = _out282;
                      }
                    }
                  } else if (_source36.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _711___mcc_h368 = _source36.dtor_path;
                    DAST._IType _712_b = _700___mcc_h352;
                    {
                      if (object.Equals(_712_b, _530_toTpe)) {
                        Dafny.ISequence<Dafny.Rune> _713_recursiveGen;
                        bool _714_recOwned;
                        bool _715_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _716_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out283;
                        bool _out284;
                        bool _out285;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out283, out _out284, out _out285, out _out286);
                        _713_recursiveGen = _out283;
                        _714_recOwned = _out284;
                        _715_recErased = _out285;
                        _716_recIdents = _out286;
                        Dafny.ISequence<Dafny.Rune> _717_uneraseFn;
                        _717_uneraseFn = ((_714_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _717_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _713_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _714_recOwned;
                        isErased = true;
                        readIdents = _716_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out287;
                        bool _out288;
                        bool _out289;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _712_b), _712_b, _530_toTpe), selfIdent, @params, mustOwn, out _out287, out _out288, out _out289, out _out290);
                        s = _out287;
                        isOwned = _out288;
                        isErased = _out289;
                        readIdents = _out290;
                      }
                    }
                  } else {
                    DAST._IType _718___mcc_h371 = _source36.dtor_Newtype_a0;
                    DAST._IType _719_b = _718___mcc_h371;
                    {
                      if (object.Equals(_531_fromTpe, _719_b)) {
                        Dafny.ISequence<Dafny.Rune> _720_recursiveGen;
                        bool _721_recOwned;
                        bool _722_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _723_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out291;
                        bool _out292;
                        bool _out293;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out291, out _out292, out _out293, out _out294);
                        _720_recursiveGen = _out291;
                        _721_recOwned = _out292;
                        _722_recErased = _out293;
                        _723_recIdents = _out294;
                        Dafny.ISequence<Dafny.Rune> _724_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out295;
                        _out295 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _724_rhsType = _out295;
                        Dafny.ISequence<Dafny.Rune> _725_uneraseFn;
                        _725_uneraseFn = ((_721_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _724_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _725_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _720_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _721_recOwned;
                        isErased = false;
                        readIdents = _723_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out296;
                        bool _out297;
                        bool _out298;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _719_b), _719_b, _530_toTpe), selfIdent, @params, mustOwn, out _out296, out _out297, out _out298, out _out299);
                        s = _out296;
                        isOwned = _out297;
                        isErased = _out298;
                        readIdents = _out299;
                      }
                    }
                  }
                } else if (_source35.is_Nullable) {
                  DAST._IType _726___mcc_h374 = _source35.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _727_recursiveGen;
                    bool _728_recOwned;
                    bool _729_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _730_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out300;
                    bool _out301;
                    bool _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out300, out _out301, out _out302, out _out303);
                    _727_recursiveGen = _out300;
                    _728_recOwned = _out301;
                    _729_recErased = _out302;
                    _730_recIdents = _out303;
                    if (!(_728_recOwned)) {
                      _727_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_727_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _727_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _729_recErased;
                    readIdents = _730_recIdents;
                  }
                } else if (_source35.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _731___mcc_h377 = _source35.dtor_Tuple_a0;
                  DAST._IType _732_b = _700___mcc_h352;
                  {
                    if (object.Equals(_732_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _733_recursiveGen;
                      bool _734_recOwned;
                      bool _735_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _736_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out304;
                      bool _out305;
                      bool _out306;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out307;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out304, out _out305, out _out306, out _out307);
                      _733_recursiveGen = _out304;
                      _734_recOwned = _out305;
                      _735_recErased = _out306;
                      _736_recIdents = _out307;
                      Dafny.ISequence<Dafny.Rune> _737_uneraseFn;
                      _737_uneraseFn = ((_734_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _737_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _733_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _734_recOwned;
                      isErased = true;
                      readIdents = _736_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out308;
                      bool _out309;
                      bool _out310;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _732_b), _732_b, _530_toTpe), selfIdent, @params, mustOwn, out _out308, out _out309, out _out310, out _out311);
                      s = _out308;
                      isOwned = _out309;
                      isErased = _out310;
                      readIdents = _out311;
                    }
                  }
                } else if (_source35.is_Array) {
                  DAST._IType _738___mcc_h380 = _source35.dtor_element;
                  DAST._IType _739_b = _700___mcc_h352;
                  {
                    if (object.Equals(_739_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _740_recursiveGen;
                      bool _741_recOwned;
                      bool _742_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _743_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out312;
                      bool _out313;
                      bool _out314;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out312, out _out313, out _out314, out _out315);
                      _740_recursiveGen = _out312;
                      _741_recOwned = _out313;
                      _742_recErased = _out314;
                      _743_recIdents = _out315;
                      Dafny.ISequence<Dafny.Rune> _744_uneraseFn;
                      _744_uneraseFn = ((_741_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _744_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _740_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _741_recOwned;
                      isErased = true;
                      readIdents = _743_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out316;
                      bool _out317;
                      bool _out318;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out319;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _739_b), _739_b, _530_toTpe), selfIdent, @params, mustOwn, out _out316, out _out317, out _out318, out _out319);
                      s = _out316;
                      isOwned = _out317;
                      isErased = _out318;
                      readIdents = _out319;
                    }
                  }
                } else if (_source35.is_Seq) {
                  DAST._IType _745___mcc_h383 = _source35.dtor_element;
                  DAST._IType _746_b = _700___mcc_h352;
                  {
                    if (object.Equals(_746_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _747_recursiveGen;
                      bool _748_recOwned;
                      bool _749_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _750_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out320;
                      bool _out321;
                      bool _out322;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out320, out _out321, out _out322, out _out323);
                      _747_recursiveGen = _out320;
                      _748_recOwned = _out321;
                      _749_recErased = _out322;
                      _750_recIdents = _out323;
                      Dafny.ISequence<Dafny.Rune> _751_uneraseFn;
                      _751_uneraseFn = ((_748_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _751_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _747_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _748_recOwned;
                      isErased = true;
                      readIdents = _750_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out324;
                      bool _out325;
                      bool _out326;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _746_b), _746_b, _530_toTpe), selfIdent, @params, mustOwn, out _out324, out _out325, out _out326, out _out327);
                      s = _out324;
                      isOwned = _out325;
                      isErased = _out326;
                      readIdents = _out327;
                    }
                  }
                } else if (_source35.is_Set) {
                  DAST._IType _752___mcc_h386 = _source35.dtor_element;
                  DAST._IType _753_b = _700___mcc_h352;
                  {
                    if (object.Equals(_753_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _754_recursiveGen;
                      bool _755_recOwned;
                      bool _756_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _757_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out328;
                      bool _out329;
                      bool _out330;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out328, out _out329, out _out330, out _out331);
                      _754_recursiveGen = _out328;
                      _755_recOwned = _out329;
                      _756_recErased = _out330;
                      _757_recIdents = _out331;
                      Dafny.ISequence<Dafny.Rune> _758_uneraseFn;
                      _758_uneraseFn = ((_755_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _758_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _754_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _755_recOwned;
                      isErased = true;
                      readIdents = _757_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out332;
                      bool _out333;
                      bool _out334;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _753_b), _753_b, _530_toTpe), selfIdent, @params, mustOwn, out _out332, out _out333, out _out334, out _out335);
                      s = _out332;
                      isOwned = _out333;
                      isErased = _out334;
                      readIdents = _out335;
                    }
                  }
                } else if (_source35.is_Multiset) {
                  DAST._IType _759___mcc_h389 = _source35.dtor_element;
                  DAST._IType _760_b = _700___mcc_h352;
                  {
                    if (object.Equals(_760_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _761_recursiveGen;
                      bool _762_recOwned;
                      bool _763_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _764_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out336;
                      bool _out337;
                      bool _out338;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out336, out _out337, out _out338, out _out339);
                      _761_recursiveGen = _out336;
                      _762_recOwned = _out337;
                      _763_recErased = _out338;
                      _764_recIdents = _out339;
                      Dafny.ISequence<Dafny.Rune> _765_uneraseFn;
                      _765_uneraseFn = ((_762_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _765_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _761_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _762_recOwned;
                      isErased = true;
                      readIdents = _764_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out340;
                      bool _out341;
                      bool _out342;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out343;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _760_b), _760_b, _530_toTpe), selfIdent, @params, mustOwn, out _out340, out _out341, out _out342, out _out343);
                      s = _out340;
                      isOwned = _out341;
                      isErased = _out342;
                      readIdents = _out343;
                    }
                  }
                } else if (_source35.is_Map) {
                  DAST._IType _766___mcc_h392 = _source35.dtor_key;
                  DAST._IType _767___mcc_h393 = _source35.dtor_value;
                  DAST._IType _768_b = _700___mcc_h352;
                  {
                    if (object.Equals(_768_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _769_recursiveGen;
                      bool _770_recOwned;
                      bool _771_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _772_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out344;
                      bool _out345;
                      bool _out346;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out347;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out344, out _out345, out _out346, out _out347);
                      _769_recursiveGen = _out344;
                      _770_recOwned = _out345;
                      _771_recErased = _out346;
                      _772_recIdents = _out347;
                      Dafny.ISequence<Dafny.Rune> _773_uneraseFn;
                      _773_uneraseFn = ((_770_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _773_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _769_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _770_recOwned;
                      isErased = true;
                      readIdents = _772_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out348;
                      bool _out349;
                      bool _out350;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _768_b), _768_b, _530_toTpe), selfIdent, @params, mustOwn, out _out348, out _out349, out _out350, out _out351);
                      s = _out348;
                      isOwned = _out349;
                      isErased = _out350;
                      readIdents = _out351;
                    }
                  }
                } else if (_source35.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _774___mcc_h398 = _source35.dtor_args;
                  DAST._IType _775___mcc_h399 = _source35.dtor_result;
                  DAST._IType _776_b = _700___mcc_h352;
                  {
                    if (object.Equals(_776_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _777_recursiveGen;
                      bool _778_recOwned;
                      bool _779_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _780_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out352;
                      bool _out353;
                      bool _out354;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out355;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out352, out _out353, out _out354, out _out355);
                      _777_recursiveGen = _out352;
                      _778_recOwned = _out353;
                      _779_recErased = _out354;
                      _780_recIdents = _out355;
                      Dafny.ISequence<Dafny.Rune> _781_uneraseFn;
                      _781_uneraseFn = ((_778_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _781_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _777_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _778_recOwned;
                      isErased = true;
                      readIdents = _780_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out356;
                      bool _out357;
                      bool _out358;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out359;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _776_b), _776_b, _530_toTpe), selfIdent, @params, mustOwn, out _out356, out _out357, out _out358, out _out359);
                      s = _out356;
                      isOwned = _out357;
                      isErased = _out358;
                      readIdents = _out359;
                    }
                  }
                } else if (_source35.is_Primitive) {
                  DAST._IPrimitive _782___mcc_h404 = _source35.dtor_Primitive_a0;
                  DAST._IType _783_b = _700___mcc_h352;
                  {
                    if (object.Equals(_783_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _784_recursiveGen;
                      bool _785_recOwned;
                      bool _786_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _787_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out360;
                      bool _out361;
                      bool _out362;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out363;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out360, out _out361, out _out362, out _out363);
                      _784_recursiveGen = _out360;
                      _785_recOwned = _out361;
                      _786_recErased = _out362;
                      _787_recIdents = _out363;
                      Dafny.ISequence<Dafny.Rune> _788_uneraseFn;
                      _788_uneraseFn = ((_785_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _788_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _784_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _785_recOwned;
                      isErased = true;
                      readIdents = _787_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out364;
                      bool _out365;
                      bool _out366;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _783_b), _783_b, _530_toTpe), selfIdent, @params, mustOwn, out _out364, out _out365, out _out366, out _out367);
                      s = _out364;
                      isOwned = _out365;
                      isErased = _out366;
                      readIdents = _out367;
                    }
                  }
                } else if (_source35.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _789___mcc_h407 = _source35.dtor_Passthrough_a0;
                  DAST._IType _790_b = _700___mcc_h352;
                  {
                    if (object.Equals(_790_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _791_recursiveGen;
                      bool _792_recOwned;
                      bool _793_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _794_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out368;
                      bool _out369;
                      bool _out370;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out368, out _out369, out _out370, out _out371);
                      _791_recursiveGen = _out368;
                      _792_recOwned = _out369;
                      _793_recErased = _out370;
                      _794_recIdents = _out371;
                      Dafny.ISequence<Dafny.Rune> _795_uneraseFn;
                      _795_uneraseFn = ((_792_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _795_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _791_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _792_recOwned;
                      isErased = true;
                      readIdents = _794_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out372;
                      bool _out373;
                      bool _out374;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _790_b), _790_b, _530_toTpe), selfIdent, @params, mustOwn, out _out372, out _out373, out _out374, out _out375);
                      s = _out372;
                      isOwned = _out373;
                      isErased = _out374;
                      readIdents = _out375;
                    }
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _796___mcc_h410 = _source35.dtor_TypeArg_a0;
                  DAST._IType _797_b = _700___mcc_h352;
                  {
                    if (object.Equals(_797_b, _530_toTpe)) {
                      Dafny.ISequence<Dafny.Rune> _798_recursiveGen;
                      bool _799_recOwned;
                      bool _800_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _801_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out376;
                      bool _out377;
                      bool _out378;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out376, out _out377, out _out378, out _out379);
                      _798_recursiveGen = _out376;
                      _799_recOwned = _out377;
                      _800_recErased = _out378;
                      _801_recIdents = _out379;
                      Dafny.ISequence<Dafny.Rune> _802_uneraseFn;
                      _802_uneraseFn = ((_799_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _802_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _798_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _799_recOwned;
                      isErased = true;
                      readIdents = _801_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out380;
                      bool _out381;
                      bool _out382;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _797_b), _797_b, _530_toTpe), selfIdent, @params, mustOwn, out _out380, out _out381, out _out382, out _out383);
                      s = _out380;
                      isOwned = _out381;
                      isErased = _out382;
                      readIdents = _out383;
                    }
                  }
                }
              }
            } else if (_source29.is_Nullable) {
              DAST._IType _803___mcc_h413 = _source29.dtor_Nullable_a0;
              DAST._IType _source37 = _538___mcc_h253;
              if (_source37.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _804___mcc_h417 = _source37.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _805___mcc_h418 = _source37.dtor_typeArgs;
                DAST._IResolvedType _806___mcc_h419 = _source37.dtor_resolved;
                DAST._IResolvedType _source38 = _806___mcc_h419;
                if (_source38.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _807___mcc_h426 = _source38.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _808_recursiveGen;
                    bool _809_recOwned;
                    bool _810_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _811_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out384;
                    bool _out385;
                    bool _out386;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out387;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out384, out _out385, out _out386, out _out387);
                    _808_recursiveGen = _out384;
                    _809_recOwned = _out385;
                    _810_recErased = _out386;
                    _811_recIdents = _out387;
                    if (!(_809_recOwned)) {
                      _808_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_808_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_808_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _809_recOwned;
                    isErased = _810_recErased;
                    readIdents = _811_recIdents;
                  }
                } else if (_source38.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _812___mcc_h429 = _source38.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _813_recursiveGen;
                    bool _814_recOwned;
                    bool _815_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _816_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out388;
                    bool _out389;
                    bool _out390;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out388, out _out389, out _out390, out _out391);
                    _813_recursiveGen = _out388;
                    _814_recOwned = _out389;
                    _815_recErased = _out390;
                    _816_recIdents = _out391;
                    if (!(_814_recOwned)) {
                      _813_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_813_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_813_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _814_recOwned;
                    isErased = _815_recErased;
                    readIdents = _816_recIdents;
                  }
                } else {
                  DAST._IType _817___mcc_h432 = _source38.dtor_Newtype_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _818_recursiveGen;
                    bool _819_recOwned;
                    bool _820_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _821_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out392;
                    bool _out393;
                    bool _out394;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out392, out _out393, out _out394, out _out395);
                    _818_recursiveGen = _out392;
                    _819_recOwned = _out393;
                    _820_recErased = _out394;
                    _821_recIdents = _out395;
                    if (!(_819_recOwned)) {
                      _818_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_818_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(_818_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                    isOwned = _819_recOwned;
                    isErased = _820_recErased;
                    readIdents = _821_recIdents;
                  }
                }
              } else if (_source37.is_Nullable) {
                DAST._IType _822___mcc_h435 = _source37.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _823_recursiveGen;
                  bool _824_recOwned;
                  bool _825_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _826_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out396;
                  bool _out397;
                  bool _out398;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out396, out _out397, out _out398, out _out399);
                  _823_recursiveGen = _out396;
                  _824_recOwned = _out397;
                  _825_recErased = _out398;
                  _826_recIdents = _out399;
                  if (!(_824_recOwned)) {
                    _823_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_823_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_823_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _824_recOwned;
                  isErased = _825_recErased;
                  readIdents = _826_recIdents;
                }
              } else if (_source37.is_Tuple) {
                Dafny.ISequence<DAST._IType> _827___mcc_h438 = _source37.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _828_recursiveGen;
                  bool _829_recOwned;
                  bool _830_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _831_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out400;
                  bool _out401;
                  bool _out402;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out400, out _out401, out _out402, out _out403);
                  _828_recursiveGen = _out400;
                  _829_recOwned = _out401;
                  _830_recErased = _out402;
                  _831_recIdents = _out403;
                  if (!(_829_recOwned)) {
                    _828_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_828_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_828_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _829_recOwned;
                  isErased = _830_recErased;
                  readIdents = _831_recIdents;
                }
              } else if (_source37.is_Array) {
                DAST._IType _832___mcc_h441 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _833_recursiveGen;
                  bool _834_recOwned;
                  bool _835_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _836_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out404;
                  bool _out405;
                  bool _out406;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out404, out _out405, out _out406, out _out407);
                  _833_recursiveGen = _out404;
                  _834_recOwned = _out405;
                  _835_recErased = _out406;
                  _836_recIdents = _out407;
                  if (!(_834_recOwned)) {
                    _833_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_833_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_833_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _834_recOwned;
                  isErased = _835_recErased;
                  readIdents = _836_recIdents;
                }
              } else if (_source37.is_Seq) {
                DAST._IType _837___mcc_h444 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _838_recursiveGen;
                  bool _839_recOwned;
                  bool _840_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _841_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out408;
                  bool _out409;
                  bool _out410;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out411;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out408, out _out409, out _out410, out _out411);
                  _838_recursiveGen = _out408;
                  _839_recOwned = _out409;
                  _840_recErased = _out410;
                  _841_recIdents = _out411;
                  if (!(_839_recOwned)) {
                    _838_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_838_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_838_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _839_recOwned;
                  isErased = _840_recErased;
                  readIdents = _841_recIdents;
                }
              } else if (_source37.is_Set) {
                DAST._IType _842___mcc_h447 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _843_recursiveGen;
                  bool _844_recOwned;
                  bool _845_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _846_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out412;
                  bool _out413;
                  bool _out414;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out412, out _out413, out _out414, out _out415);
                  _843_recursiveGen = _out412;
                  _844_recOwned = _out413;
                  _845_recErased = _out414;
                  _846_recIdents = _out415;
                  if (!(_844_recOwned)) {
                    _843_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_843_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_843_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _844_recOwned;
                  isErased = _845_recErased;
                  readIdents = _846_recIdents;
                }
              } else if (_source37.is_Multiset) {
                DAST._IType _847___mcc_h450 = _source37.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _848_recursiveGen;
                  bool _849_recOwned;
                  bool _850_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _851_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out416;
                  bool _out417;
                  bool _out418;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out416, out _out417, out _out418, out _out419);
                  _848_recursiveGen = _out416;
                  _849_recOwned = _out417;
                  _850_recErased = _out418;
                  _851_recIdents = _out419;
                  if (!(_849_recOwned)) {
                    _848_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_848_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_848_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _849_recOwned;
                  isErased = _850_recErased;
                  readIdents = _851_recIdents;
                }
              } else if (_source37.is_Map) {
                DAST._IType _852___mcc_h453 = _source37.dtor_key;
                DAST._IType _853___mcc_h454 = _source37.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _854_recursiveGen;
                  bool _855_recOwned;
                  bool _856_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _857_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out420;
                  bool _out421;
                  bool _out422;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out420, out _out421, out _out422, out _out423);
                  _854_recursiveGen = _out420;
                  _855_recOwned = _out421;
                  _856_recErased = _out422;
                  _857_recIdents = _out423;
                  if (!(_855_recOwned)) {
                    _854_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_854_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_854_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _855_recOwned;
                  isErased = _856_recErased;
                  readIdents = _857_recIdents;
                }
              } else if (_source37.is_Arrow) {
                Dafny.ISequence<DAST._IType> _858___mcc_h459 = _source37.dtor_args;
                DAST._IType _859___mcc_h460 = _source37.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _860_recursiveGen;
                  bool _861_recOwned;
                  bool _862_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _863_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out424;
                  bool _out425;
                  bool _out426;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out424, out _out425, out _out426, out _out427);
                  _860_recursiveGen = _out424;
                  _861_recOwned = _out425;
                  _862_recErased = _out426;
                  _863_recIdents = _out427;
                  if (!(_861_recOwned)) {
                    _860_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_860_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_860_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _861_recOwned;
                  isErased = _862_recErased;
                  readIdents = _863_recIdents;
                }
              } else if (_source37.is_Primitive) {
                DAST._IPrimitive _864___mcc_h465 = _source37.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _865_recursiveGen;
                  bool _866_recOwned;
                  bool _867_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _868_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out428;
                  bool _out429;
                  bool _out430;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out428, out _out429, out _out430, out _out431);
                  _865_recursiveGen = _out428;
                  _866_recOwned = _out429;
                  _867_recErased = _out430;
                  _868_recIdents = _out431;
                  if (!(_866_recOwned)) {
                    _865_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_865_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_865_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _866_recOwned;
                  isErased = _867_recErased;
                  readIdents = _868_recIdents;
                }
              } else if (_source37.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _869___mcc_h468 = _source37.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _870_recursiveGen;
                  bool _871_recOwned;
                  bool _872_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _873_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out432;
                  bool _out433;
                  bool _out434;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out432, out _out433, out _out434, out _out435);
                  _870_recursiveGen = _out432;
                  _871_recOwned = _out433;
                  _872_recErased = _out434;
                  _873_recIdents = _out435;
                  if (!(_871_recOwned)) {
                    _870_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_870_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_870_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _871_recOwned;
                  isErased = _872_recErased;
                  readIdents = _873_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _874___mcc_h471 = _source37.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _875_recursiveGen;
                  bool _876_recOwned;
                  bool _877_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _878_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out436;
                  bool _out437;
                  bool _out438;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out436, out _out437, out _out438, out _out439);
                  _875_recursiveGen = _out436;
                  _876_recOwned = _out437;
                  _877_recErased = _out438;
                  _878_recIdents = _out439;
                  if (!(_876_recOwned)) {
                    _875_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_875_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(_875_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap()"));
                  isOwned = _876_recOwned;
                  isErased = _877_recErased;
                  readIdents = _878_recIdents;
                }
              }
            } else if (_source29.is_Tuple) {
              Dafny.ISequence<DAST._IType> _879___mcc_h474 = _source29.dtor_Tuple_a0;
              DAST._IType _source39 = _538___mcc_h253;
              if (_source39.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _880___mcc_h478 = _source39.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _881___mcc_h479 = _source39.dtor_typeArgs;
                DAST._IResolvedType _882___mcc_h480 = _source39.dtor_resolved;
                DAST._IResolvedType _source40 = _882___mcc_h480;
                if (_source40.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _883___mcc_h484 = _source40.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _884_recursiveGen;
                    bool _885_recOwned;
                    bool _886_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _887_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out440;
                    bool _out441;
                    bool _out442;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out440, out _out441, out _out442, out _out443);
                    _884_recursiveGen = _out440;
                    _885_recOwned = _out441;
                    _886_recErased = _out442;
                    _887_recIdents = _out443;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _884_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _885_recOwned;
                    isErased = _886_recErased;
                    readIdents = _887_recIdents;
                  }
                } else if (_source40.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _888___mcc_h486 = _source40.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _889_recursiveGen;
                    bool _890_recOwned;
                    bool _891_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _892_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out444;
                    bool _out445;
                    bool _out446;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out444, out _out445, out _out446, out _out447);
                    _889_recursiveGen = _out444;
                    _890_recOwned = _out445;
                    _891_recErased = _out446;
                    _892_recIdents = _out447;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _889_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _890_recOwned;
                    isErased = _891_recErased;
                    readIdents = _892_recIdents;
                  }
                } else {
                  DAST._IType _893___mcc_h488 = _source40.dtor_Newtype_a0;
                  DAST._IType _894_b = _893___mcc_h488;
                  {
                    if (object.Equals(_531_fromTpe, _894_b)) {
                      Dafny.ISequence<Dafny.Rune> _895_recursiveGen;
                      bool _896_recOwned;
                      bool _897_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _898_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out448;
                      bool _out449;
                      bool _out450;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out448, out _out449, out _out450, out _out451);
                      _895_recursiveGen = _out448;
                      _896_recOwned = _out449;
                      _897_recErased = _out450;
                      _898_recIdents = _out451;
                      Dafny.ISequence<Dafny.Rune> _899_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out452;
                      _out452 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _899_rhsType = _out452;
                      Dafny.ISequence<Dafny.Rune> _900_uneraseFn;
                      _900_uneraseFn = ((_896_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _899_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _900_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _895_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _896_recOwned;
                      isErased = false;
                      readIdents = _898_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out453;
                      bool _out454;
                      bool _out455;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out456;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _894_b), _894_b, _530_toTpe), selfIdent, @params, mustOwn, out _out453, out _out454, out _out455, out _out456);
                      s = _out453;
                      isOwned = _out454;
                      isErased = _out455;
                      readIdents = _out456;
                    }
                  }
                }
              } else if (_source39.is_Nullable) {
                DAST._IType _901___mcc_h490 = _source39.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _902_recursiveGen;
                  bool _903_recOwned;
                  bool _904_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _905_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out457;
                  bool _out458;
                  bool _out459;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out457, out _out458, out _out459, out _out460);
                  _902_recursiveGen = _out457;
                  _903_recOwned = _out458;
                  _904_recErased = _out459;
                  _905_recIdents = _out460;
                  if (!(_903_recOwned)) {
                    _902_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_902_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _902_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _904_recErased;
                  readIdents = _905_recIdents;
                }
              } else if (_source39.is_Tuple) {
                Dafny.ISequence<DAST._IType> _906___mcc_h492 = _source39.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _907_recursiveGen;
                  bool _908_recOwned;
                  bool _909_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _910_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out461;
                  bool _out462;
                  bool _out463;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out461, out _out462, out _out463, out _out464);
                  _907_recursiveGen = _out461;
                  _908_recOwned = _out462;
                  _909_recErased = _out463;
                  _910_recIdents = _out464;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _907_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _908_recOwned;
                  isErased = _909_recErased;
                  readIdents = _910_recIdents;
                }
              } else if (_source39.is_Array) {
                DAST._IType _911___mcc_h494 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _912_recursiveGen;
                  bool _913_recOwned;
                  bool _914_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _915_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out465;
                  bool _out466;
                  bool _out467;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out465, out _out466, out _out467, out _out468);
                  _912_recursiveGen = _out465;
                  _913_recOwned = _out466;
                  _914_recErased = _out467;
                  _915_recIdents = _out468;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _912_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _913_recOwned;
                  isErased = _914_recErased;
                  readIdents = _915_recIdents;
                }
              } else if (_source39.is_Seq) {
                DAST._IType _916___mcc_h496 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _917_recursiveGen;
                  bool _918_recOwned;
                  bool _919_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _920_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out469;
                  bool _out470;
                  bool _out471;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out472;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out469, out _out470, out _out471, out _out472);
                  _917_recursiveGen = _out469;
                  _918_recOwned = _out470;
                  _919_recErased = _out471;
                  _920_recIdents = _out472;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _917_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _918_recOwned;
                  isErased = _919_recErased;
                  readIdents = _920_recIdents;
                }
              } else if (_source39.is_Set) {
                DAST._IType _921___mcc_h498 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _922_recursiveGen;
                  bool _923_recOwned;
                  bool _924_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _925_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out473;
                  bool _out474;
                  bool _out475;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out473, out _out474, out _out475, out _out476);
                  _922_recursiveGen = _out473;
                  _923_recOwned = _out474;
                  _924_recErased = _out475;
                  _925_recIdents = _out476;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _922_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _923_recOwned;
                  isErased = _924_recErased;
                  readIdents = _925_recIdents;
                }
              } else if (_source39.is_Multiset) {
                DAST._IType _926___mcc_h500 = _source39.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _927_recursiveGen;
                  bool _928_recOwned;
                  bool _929_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _930_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out477;
                  bool _out478;
                  bool _out479;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out477, out _out478, out _out479, out _out480);
                  _927_recursiveGen = _out477;
                  _928_recOwned = _out478;
                  _929_recErased = _out479;
                  _930_recIdents = _out480;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _927_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _928_recOwned;
                  isErased = _929_recErased;
                  readIdents = _930_recIdents;
                }
              } else if (_source39.is_Map) {
                DAST._IType _931___mcc_h502 = _source39.dtor_key;
                DAST._IType _932___mcc_h503 = _source39.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _933_recursiveGen;
                  bool _934_recOwned;
                  bool _935_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _936_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out481;
                  bool _out482;
                  bool _out483;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out481, out _out482, out _out483, out _out484);
                  _933_recursiveGen = _out481;
                  _934_recOwned = _out482;
                  _935_recErased = _out483;
                  _936_recIdents = _out484;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _933_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _934_recOwned;
                  isErased = _935_recErased;
                  readIdents = _936_recIdents;
                }
              } else if (_source39.is_Arrow) {
                Dafny.ISequence<DAST._IType> _937___mcc_h506 = _source39.dtor_args;
                DAST._IType _938___mcc_h507 = _source39.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _939_recursiveGen;
                  bool _940_recOwned;
                  bool _941_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _942_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out485;
                  bool _out486;
                  bool _out487;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out488;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out485, out _out486, out _out487, out _out488);
                  _939_recursiveGen = _out485;
                  _940_recOwned = _out486;
                  _941_recErased = _out487;
                  _942_recIdents = _out488;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _939_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _940_recOwned;
                  isErased = _941_recErased;
                  readIdents = _942_recIdents;
                }
              } else if (_source39.is_Primitive) {
                DAST._IPrimitive _943___mcc_h510 = _source39.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _944_recursiveGen;
                  bool _945_recOwned;
                  bool _946_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _947_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out489;
                  bool _out490;
                  bool _out491;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out489, out _out490, out _out491, out _out492);
                  _944_recursiveGen = _out489;
                  _945_recOwned = _out490;
                  _946_recErased = _out491;
                  _947_recIdents = _out492;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _944_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _945_recOwned;
                  isErased = _946_recErased;
                  readIdents = _947_recIdents;
                }
              } else if (_source39.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _948___mcc_h512 = _source39.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _949_recursiveGen;
                  bool _950_recOwned;
                  bool _951_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _952_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out493;
                  bool _out494;
                  bool _out495;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out493, out _out494, out _out495, out _out496);
                  _949_recursiveGen = _out493;
                  _950_recOwned = _out494;
                  _951_recErased = _out495;
                  _952_recIdents = _out496;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _949_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _950_recOwned;
                  isErased = _951_recErased;
                  readIdents = _952_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _953___mcc_h514 = _source39.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _954_recursiveGen;
                  bool _955_recOwned;
                  bool _956_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _957_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out497;
                  bool _out498;
                  bool _out499;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out497, out _out498, out _out499, out _out500);
                  _954_recursiveGen = _out497;
                  _955_recOwned = _out498;
                  _956_recErased = _out499;
                  _957_recIdents = _out500;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _954_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _955_recOwned;
                  isErased = _956_recErased;
                  readIdents = _957_recIdents;
                }
              }
            } else if (_source29.is_Array) {
              DAST._IType _958___mcc_h516 = _source29.dtor_element;
              DAST._IType _source41 = _538___mcc_h253;
              if (_source41.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _959___mcc_h520 = _source41.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _960___mcc_h521 = _source41.dtor_typeArgs;
                DAST._IResolvedType _961___mcc_h522 = _source41.dtor_resolved;
                DAST._IResolvedType _source42 = _961___mcc_h522;
                if (_source42.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _962___mcc_h526 = _source42.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _963_recursiveGen;
                    bool _964_recOwned;
                    bool _965_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _966_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out501;
                    bool _out502;
                    bool _out503;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out501, out _out502, out _out503, out _out504);
                    _963_recursiveGen = _out501;
                    _964_recOwned = _out502;
                    _965_recErased = _out503;
                    _966_recIdents = _out504;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _963_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _964_recOwned;
                    isErased = _965_recErased;
                    readIdents = _966_recIdents;
                  }
                } else if (_source42.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _967___mcc_h528 = _source42.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _968_recursiveGen;
                    bool _969_recOwned;
                    bool _970_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _971_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out505;
                    bool _out506;
                    bool _out507;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out505, out _out506, out _out507, out _out508);
                    _968_recursiveGen = _out505;
                    _969_recOwned = _out506;
                    _970_recErased = _out507;
                    _971_recIdents = _out508;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _968_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _969_recOwned;
                    isErased = _970_recErased;
                    readIdents = _971_recIdents;
                  }
                } else {
                  DAST._IType _972___mcc_h530 = _source42.dtor_Newtype_a0;
                  DAST._IType _973_b = _972___mcc_h530;
                  {
                    if (object.Equals(_531_fromTpe, _973_b)) {
                      Dafny.ISequence<Dafny.Rune> _974_recursiveGen;
                      bool _975_recOwned;
                      bool _976_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _977_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out509;
                      bool _out510;
                      bool _out511;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out509, out _out510, out _out511, out _out512);
                      _974_recursiveGen = _out509;
                      _975_recOwned = _out510;
                      _976_recErased = _out511;
                      _977_recIdents = _out512;
                      Dafny.ISequence<Dafny.Rune> _978_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out513;
                      _out513 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _978_rhsType = _out513;
                      Dafny.ISequence<Dafny.Rune> _979_uneraseFn;
                      _979_uneraseFn = ((_975_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _978_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _979_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _974_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _975_recOwned;
                      isErased = false;
                      readIdents = _977_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out514;
                      bool _out515;
                      bool _out516;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _973_b), _973_b, _530_toTpe), selfIdent, @params, mustOwn, out _out514, out _out515, out _out516, out _out517);
                      s = _out514;
                      isOwned = _out515;
                      isErased = _out516;
                      readIdents = _out517;
                    }
                  }
                }
              } else if (_source41.is_Nullable) {
                DAST._IType _980___mcc_h532 = _source41.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _981_recursiveGen;
                  bool _982_recOwned;
                  bool _983_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _984_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out518;
                  bool _out519;
                  bool _out520;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out518, out _out519, out _out520, out _out521);
                  _981_recursiveGen = _out518;
                  _982_recOwned = _out519;
                  _983_recErased = _out520;
                  _984_recIdents = _out521;
                  if (!(_982_recOwned)) {
                    _981_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_981_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _981_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _983_recErased;
                  readIdents = _984_recIdents;
                }
              } else if (_source41.is_Tuple) {
                Dafny.ISequence<DAST._IType> _985___mcc_h534 = _source41.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _986_recursiveGen;
                  bool _987_recOwned;
                  bool _988_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _989_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out522;
                  bool _out523;
                  bool _out524;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out522, out _out523, out _out524, out _out525);
                  _986_recursiveGen = _out522;
                  _987_recOwned = _out523;
                  _988_recErased = _out524;
                  _989_recIdents = _out525;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _986_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _987_recOwned;
                  isErased = _988_recErased;
                  readIdents = _989_recIdents;
                }
              } else if (_source41.is_Array) {
                DAST._IType _990___mcc_h536 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _991_recursiveGen;
                  bool _992_recOwned;
                  bool _993_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _994_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out526;
                  bool _out527;
                  bool _out528;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out526, out _out527, out _out528, out _out529);
                  _991_recursiveGen = _out526;
                  _992_recOwned = _out527;
                  _993_recErased = _out528;
                  _994_recIdents = _out529;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _991_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _992_recOwned;
                  isErased = _993_recErased;
                  readIdents = _994_recIdents;
                }
              } else if (_source41.is_Seq) {
                DAST._IType _995___mcc_h538 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _996_recursiveGen;
                  bool _997_recOwned;
                  bool _998_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _999_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out530;
                  bool _out531;
                  bool _out532;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out530, out _out531, out _out532, out _out533);
                  _996_recursiveGen = _out530;
                  _997_recOwned = _out531;
                  _998_recErased = _out532;
                  _999_recIdents = _out533;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _996_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _997_recOwned;
                  isErased = _998_recErased;
                  readIdents = _999_recIdents;
                }
              } else if (_source41.is_Set) {
                DAST._IType _1000___mcc_h540 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1001_recursiveGen;
                  bool _1002_recOwned;
                  bool _1003_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1004_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out534;
                  bool _out535;
                  bool _out536;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out537;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out534, out _out535, out _out536, out _out537);
                  _1001_recursiveGen = _out534;
                  _1002_recOwned = _out535;
                  _1003_recErased = _out536;
                  _1004_recIdents = _out537;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1001_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1002_recOwned;
                  isErased = _1003_recErased;
                  readIdents = _1004_recIdents;
                }
              } else if (_source41.is_Multiset) {
                DAST._IType _1005___mcc_h542 = _source41.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1006_recursiveGen;
                  bool _1007_recOwned;
                  bool _1008_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1009_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out538;
                  bool _out539;
                  bool _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out538, out _out539, out _out540, out _out541);
                  _1006_recursiveGen = _out538;
                  _1007_recOwned = _out539;
                  _1008_recErased = _out540;
                  _1009_recIdents = _out541;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1006_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1007_recOwned;
                  isErased = _1008_recErased;
                  readIdents = _1009_recIdents;
                }
              } else if (_source41.is_Map) {
                DAST._IType _1010___mcc_h544 = _source41.dtor_key;
                DAST._IType _1011___mcc_h545 = _source41.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1012_recursiveGen;
                  bool _1013_recOwned;
                  bool _1014_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1015_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out542;
                  bool _out543;
                  bool _out544;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out542, out _out543, out _out544, out _out545);
                  _1012_recursiveGen = _out542;
                  _1013_recOwned = _out543;
                  _1014_recErased = _out544;
                  _1015_recIdents = _out545;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1012_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1013_recOwned;
                  isErased = _1014_recErased;
                  readIdents = _1015_recIdents;
                }
              } else if (_source41.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1016___mcc_h548 = _source41.dtor_args;
                DAST._IType _1017___mcc_h549 = _source41.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1018_recursiveGen;
                  bool _1019_recOwned;
                  bool _1020_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1021_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out546;
                  bool _out547;
                  bool _out548;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out546, out _out547, out _out548, out _out549);
                  _1018_recursiveGen = _out546;
                  _1019_recOwned = _out547;
                  _1020_recErased = _out548;
                  _1021_recIdents = _out549;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1018_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1019_recOwned;
                  isErased = _1020_recErased;
                  readIdents = _1021_recIdents;
                }
              } else if (_source41.is_Primitive) {
                DAST._IPrimitive _1022___mcc_h552 = _source41.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1023_recursiveGen;
                  bool _1024_recOwned;
                  bool _1025_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1026_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out550;
                  bool _out551;
                  bool _out552;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out550, out _out551, out _out552, out _out553);
                  _1023_recursiveGen = _out550;
                  _1024_recOwned = _out551;
                  _1025_recErased = _out552;
                  _1026_recIdents = _out553;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1023_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1024_recOwned;
                  isErased = _1025_recErased;
                  readIdents = _1026_recIdents;
                }
              } else if (_source41.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1027___mcc_h554 = _source41.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1028_recursiveGen;
                  bool _1029_recOwned;
                  bool _1030_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1031_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out554;
                  bool _out555;
                  bool _out556;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out554, out _out555, out _out556, out _out557);
                  _1028_recursiveGen = _out554;
                  _1029_recOwned = _out555;
                  _1030_recErased = _out556;
                  _1031_recIdents = _out557;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1028_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1029_recOwned;
                  isErased = _1030_recErased;
                  readIdents = _1031_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1032___mcc_h556 = _source41.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1033_recursiveGen;
                  bool _1034_recOwned;
                  bool _1035_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1036_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out558;
                  bool _out559;
                  bool _out560;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out561;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out558, out _out559, out _out560, out _out561);
                  _1033_recursiveGen = _out558;
                  _1034_recOwned = _out559;
                  _1035_recErased = _out560;
                  _1036_recIdents = _out561;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1033_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1034_recOwned;
                  isErased = _1035_recErased;
                  readIdents = _1036_recIdents;
                }
              }
            } else if (_source29.is_Seq) {
              DAST._IType _1037___mcc_h558 = _source29.dtor_element;
              DAST._IType _source43 = _538___mcc_h253;
              if (_source43.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1038___mcc_h562 = _source43.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1039___mcc_h563 = _source43.dtor_typeArgs;
                DAST._IResolvedType _1040___mcc_h564 = _source43.dtor_resolved;
                DAST._IResolvedType _source44 = _1040___mcc_h564;
                if (_source44.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1041___mcc_h568 = _source44.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1042_recursiveGen;
                    bool _1043_recOwned;
                    bool _1044_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1045_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out562;
                    bool _out563;
                    bool _out564;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out562, out _out563, out _out564, out _out565);
                    _1042_recursiveGen = _out562;
                    _1043_recOwned = _out563;
                    _1044_recErased = _out564;
                    _1045_recIdents = _out565;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1042_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1043_recOwned;
                    isErased = _1044_recErased;
                    readIdents = _1045_recIdents;
                  }
                } else if (_source44.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1046___mcc_h570 = _source44.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1047_recursiveGen;
                    bool _1048_recOwned;
                    bool _1049_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1050_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out566;
                    bool _out567;
                    bool _out568;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out566, out _out567, out _out568, out _out569);
                    _1047_recursiveGen = _out566;
                    _1048_recOwned = _out567;
                    _1049_recErased = _out568;
                    _1050_recIdents = _out569;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1047_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1048_recOwned;
                    isErased = _1049_recErased;
                    readIdents = _1050_recIdents;
                  }
                } else {
                  DAST._IType _1051___mcc_h572 = _source44.dtor_Newtype_a0;
                  DAST._IType _1052_b = _1051___mcc_h572;
                  {
                    if (object.Equals(_531_fromTpe, _1052_b)) {
                      Dafny.ISequence<Dafny.Rune> _1053_recursiveGen;
                      bool _1054_recOwned;
                      bool _1055_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1056_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out570;
                      bool _out571;
                      bool _out572;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out573;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out570, out _out571, out _out572, out _out573);
                      _1053_recursiveGen = _out570;
                      _1054_recOwned = _out571;
                      _1055_recErased = _out572;
                      _1056_recIdents = _out573;
                      Dafny.ISequence<Dafny.Rune> _1057_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out574;
                      _out574 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1057_rhsType = _out574;
                      Dafny.ISequence<Dafny.Rune> _1058_uneraseFn;
                      _1058_uneraseFn = ((_1054_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1057_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1058_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1053_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1054_recOwned;
                      isErased = false;
                      readIdents = _1056_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out575;
                      bool _out576;
                      bool _out577;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1052_b), _1052_b, _530_toTpe), selfIdent, @params, mustOwn, out _out575, out _out576, out _out577, out _out578);
                      s = _out575;
                      isOwned = _out576;
                      isErased = _out577;
                      readIdents = _out578;
                    }
                  }
                }
              } else if (_source43.is_Nullable) {
                DAST._IType _1059___mcc_h574 = _source43.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1060_recursiveGen;
                  bool _1061_recOwned;
                  bool _1062_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1063_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out579;
                  bool _out580;
                  bool _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out579, out _out580, out _out581, out _out582);
                  _1060_recursiveGen = _out579;
                  _1061_recOwned = _out580;
                  _1062_recErased = _out581;
                  _1063_recIdents = _out582;
                  if (!(_1061_recOwned)) {
                    _1060_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1060_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1060_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1062_recErased;
                  readIdents = _1063_recIdents;
                }
              } else if (_source43.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1064___mcc_h576 = _source43.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1065_recursiveGen;
                  bool _1066_recOwned;
                  bool _1067_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1068_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out583;
                  bool _out584;
                  bool _out585;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out583, out _out584, out _out585, out _out586);
                  _1065_recursiveGen = _out583;
                  _1066_recOwned = _out584;
                  _1067_recErased = _out585;
                  _1068_recIdents = _out586;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1065_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1066_recOwned;
                  isErased = _1067_recErased;
                  readIdents = _1068_recIdents;
                }
              } else if (_source43.is_Array) {
                DAST._IType _1069___mcc_h578 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1070_recursiveGen;
                  bool _1071_recOwned;
                  bool _1072_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1073_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out587;
                  bool _out588;
                  bool _out589;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out587, out _out588, out _out589, out _out590);
                  _1070_recursiveGen = _out587;
                  _1071_recOwned = _out588;
                  _1072_recErased = _out589;
                  _1073_recIdents = _out590;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1070_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1071_recOwned;
                  isErased = _1072_recErased;
                  readIdents = _1073_recIdents;
                }
              } else if (_source43.is_Seq) {
                DAST._IType _1074___mcc_h580 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1075_recursiveGen;
                  bool _1076_recOwned;
                  bool _1077_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1078_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out591;
                  bool _out592;
                  bool _out593;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out591, out _out592, out _out593, out _out594);
                  _1075_recursiveGen = _out591;
                  _1076_recOwned = _out592;
                  _1077_recErased = _out593;
                  _1078_recIdents = _out594;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1075_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1076_recOwned;
                  isErased = _1077_recErased;
                  readIdents = _1078_recIdents;
                }
              } else if (_source43.is_Set) {
                DAST._IType _1079___mcc_h582 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1080_recursiveGen;
                  bool _1081_recOwned;
                  bool _1082_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1083_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out595;
                  bool _out596;
                  bool _out597;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out595, out _out596, out _out597, out _out598);
                  _1080_recursiveGen = _out595;
                  _1081_recOwned = _out596;
                  _1082_recErased = _out597;
                  _1083_recIdents = _out598;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1080_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1081_recOwned;
                  isErased = _1082_recErased;
                  readIdents = _1083_recIdents;
                }
              } else if (_source43.is_Multiset) {
                DAST._IType _1084___mcc_h584 = _source43.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1085_recursiveGen;
                  bool _1086_recOwned;
                  bool _1087_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1088_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out599;
                  bool _out600;
                  bool _out601;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out599, out _out600, out _out601, out _out602);
                  _1085_recursiveGen = _out599;
                  _1086_recOwned = _out600;
                  _1087_recErased = _out601;
                  _1088_recIdents = _out602;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1085_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1086_recOwned;
                  isErased = _1087_recErased;
                  readIdents = _1088_recIdents;
                }
              } else if (_source43.is_Map) {
                DAST._IType _1089___mcc_h586 = _source43.dtor_key;
                DAST._IType _1090___mcc_h587 = _source43.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1091_recursiveGen;
                  bool _1092_recOwned;
                  bool _1093_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1094_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out603;
                  bool _out604;
                  bool _out605;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out603, out _out604, out _out605, out _out606);
                  _1091_recursiveGen = _out603;
                  _1092_recOwned = _out604;
                  _1093_recErased = _out605;
                  _1094_recIdents = _out606;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1091_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1092_recOwned;
                  isErased = _1093_recErased;
                  readIdents = _1094_recIdents;
                }
              } else if (_source43.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1095___mcc_h590 = _source43.dtor_args;
                DAST._IType _1096___mcc_h591 = _source43.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1097_recursiveGen;
                  bool _1098_recOwned;
                  bool _1099_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1100_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out607;
                  bool _out608;
                  bool _out609;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out607, out _out608, out _out609, out _out610);
                  _1097_recursiveGen = _out607;
                  _1098_recOwned = _out608;
                  _1099_recErased = _out609;
                  _1100_recIdents = _out610;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1097_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1098_recOwned;
                  isErased = _1099_recErased;
                  readIdents = _1100_recIdents;
                }
              } else if (_source43.is_Primitive) {
                DAST._IPrimitive _1101___mcc_h594 = _source43.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1102_recursiveGen;
                  bool _1103_recOwned;
                  bool _1104_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1105_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out611;
                  bool _out612;
                  bool _out613;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out611, out _out612, out _out613, out _out614);
                  _1102_recursiveGen = _out611;
                  _1103_recOwned = _out612;
                  _1104_recErased = _out613;
                  _1105_recIdents = _out614;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1102_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1103_recOwned;
                  isErased = _1104_recErased;
                  readIdents = _1105_recIdents;
                }
              } else if (_source43.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1106___mcc_h596 = _source43.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1107_recursiveGen;
                  bool _1108_recOwned;
                  bool _1109_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1110_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out615;
                  bool _out616;
                  bool _out617;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out618;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out615, out _out616, out _out617, out _out618);
                  _1107_recursiveGen = _out615;
                  _1108_recOwned = _out616;
                  _1109_recErased = _out617;
                  _1110_recIdents = _out618;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1107_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1108_recOwned;
                  isErased = _1109_recErased;
                  readIdents = _1110_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1111___mcc_h598 = _source43.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1112_recursiveGen;
                  bool _1113_recOwned;
                  bool _1114_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1115_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out619;
                  bool _out620;
                  bool _out621;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out619, out _out620, out _out621, out _out622);
                  _1112_recursiveGen = _out619;
                  _1113_recOwned = _out620;
                  _1114_recErased = _out621;
                  _1115_recIdents = _out622;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1112_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1113_recOwned;
                  isErased = _1114_recErased;
                  readIdents = _1115_recIdents;
                }
              }
            } else if (_source29.is_Set) {
              DAST._IType _1116___mcc_h600 = _source29.dtor_element;
              DAST._IType _source45 = _538___mcc_h253;
              if (_source45.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1117___mcc_h604 = _source45.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1118___mcc_h605 = _source45.dtor_typeArgs;
                DAST._IResolvedType _1119___mcc_h606 = _source45.dtor_resolved;
                DAST._IResolvedType _source46 = _1119___mcc_h606;
                if (_source46.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1120___mcc_h610 = _source46.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1121_recursiveGen;
                    bool _1122_recOwned;
                    bool _1123_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1124_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out623;
                    bool _out624;
                    bool _out625;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out626;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out623, out _out624, out _out625, out _out626);
                    _1121_recursiveGen = _out623;
                    _1122_recOwned = _out624;
                    _1123_recErased = _out625;
                    _1124_recIdents = _out626;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1121_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1122_recOwned;
                    isErased = _1123_recErased;
                    readIdents = _1124_recIdents;
                  }
                } else if (_source46.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1125___mcc_h612 = _source46.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1126_recursiveGen;
                    bool _1127_recOwned;
                    bool _1128_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1129_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out627;
                    bool _out628;
                    bool _out629;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out627, out _out628, out _out629, out _out630);
                    _1126_recursiveGen = _out627;
                    _1127_recOwned = _out628;
                    _1128_recErased = _out629;
                    _1129_recIdents = _out630;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1126_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1127_recOwned;
                    isErased = _1128_recErased;
                    readIdents = _1129_recIdents;
                  }
                } else {
                  DAST._IType _1130___mcc_h614 = _source46.dtor_Newtype_a0;
                  DAST._IType _1131_b = _1130___mcc_h614;
                  {
                    if (object.Equals(_531_fromTpe, _1131_b)) {
                      Dafny.ISequence<Dafny.Rune> _1132_recursiveGen;
                      bool _1133_recOwned;
                      bool _1134_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1135_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out631;
                      bool _out632;
                      bool _out633;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out631, out _out632, out _out633, out _out634);
                      _1132_recursiveGen = _out631;
                      _1133_recOwned = _out632;
                      _1134_recErased = _out633;
                      _1135_recIdents = _out634;
                      Dafny.ISequence<Dafny.Rune> _1136_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out635;
                      _out635 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1136_rhsType = _out635;
                      Dafny.ISequence<Dafny.Rune> _1137_uneraseFn;
                      _1137_uneraseFn = ((_1133_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1136_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1137_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1132_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1133_recOwned;
                      isErased = false;
                      readIdents = _1135_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out636;
                      bool _out637;
                      bool _out638;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out639;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1131_b), _1131_b, _530_toTpe), selfIdent, @params, mustOwn, out _out636, out _out637, out _out638, out _out639);
                      s = _out636;
                      isOwned = _out637;
                      isErased = _out638;
                      readIdents = _out639;
                    }
                  }
                }
              } else if (_source45.is_Nullable) {
                DAST._IType _1138___mcc_h616 = _source45.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1139_recursiveGen;
                  bool _1140_recOwned;
                  bool _1141_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1142_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out640;
                  bool _out641;
                  bool _out642;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out640, out _out641, out _out642, out _out643);
                  _1139_recursiveGen = _out640;
                  _1140_recOwned = _out641;
                  _1141_recErased = _out642;
                  _1142_recIdents = _out643;
                  if (!(_1140_recOwned)) {
                    _1139_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1139_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1139_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1141_recErased;
                  readIdents = _1142_recIdents;
                }
              } else if (_source45.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1143___mcc_h618 = _source45.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1144_recursiveGen;
                  bool _1145_recOwned;
                  bool _1146_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1147_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out644;
                  bool _out645;
                  bool _out646;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out644, out _out645, out _out646, out _out647);
                  _1144_recursiveGen = _out644;
                  _1145_recOwned = _out645;
                  _1146_recErased = _out646;
                  _1147_recIdents = _out647;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1144_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1145_recOwned;
                  isErased = _1146_recErased;
                  readIdents = _1147_recIdents;
                }
              } else if (_source45.is_Array) {
                DAST._IType _1148___mcc_h620 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1149_recursiveGen;
                  bool _1150_recOwned;
                  bool _1151_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1152_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out648;
                  bool _out649;
                  bool _out650;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out651;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out648, out _out649, out _out650, out _out651);
                  _1149_recursiveGen = _out648;
                  _1150_recOwned = _out649;
                  _1151_recErased = _out650;
                  _1152_recIdents = _out651;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1149_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1150_recOwned;
                  isErased = _1151_recErased;
                  readIdents = _1152_recIdents;
                }
              } else if (_source45.is_Seq) {
                DAST._IType _1153___mcc_h622 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1154_recursiveGen;
                  bool _1155_recOwned;
                  bool _1156_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1157_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out652;
                  bool _out653;
                  bool _out654;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out652, out _out653, out _out654, out _out655);
                  _1154_recursiveGen = _out652;
                  _1155_recOwned = _out653;
                  _1156_recErased = _out654;
                  _1157_recIdents = _out655;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1154_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1155_recOwned;
                  isErased = _1156_recErased;
                  readIdents = _1157_recIdents;
                }
              } else if (_source45.is_Set) {
                DAST._IType _1158___mcc_h624 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1159_recursiveGen;
                  bool _1160_recOwned;
                  bool _1161_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1162_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out656;
                  bool _out657;
                  bool _out658;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out659;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out656, out _out657, out _out658, out _out659);
                  _1159_recursiveGen = _out656;
                  _1160_recOwned = _out657;
                  _1161_recErased = _out658;
                  _1162_recIdents = _out659;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1159_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1160_recOwned;
                  isErased = _1161_recErased;
                  readIdents = _1162_recIdents;
                }
              } else if (_source45.is_Multiset) {
                DAST._IType _1163___mcc_h626 = _source45.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1164_recursiveGen;
                  bool _1165_recOwned;
                  bool _1166_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1167_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out660;
                  bool _out661;
                  bool _out662;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out660, out _out661, out _out662, out _out663);
                  _1164_recursiveGen = _out660;
                  _1165_recOwned = _out661;
                  _1166_recErased = _out662;
                  _1167_recIdents = _out663;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1164_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1165_recOwned;
                  isErased = _1166_recErased;
                  readIdents = _1167_recIdents;
                }
              } else if (_source45.is_Map) {
                DAST._IType _1168___mcc_h628 = _source45.dtor_key;
                DAST._IType _1169___mcc_h629 = _source45.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1170_recursiveGen;
                  bool _1171_recOwned;
                  bool _1172_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1173_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out664;
                  bool _out665;
                  bool _out666;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out664, out _out665, out _out666, out _out667);
                  _1170_recursiveGen = _out664;
                  _1171_recOwned = _out665;
                  _1172_recErased = _out666;
                  _1173_recIdents = _out667;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1170_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1171_recOwned;
                  isErased = _1172_recErased;
                  readIdents = _1173_recIdents;
                }
              } else if (_source45.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1174___mcc_h632 = _source45.dtor_args;
                DAST._IType _1175___mcc_h633 = _source45.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1176_recursiveGen;
                  bool _1177_recOwned;
                  bool _1178_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1179_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out668;
                  bool _out669;
                  bool _out670;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out671;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out668, out _out669, out _out670, out _out671);
                  _1176_recursiveGen = _out668;
                  _1177_recOwned = _out669;
                  _1178_recErased = _out670;
                  _1179_recIdents = _out671;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1176_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1177_recOwned;
                  isErased = _1178_recErased;
                  readIdents = _1179_recIdents;
                }
              } else if (_source45.is_Primitive) {
                DAST._IPrimitive _1180___mcc_h636 = _source45.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1181_recursiveGen;
                  bool _1182_recOwned;
                  bool _1183_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1184_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out672;
                  bool _out673;
                  bool _out674;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out675;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out672, out _out673, out _out674, out _out675);
                  _1181_recursiveGen = _out672;
                  _1182_recOwned = _out673;
                  _1183_recErased = _out674;
                  _1184_recIdents = _out675;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1181_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1182_recOwned;
                  isErased = _1183_recErased;
                  readIdents = _1184_recIdents;
                }
              } else if (_source45.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1185___mcc_h638 = _source45.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1186_recursiveGen;
                  bool _1187_recOwned;
                  bool _1188_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1189_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out676;
                  bool _out677;
                  bool _out678;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out679;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out676, out _out677, out _out678, out _out679);
                  _1186_recursiveGen = _out676;
                  _1187_recOwned = _out677;
                  _1188_recErased = _out678;
                  _1189_recIdents = _out679;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1186_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1187_recOwned;
                  isErased = _1188_recErased;
                  readIdents = _1189_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1190___mcc_h640 = _source45.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1191_recursiveGen;
                  bool _1192_recOwned;
                  bool _1193_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1194_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out680;
                  bool _out681;
                  bool _out682;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out683;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out680, out _out681, out _out682, out _out683);
                  _1191_recursiveGen = _out680;
                  _1192_recOwned = _out681;
                  _1193_recErased = _out682;
                  _1194_recIdents = _out683;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1191_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1192_recOwned;
                  isErased = _1193_recErased;
                  readIdents = _1194_recIdents;
                }
              }
            } else if (_source29.is_Multiset) {
              DAST._IType _1195___mcc_h642 = _source29.dtor_element;
              DAST._IType _source47 = _538___mcc_h253;
              if (_source47.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1196___mcc_h646 = _source47.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1197___mcc_h647 = _source47.dtor_typeArgs;
                DAST._IResolvedType _1198___mcc_h648 = _source47.dtor_resolved;
                DAST._IResolvedType _source48 = _1198___mcc_h648;
                if (_source48.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1199___mcc_h652 = _source48.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1200_recursiveGen;
                    bool _1201_recOwned;
                    bool _1202_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1203_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out684;
                    bool _out685;
                    bool _out686;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out687;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out684, out _out685, out _out686, out _out687);
                    _1200_recursiveGen = _out684;
                    _1201_recOwned = _out685;
                    _1202_recErased = _out686;
                    _1203_recIdents = _out687;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1200_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1201_recOwned;
                    isErased = _1202_recErased;
                    readIdents = _1203_recIdents;
                  }
                } else if (_source48.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1204___mcc_h654 = _source48.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1205_recursiveGen;
                    bool _1206_recOwned;
                    bool _1207_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1208_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out688;
                    bool _out689;
                    bool _out690;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out691;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out688, out _out689, out _out690, out _out691);
                    _1205_recursiveGen = _out688;
                    _1206_recOwned = _out689;
                    _1207_recErased = _out690;
                    _1208_recIdents = _out691;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1205_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1206_recOwned;
                    isErased = _1207_recErased;
                    readIdents = _1208_recIdents;
                  }
                } else {
                  DAST._IType _1209___mcc_h656 = _source48.dtor_Newtype_a0;
                  DAST._IType _1210_b = _1209___mcc_h656;
                  {
                    if (object.Equals(_531_fromTpe, _1210_b)) {
                      Dafny.ISequence<Dafny.Rune> _1211_recursiveGen;
                      bool _1212_recOwned;
                      bool _1213_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1214_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out692;
                      bool _out693;
                      bool _out694;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out695;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out692, out _out693, out _out694, out _out695);
                      _1211_recursiveGen = _out692;
                      _1212_recOwned = _out693;
                      _1213_recErased = _out694;
                      _1214_recIdents = _out695;
                      Dafny.ISequence<Dafny.Rune> _1215_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out696;
                      _out696 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1215_rhsType = _out696;
                      Dafny.ISequence<Dafny.Rune> _1216_uneraseFn;
                      _1216_uneraseFn = ((_1212_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1215_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1216_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1211_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1212_recOwned;
                      isErased = false;
                      readIdents = _1214_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out697;
                      bool _out698;
                      bool _out699;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out700;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1210_b), _1210_b, _530_toTpe), selfIdent, @params, mustOwn, out _out697, out _out698, out _out699, out _out700);
                      s = _out697;
                      isOwned = _out698;
                      isErased = _out699;
                      readIdents = _out700;
                    }
                  }
                }
              } else if (_source47.is_Nullable) {
                DAST._IType _1217___mcc_h658 = _source47.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1218_recursiveGen;
                  bool _1219_recOwned;
                  bool _1220_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1221_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out701;
                  bool _out702;
                  bool _out703;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out704;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out701, out _out702, out _out703, out _out704);
                  _1218_recursiveGen = _out701;
                  _1219_recOwned = _out702;
                  _1220_recErased = _out703;
                  _1221_recIdents = _out704;
                  if (!(_1219_recOwned)) {
                    _1218_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1218_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1218_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1220_recErased;
                  readIdents = _1221_recIdents;
                }
              } else if (_source47.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1222___mcc_h660 = _source47.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1223_recursiveGen;
                  bool _1224_recOwned;
                  bool _1225_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1226_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out705;
                  bool _out706;
                  bool _out707;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out708;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out705, out _out706, out _out707, out _out708);
                  _1223_recursiveGen = _out705;
                  _1224_recOwned = _out706;
                  _1225_recErased = _out707;
                  _1226_recIdents = _out708;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1223_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1224_recOwned;
                  isErased = _1225_recErased;
                  readIdents = _1226_recIdents;
                }
              } else if (_source47.is_Array) {
                DAST._IType _1227___mcc_h662 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1228_recursiveGen;
                  bool _1229_recOwned;
                  bool _1230_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1231_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out709;
                  bool _out710;
                  bool _out711;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out712;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out709, out _out710, out _out711, out _out712);
                  _1228_recursiveGen = _out709;
                  _1229_recOwned = _out710;
                  _1230_recErased = _out711;
                  _1231_recIdents = _out712;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1228_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1229_recOwned;
                  isErased = _1230_recErased;
                  readIdents = _1231_recIdents;
                }
              } else if (_source47.is_Seq) {
                DAST._IType _1232___mcc_h664 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1233_recursiveGen;
                  bool _1234_recOwned;
                  bool _1235_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1236_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out713;
                  bool _out714;
                  bool _out715;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out716;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out713, out _out714, out _out715, out _out716);
                  _1233_recursiveGen = _out713;
                  _1234_recOwned = _out714;
                  _1235_recErased = _out715;
                  _1236_recIdents = _out716;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1233_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1234_recOwned;
                  isErased = _1235_recErased;
                  readIdents = _1236_recIdents;
                }
              } else if (_source47.is_Set) {
                DAST._IType _1237___mcc_h666 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1238_recursiveGen;
                  bool _1239_recOwned;
                  bool _1240_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1241_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out717;
                  bool _out718;
                  bool _out719;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out720;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out717, out _out718, out _out719, out _out720);
                  _1238_recursiveGen = _out717;
                  _1239_recOwned = _out718;
                  _1240_recErased = _out719;
                  _1241_recIdents = _out720;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1238_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1239_recOwned;
                  isErased = _1240_recErased;
                  readIdents = _1241_recIdents;
                }
              } else if (_source47.is_Multiset) {
                DAST._IType _1242___mcc_h668 = _source47.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1243_recursiveGen;
                  bool _1244_recOwned;
                  bool _1245_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1246_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out721;
                  bool _out722;
                  bool _out723;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out724;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out721, out _out722, out _out723, out _out724);
                  _1243_recursiveGen = _out721;
                  _1244_recOwned = _out722;
                  _1245_recErased = _out723;
                  _1246_recIdents = _out724;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1243_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1244_recOwned;
                  isErased = _1245_recErased;
                  readIdents = _1246_recIdents;
                }
              } else if (_source47.is_Map) {
                DAST._IType _1247___mcc_h670 = _source47.dtor_key;
                DAST._IType _1248___mcc_h671 = _source47.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1249_recursiveGen;
                  bool _1250_recOwned;
                  bool _1251_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1252_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out725;
                  bool _out726;
                  bool _out727;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out728;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out725, out _out726, out _out727, out _out728);
                  _1249_recursiveGen = _out725;
                  _1250_recOwned = _out726;
                  _1251_recErased = _out727;
                  _1252_recIdents = _out728;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1249_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1250_recOwned;
                  isErased = _1251_recErased;
                  readIdents = _1252_recIdents;
                }
              } else if (_source47.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1253___mcc_h674 = _source47.dtor_args;
                DAST._IType _1254___mcc_h675 = _source47.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1255_recursiveGen;
                  bool _1256_recOwned;
                  bool _1257_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1258_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out729;
                  bool _out730;
                  bool _out731;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out732;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out729, out _out730, out _out731, out _out732);
                  _1255_recursiveGen = _out729;
                  _1256_recOwned = _out730;
                  _1257_recErased = _out731;
                  _1258_recIdents = _out732;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1255_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1256_recOwned;
                  isErased = _1257_recErased;
                  readIdents = _1258_recIdents;
                }
              } else if (_source47.is_Primitive) {
                DAST._IPrimitive _1259___mcc_h678 = _source47.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1260_recursiveGen;
                  bool _1261_recOwned;
                  bool _1262_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1263_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out733;
                  bool _out734;
                  bool _out735;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out736;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out733, out _out734, out _out735, out _out736);
                  _1260_recursiveGen = _out733;
                  _1261_recOwned = _out734;
                  _1262_recErased = _out735;
                  _1263_recIdents = _out736;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1260_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1261_recOwned;
                  isErased = _1262_recErased;
                  readIdents = _1263_recIdents;
                }
              } else if (_source47.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1264___mcc_h680 = _source47.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1265_recursiveGen;
                  bool _1266_recOwned;
                  bool _1267_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1268_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out737;
                  bool _out738;
                  bool _out739;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out740;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out737, out _out738, out _out739, out _out740);
                  _1265_recursiveGen = _out737;
                  _1266_recOwned = _out738;
                  _1267_recErased = _out739;
                  _1268_recIdents = _out740;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1265_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1266_recOwned;
                  isErased = _1267_recErased;
                  readIdents = _1268_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1269___mcc_h682 = _source47.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1270_recursiveGen;
                  bool _1271_recOwned;
                  bool _1272_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1273_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out741;
                  bool _out742;
                  bool _out743;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out744;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out741, out _out742, out _out743, out _out744);
                  _1270_recursiveGen = _out741;
                  _1271_recOwned = _out742;
                  _1272_recErased = _out743;
                  _1273_recIdents = _out744;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1270_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1271_recOwned;
                  isErased = _1272_recErased;
                  readIdents = _1273_recIdents;
                }
              }
            } else if (_source29.is_Map) {
              DAST._IType _1274___mcc_h684 = _source29.dtor_key;
              DAST._IType _1275___mcc_h685 = _source29.dtor_value;
              DAST._IType _source49 = _538___mcc_h253;
              if (_source49.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1276___mcc_h692 = _source49.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1277___mcc_h693 = _source49.dtor_typeArgs;
                DAST._IResolvedType _1278___mcc_h694 = _source49.dtor_resolved;
                DAST._IResolvedType _source50 = _1278___mcc_h694;
                if (_source50.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1279___mcc_h698 = _source50.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1280_recursiveGen;
                    bool _1281_recOwned;
                    bool _1282_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1283_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out745;
                    bool _out746;
                    bool _out747;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out748;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out745, out _out746, out _out747, out _out748);
                    _1280_recursiveGen = _out745;
                    _1281_recOwned = _out746;
                    _1282_recErased = _out747;
                    _1283_recIdents = _out748;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1280_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1281_recOwned;
                    isErased = _1282_recErased;
                    readIdents = _1283_recIdents;
                  }
                } else if (_source50.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1284___mcc_h700 = _source50.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1285_recursiveGen;
                    bool _1286_recOwned;
                    bool _1287_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1288_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out749;
                    bool _out750;
                    bool _out751;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out752;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out749, out _out750, out _out751, out _out752);
                    _1285_recursiveGen = _out749;
                    _1286_recOwned = _out750;
                    _1287_recErased = _out751;
                    _1288_recIdents = _out752;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1285_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1286_recOwned;
                    isErased = _1287_recErased;
                    readIdents = _1288_recIdents;
                  }
                } else {
                  DAST._IType _1289___mcc_h702 = _source50.dtor_Newtype_a0;
                  DAST._IType _1290_b = _1289___mcc_h702;
                  {
                    if (object.Equals(_531_fromTpe, _1290_b)) {
                      Dafny.ISequence<Dafny.Rune> _1291_recursiveGen;
                      bool _1292_recOwned;
                      bool _1293_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1294_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out753;
                      bool _out754;
                      bool _out755;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out756;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out753, out _out754, out _out755, out _out756);
                      _1291_recursiveGen = _out753;
                      _1292_recOwned = _out754;
                      _1293_recErased = _out755;
                      _1294_recIdents = _out756;
                      Dafny.ISequence<Dafny.Rune> _1295_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out757;
                      _out757 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1295_rhsType = _out757;
                      Dafny.ISequence<Dafny.Rune> _1296_uneraseFn;
                      _1296_uneraseFn = ((_1292_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1295_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1296_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1291_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1292_recOwned;
                      isErased = false;
                      readIdents = _1294_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out758;
                      bool _out759;
                      bool _out760;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out761;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1290_b), _1290_b, _530_toTpe), selfIdent, @params, mustOwn, out _out758, out _out759, out _out760, out _out761);
                      s = _out758;
                      isOwned = _out759;
                      isErased = _out760;
                      readIdents = _out761;
                    }
                  }
                }
              } else if (_source49.is_Nullable) {
                DAST._IType _1297___mcc_h704 = _source49.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1298_recursiveGen;
                  bool _1299_recOwned;
                  bool _1300_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1301_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out762;
                  bool _out763;
                  bool _out764;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out765;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out762, out _out763, out _out764, out _out765);
                  _1298_recursiveGen = _out762;
                  _1299_recOwned = _out763;
                  _1300_recErased = _out764;
                  _1301_recIdents = _out765;
                  if (!(_1299_recOwned)) {
                    _1298_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1298_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1298_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1300_recErased;
                  readIdents = _1301_recIdents;
                }
              } else if (_source49.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1302___mcc_h706 = _source49.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1303_recursiveGen;
                  bool _1304_recOwned;
                  bool _1305_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1306_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out766;
                  bool _out767;
                  bool _out768;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out769;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out766, out _out767, out _out768, out _out769);
                  _1303_recursiveGen = _out766;
                  _1304_recOwned = _out767;
                  _1305_recErased = _out768;
                  _1306_recIdents = _out769;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1303_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1304_recOwned;
                  isErased = _1305_recErased;
                  readIdents = _1306_recIdents;
                }
              } else if (_source49.is_Array) {
                DAST._IType _1307___mcc_h708 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1308_recursiveGen;
                  bool _1309_recOwned;
                  bool _1310_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1311_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out770;
                  bool _out771;
                  bool _out772;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out773;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out770, out _out771, out _out772, out _out773);
                  _1308_recursiveGen = _out770;
                  _1309_recOwned = _out771;
                  _1310_recErased = _out772;
                  _1311_recIdents = _out773;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1308_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1309_recOwned;
                  isErased = _1310_recErased;
                  readIdents = _1311_recIdents;
                }
              } else if (_source49.is_Seq) {
                DAST._IType _1312___mcc_h710 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1313_recursiveGen;
                  bool _1314_recOwned;
                  bool _1315_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1316_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out774;
                  bool _out775;
                  bool _out776;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out777;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out774, out _out775, out _out776, out _out777);
                  _1313_recursiveGen = _out774;
                  _1314_recOwned = _out775;
                  _1315_recErased = _out776;
                  _1316_recIdents = _out777;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1313_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1314_recOwned;
                  isErased = _1315_recErased;
                  readIdents = _1316_recIdents;
                }
              } else if (_source49.is_Set) {
                DAST._IType _1317___mcc_h712 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1318_recursiveGen;
                  bool _1319_recOwned;
                  bool _1320_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1321_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out778;
                  bool _out779;
                  bool _out780;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out781;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out778, out _out779, out _out780, out _out781);
                  _1318_recursiveGen = _out778;
                  _1319_recOwned = _out779;
                  _1320_recErased = _out780;
                  _1321_recIdents = _out781;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1318_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1319_recOwned;
                  isErased = _1320_recErased;
                  readIdents = _1321_recIdents;
                }
              } else if (_source49.is_Multiset) {
                DAST._IType _1322___mcc_h714 = _source49.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1323_recursiveGen;
                  bool _1324_recOwned;
                  bool _1325_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1326_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out782;
                  bool _out783;
                  bool _out784;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out785;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out782, out _out783, out _out784, out _out785);
                  _1323_recursiveGen = _out782;
                  _1324_recOwned = _out783;
                  _1325_recErased = _out784;
                  _1326_recIdents = _out785;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1323_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1324_recOwned;
                  isErased = _1325_recErased;
                  readIdents = _1326_recIdents;
                }
              } else if (_source49.is_Map) {
                DAST._IType _1327___mcc_h716 = _source49.dtor_key;
                DAST._IType _1328___mcc_h717 = _source49.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1329_recursiveGen;
                  bool _1330_recOwned;
                  bool _1331_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1332_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out786;
                  bool _out787;
                  bool _out788;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out789;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out786, out _out787, out _out788, out _out789);
                  _1329_recursiveGen = _out786;
                  _1330_recOwned = _out787;
                  _1331_recErased = _out788;
                  _1332_recIdents = _out789;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1329_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1330_recOwned;
                  isErased = _1331_recErased;
                  readIdents = _1332_recIdents;
                }
              } else if (_source49.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1333___mcc_h720 = _source49.dtor_args;
                DAST._IType _1334___mcc_h721 = _source49.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1335_recursiveGen;
                  bool _1336_recOwned;
                  bool _1337_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1338_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out790;
                  bool _out791;
                  bool _out792;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out793;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out790, out _out791, out _out792, out _out793);
                  _1335_recursiveGen = _out790;
                  _1336_recOwned = _out791;
                  _1337_recErased = _out792;
                  _1338_recIdents = _out793;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1335_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1336_recOwned;
                  isErased = _1337_recErased;
                  readIdents = _1338_recIdents;
                }
              } else if (_source49.is_Primitive) {
                DAST._IPrimitive _1339___mcc_h724 = _source49.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1340_recursiveGen;
                  bool _1341_recOwned;
                  bool _1342_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1343_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out794;
                  bool _out795;
                  bool _out796;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out797;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out794, out _out795, out _out796, out _out797);
                  _1340_recursiveGen = _out794;
                  _1341_recOwned = _out795;
                  _1342_recErased = _out796;
                  _1343_recIdents = _out797;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1340_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1341_recOwned;
                  isErased = _1342_recErased;
                  readIdents = _1343_recIdents;
                }
              } else if (_source49.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1344___mcc_h726 = _source49.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1345_recursiveGen;
                  bool _1346_recOwned;
                  bool _1347_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1348_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out798;
                  bool _out799;
                  bool _out800;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out801;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out798, out _out799, out _out800, out _out801);
                  _1345_recursiveGen = _out798;
                  _1346_recOwned = _out799;
                  _1347_recErased = _out800;
                  _1348_recIdents = _out801;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1345_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1346_recOwned;
                  isErased = _1347_recErased;
                  readIdents = _1348_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1349___mcc_h728 = _source49.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1350_recursiveGen;
                  bool _1351_recOwned;
                  bool _1352_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1353_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out802;
                  bool _out803;
                  bool _out804;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out805;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out802, out _out803, out _out804, out _out805);
                  _1350_recursiveGen = _out802;
                  _1351_recOwned = _out803;
                  _1352_recErased = _out804;
                  _1353_recIdents = _out805;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1350_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1351_recOwned;
                  isErased = _1352_recErased;
                  readIdents = _1353_recIdents;
                }
              }
            } else if (_source29.is_Arrow) {
              Dafny.ISequence<DAST._IType> _1354___mcc_h730 = _source29.dtor_args;
              DAST._IType _1355___mcc_h731 = _source29.dtor_result;
              DAST._IType _source51 = _538___mcc_h253;
              if (_source51.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1356___mcc_h738 = _source51.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1357___mcc_h739 = _source51.dtor_typeArgs;
                DAST._IResolvedType _1358___mcc_h740 = _source51.dtor_resolved;
                DAST._IResolvedType _source52 = _1358___mcc_h740;
                if (_source52.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1359___mcc_h744 = _source52.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1360_recursiveGen;
                    bool _1361_recOwned;
                    bool _1362_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1363_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out806;
                    bool _out807;
                    bool _out808;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out809;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out806, out _out807, out _out808, out _out809);
                    _1360_recursiveGen = _out806;
                    _1361_recOwned = _out807;
                    _1362_recErased = _out808;
                    _1363_recIdents = _out809;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1360_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1361_recOwned;
                    isErased = _1362_recErased;
                    readIdents = _1363_recIdents;
                  }
                } else if (_source52.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1364___mcc_h746 = _source52.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1365_recursiveGen;
                    bool _1366_recOwned;
                    bool _1367_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1368_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out810;
                    bool _out811;
                    bool _out812;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out813;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out810, out _out811, out _out812, out _out813);
                    _1365_recursiveGen = _out810;
                    _1366_recOwned = _out811;
                    _1367_recErased = _out812;
                    _1368_recIdents = _out813;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1365_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1366_recOwned;
                    isErased = _1367_recErased;
                    readIdents = _1368_recIdents;
                  }
                } else {
                  DAST._IType _1369___mcc_h748 = _source52.dtor_Newtype_a0;
                  DAST._IType _1370_b = _1369___mcc_h748;
                  {
                    if (object.Equals(_531_fromTpe, _1370_b)) {
                      Dafny.ISequence<Dafny.Rune> _1371_recursiveGen;
                      bool _1372_recOwned;
                      bool _1373_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1374_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out814;
                      bool _out815;
                      bool _out816;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out817;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out814, out _out815, out _out816, out _out817);
                      _1371_recursiveGen = _out814;
                      _1372_recOwned = _out815;
                      _1373_recErased = _out816;
                      _1374_recIdents = _out817;
                      Dafny.ISequence<Dafny.Rune> _1375_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out818;
                      _out818 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1375_rhsType = _out818;
                      Dafny.ISequence<Dafny.Rune> _1376_uneraseFn;
                      _1376_uneraseFn = ((_1372_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1375_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1376_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1371_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1372_recOwned;
                      isErased = false;
                      readIdents = _1374_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out819;
                      bool _out820;
                      bool _out821;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out822;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1370_b), _1370_b, _530_toTpe), selfIdent, @params, mustOwn, out _out819, out _out820, out _out821, out _out822);
                      s = _out819;
                      isOwned = _out820;
                      isErased = _out821;
                      readIdents = _out822;
                    }
                  }
                }
              } else if (_source51.is_Nullable) {
                DAST._IType _1377___mcc_h750 = _source51.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1378_recursiveGen;
                  bool _1379_recOwned;
                  bool _1380_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1381_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out823;
                  bool _out824;
                  bool _out825;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out826;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out823, out _out824, out _out825, out _out826);
                  _1378_recursiveGen = _out823;
                  _1379_recOwned = _out824;
                  _1380_recErased = _out825;
                  _1381_recIdents = _out826;
                  if (!(_1379_recOwned)) {
                    _1378_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1378_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1378_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1380_recErased;
                  readIdents = _1381_recIdents;
                }
              } else if (_source51.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1382___mcc_h752 = _source51.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1383_recursiveGen;
                  bool _1384_recOwned;
                  bool _1385_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1386_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out827;
                  bool _out828;
                  bool _out829;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out830;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out827, out _out828, out _out829, out _out830);
                  _1383_recursiveGen = _out827;
                  _1384_recOwned = _out828;
                  _1385_recErased = _out829;
                  _1386_recIdents = _out830;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1383_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1384_recOwned;
                  isErased = _1385_recErased;
                  readIdents = _1386_recIdents;
                }
              } else if (_source51.is_Array) {
                DAST._IType _1387___mcc_h754 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1388_recursiveGen;
                  bool _1389_recOwned;
                  bool _1390_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1391_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out831;
                  bool _out832;
                  bool _out833;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out834;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out831, out _out832, out _out833, out _out834);
                  _1388_recursiveGen = _out831;
                  _1389_recOwned = _out832;
                  _1390_recErased = _out833;
                  _1391_recIdents = _out834;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1388_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1389_recOwned;
                  isErased = _1390_recErased;
                  readIdents = _1391_recIdents;
                }
              } else if (_source51.is_Seq) {
                DAST._IType _1392___mcc_h756 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1393_recursiveGen;
                  bool _1394_recOwned;
                  bool _1395_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1396_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out835;
                  bool _out836;
                  bool _out837;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out838;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out835, out _out836, out _out837, out _out838);
                  _1393_recursiveGen = _out835;
                  _1394_recOwned = _out836;
                  _1395_recErased = _out837;
                  _1396_recIdents = _out838;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1393_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1394_recOwned;
                  isErased = _1395_recErased;
                  readIdents = _1396_recIdents;
                }
              } else if (_source51.is_Set) {
                DAST._IType _1397___mcc_h758 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1398_recursiveGen;
                  bool _1399_recOwned;
                  bool _1400_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1401_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out839;
                  bool _out840;
                  bool _out841;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out842;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out839, out _out840, out _out841, out _out842);
                  _1398_recursiveGen = _out839;
                  _1399_recOwned = _out840;
                  _1400_recErased = _out841;
                  _1401_recIdents = _out842;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1398_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1399_recOwned;
                  isErased = _1400_recErased;
                  readIdents = _1401_recIdents;
                }
              } else if (_source51.is_Multiset) {
                DAST._IType _1402___mcc_h760 = _source51.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1403_recursiveGen;
                  bool _1404_recOwned;
                  bool _1405_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1406_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out843;
                  bool _out844;
                  bool _out845;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out846;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out843, out _out844, out _out845, out _out846);
                  _1403_recursiveGen = _out843;
                  _1404_recOwned = _out844;
                  _1405_recErased = _out845;
                  _1406_recIdents = _out846;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1403_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1404_recOwned;
                  isErased = _1405_recErased;
                  readIdents = _1406_recIdents;
                }
              } else if (_source51.is_Map) {
                DAST._IType _1407___mcc_h762 = _source51.dtor_key;
                DAST._IType _1408___mcc_h763 = _source51.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1409_recursiveGen;
                  bool _1410_recOwned;
                  bool _1411_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1412_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out847;
                  bool _out848;
                  bool _out849;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out850;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out847, out _out848, out _out849, out _out850);
                  _1409_recursiveGen = _out847;
                  _1410_recOwned = _out848;
                  _1411_recErased = _out849;
                  _1412_recIdents = _out850;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1409_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1410_recOwned;
                  isErased = _1411_recErased;
                  readIdents = _1412_recIdents;
                }
              } else if (_source51.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1413___mcc_h766 = _source51.dtor_args;
                DAST._IType _1414___mcc_h767 = _source51.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1415_recursiveGen;
                  bool _1416_recOwned;
                  bool _1417_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1418_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out851;
                  bool _out852;
                  bool _out853;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out854;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out851, out _out852, out _out853, out _out854);
                  _1415_recursiveGen = _out851;
                  _1416_recOwned = _out852;
                  _1417_recErased = _out853;
                  _1418_recIdents = _out854;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1415_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1416_recOwned;
                  isErased = _1417_recErased;
                  readIdents = _1418_recIdents;
                }
              } else if (_source51.is_Primitive) {
                DAST._IPrimitive _1419___mcc_h770 = _source51.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1420_recursiveGen;
                  bool _1421_recOwned;
                  bool _1422_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1423_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out855;
                  bool _out856;
                  bool _out857;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out858;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out855, out _out856, out _out857, out _out858);
                  _1420_recursiveGen = _out855;
                  _1421_recOwned = _out856;
                  _1422_recErased = _out857;
                  _1423_recIdents = _out858;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1420_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1421_recOwned;
                  isErased = _1422_recErased;
                  readIdents = _1423_recIdents;
                }
              } else if (_source51.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1424___mcc_h772 = _source51.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1425_recursiveGen;
                  bool _1426_recOwned;
                  bool _1427_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1428_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out859;
                  bool _out860;
                  bool _out861;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out862;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out859, out _out860, out _out861, out _out862);
                  _1425_recursiveGen = _out859;
                  _1426_recOwned = _out860;
                  _1427_recErased = _out861;
                  _1428_recIdents = _out862;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1425_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1426_recOwned;
                  isErased = _1427_recErased;
                  readIdents = _1428_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1429___mcc_h774 = _source51.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1430_recursiveGen;
                  bool _1431_recOwned;
                  bool _1432_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1433_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out863;
                  bool _out864;
                  bool _out865;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out866;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out863, out _out864, out _out865, out _out866);
                  _1430_recursiveGen = _out863;
                  _1431_recOwned = _out864;
                  _1432_recErased = _out865;
                  _1433_recIdents = _out866;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1430_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1431_recOwned;
                  isErased = _1432_recErased;
                  readIdents = _1433_recIdents;
                }
              }
            } else if (_source29.is_Primitive) {
              DAST._IPrimitive _1434___mcc_h776 = _source29.dtor_Primitive_a0;
              DAST._IPrimitive _source53 = _1434___mcc_h776;
              if (_source53.is_Int) {
                DAST._IType _source54 = _538___mcc_h253;
                if (_source54.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1435___mcc_h780 = _source54.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1436___mcc_h781 = _source54.dtor_typeArgs;
                  DAST._IResolvedType _1437___mcc_h782 = _source54.dtor_resolved;
                  DAST._IResolvedType _source55 = _1437___mcc_h782;
                  if (_source55.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1438___mcc_h786 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1439_recursiveGen;
                      bool _1440_recOwned;
                      bool _1441_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1442_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out867;
                      bool _out868;
                      bool _out869;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out870;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out867, out _out868, out _out869, out _out870);
                      _1439_recursiveGen = _out867;
                      _1440_recOwned = _out868;
                      _1441_recErased = _out869;
                      _1442_recIdents = _out870;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1439_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1440_recOwned;
                      isErased = _1441_recErased;
                      readIdents = _1442_recIdents;
                    }
                  } else if (_source55.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1443___mcc_h788 = _source55.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1444_recursiveGen;
                      bool _1445_recOwned;
                      bool _1446_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1447_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out871;
                      bool _out872;
                      bool _out873;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out874;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out871, out _out872, out _out873, out _out874);
                      _1444_recursiveGen = _out871;
                      _1445_recOwned = _out872;
                      _1446_recErased = _out873;
                      _1447_recIdents = _out874;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1444_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1445_recOwned;
                      isErased = _1446_recErased;
                      readIdents = _1447_recIdents;
                    }
                  } else {
                    DAST._IType _1448___mcc_h790 = _source55.dtor_Newtype_a0;
                    DAST._IType _1449_b = _1448___mcc_h790;
                    {
                      if (object.Equals(_531_fromTpe, _1449_b)) {
                        Dafny.ISequence<Dafny.Rune> _1450_recursiveGen;
                        bool _1451_recOwned;
                        bool _1452_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1453_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out875;
                        bool _out876;
                        bool _out877;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out878;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out875, out _out876, out _out877, out _out878);
                        _1450_recursiveGen = _out875;
                        _1451_recOwned = _out876;
                        _1452_recErased = _out877;
                        _1453_recIdents = _out878;
                        Dafny.ISequence<Dafny.Rune> _1454_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out879;
                        _out879 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _1454_rhsType = _out879;
                        Dafny.ISequence<Dafny.Rune> _1455_uneraseFn;
                        _1455_uneraseFn = ((_1451_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1454_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1455_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1450_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1451_recOwned;
                        isErased = false;
                        readIdents = _1453_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out880;
                        bool _out881;
                        bool _out882;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out883;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1449_b), _1449_b, _530_toTpe), selfIdent, @params, mustOwn, out _out880, out _out881, out _out882, out _out883);
                        s = _out880;
                        isOwned = _out881;
                        isErased = _out882;
                        readIdents = _out883;
                      }
                    }
                  }
                } else if (_source54.is_Nullable) {
                  DAST._IType _1456___mcc_h792 = _source54.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1457_recursiveGen;
                    bool _1458_recOwned;
                    bool _1459_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1460_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out884;
                    bool _out885;
                    bool _out886;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out887;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out884, out _out885, out _out886, out _out887);
                    _1457_recursiveGen = _out884;
                    _1458_recOwned = _out885;
                    _1459_recErased = _out886;
                    _1460_recIdents = _out887;
                    if (!(_1458_recOwned)) {
                      _1457_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1457_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1457_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1459_recErased;
                    readIdents = _1460_recIdents;
                  }
                } else if (_source54.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1461___mcc_h794 = _source54.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1462_recursiveGen;
                    bool _1463_recOwned;
                    bool _1464_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1465_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out888;
                    bool _out889;
                    bool _out890;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out891;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out888, out _out889, out _out890, out _out891);
                    _1462_recursiveGen = _out888;
                    _1463_recOwned = _out889;
                    _1464_recErased = _out890;
                    _1465_recIdents = _out891;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1462_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1463_recOwned;
                    isErased = _1464_recErased;
                    readIdents = _1465_recIdents;
                  }
                } else if (_source54.is_Array) {
                  DAST._IType _1466___mcc_h796 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1467_recursiveGen;
                    bool _1468_recOwned;
                    bool _1469_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1470_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out892;
                    bool _out893;
                    bool _out894;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out895;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out892, out _out893, out _out894, out _out895);
                    _1467_recursiveGen = _out892;
                    _1468_recOwned = _out893;
                    _1469_recErased = _out894;
                    _1470_recIdents = _out895;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1467_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1468_recOwned;
                    isErased = _1469_recErased;
                    readIdents = _1470_recIdents;
                  }
                } else if (_source54.is_Seq) {
                  DAST._IType _1471___mcc_h798 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1472_recursiveGen;
                    bool _1473_recOwned;
                    bool _1474_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1475_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out896;
                    bool _out897;
                    bool _out898;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out899;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out896, out _out897, out _out898, out _out899);
                    _1472_recursiveGen = _out896;
                    _1473_recOwned = _out897;
                    _1474_recErased = _out898;
                    _1475_recIdents = _out899;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1472_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1473_recOwned;
                    isErased = _1474_recErased;
                    readIdents = _1475_recIdents;
                  }
                } else if (_source54.is_Set) {
                  DAST._IType _1476___mcc_h800 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1477_recursiveGen;
                    bool _1478_recOwned;
                    bool _1479_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1480_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out900;
                    bool _out901;
                    bool _out902;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out903;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out900, out _out901, out _out902, out _out903);
                    _1477_recursiveGen = _out900;
                    _1478_recOwned = _out901;
                    _1479_recErased = _out902;
                    _1480_recIdents = _out903;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1477_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1478_recOwned;
                    isErased = _1479_recErased;
                    readIdents = _1480_recIdents;
                  }
                } else if (_source54.is_Multiset) {
                  DAST._IType _1481___mcc_h802 = _source54.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1482_recursiveGen;
                    bool _1483_recOwned;
                    bool _1484_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1485_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out904;
                    bool _out905;
                    bool _out906;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out907;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out904, out _out905, out _out906, out _out907);
                    _1482_recursiveGen = _out904;
                    _1483_recOwned = _out905;
                    _1484_recErased = _out906;
                    _1485_recIdents = _out907;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1482_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1483_recOwned;
                    isErased = _1484_recErased;
                    readIdents = _1485_recIdents;
                  }
                } else if (_source54.is_Map) {
                  DAST._IType _1486___mcc_h804 = _source54.dtor_key;
                  DAST._IType _1487___mcc_h805 = _source54.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1488_recursiveGen;
                    bool _1489_recOwned;
                    bool _1490_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1491_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out908;
                    bool _out909;
                    bool _out910;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out911;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out908, out _out909, out _out910, out _out911);
                    _1488_recursiveGen = _out908;
                    _1489_recOwned = _out909;
                    _1490_recErased = _out910;
                    _1491_recIdents = _out911;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1488_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1489_recOwned;
                    isErased = _1490_recErased;
                    readIdents = _1491_recIdents;
                  }
                } else if (_source54.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1492___mcc_h808 = _source54.dtor_args;
                  DAST._IType _1493___mcc_h809 = _source54.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1494_recursiveGen;
                    bool _1495_recOwned;
                    bool _1496_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1497_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out912;
                    bool _out913;
                    bool _out914;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out915;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out912, out _out913, out _out914, out _out915);
                    _1494_recursiveGen = _out912;
                    _1495_recOwned = _out913;
                    _1496_recErased = _out914;
                    _1497_recIdents = _out915;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1494_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1495_recOwned;
                    isErased = _1496_recErased;
                    readIdents = _1497_recIdents;
                  }
                } else if (_source54.is_Primitive) {
                  DAST._IPrimitive _1498___mcc_h812 = _source54.dtor_Primitive_a0;
                  DAST._IPrimitive _source56 = _1498___mcc_h812;
                  if (_source56.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1499_recursiveGen;
                      bool _1500_recOwned;
                      bool _1501_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1502_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out916;
                      bool _out917;
                      bool _out918;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out919;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out916, out _out917, out _out918, out _out919);
                      _1499_recursiveGen = _out916;
                      _1500_recOwned = _out917;
                      _1501_recErased = _out918;
                      _1502_recIdents = _out919;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1499_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1500_recOwned;
                      isErased = _1501_recErased;
                      readIdents = _1502_recIdents;
                    }
                  } else if (_source56.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1503_recursiveGen;
                      bool _1504___v47;
                      bool _1505___v48;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1506_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out920;
                      bool _out921;
                      bool _out922;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out923;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, true, out _out920, out _out921, out _out922, out _out923);
                      _1503_recursiveGen = _out920;
                      _1504___v47 = _out921;
                      _1505___v48 = _out922;
                      _1506_recIdents = _out923;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), _1503_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1506_recIdents;
                    }
                  } else if (_source56.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1507_recursiveGen;
                      bool _1508_recOwned;
                      bool _1509_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out924;
                      bool _out925;
                      bool _out926;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out927;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out924, out _out925, out _out926, out _out927);
                      _1507_recursiveGen = _out924;
                      _1508_recOwned = _out925;
                      _1509_recErased = _out926;
                      _1510_recIdents = _out927;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1507_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1508_recOwned;
                      isErased = _1509_recErased;
                      readIdents = _1510_recIdents;
                    }
                  } else if (_source56.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1511_recursiveGen;
                      bool _1512_recOwned;
                      bool _1513_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1514_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out928;
                      bool _out929;
                      bool _out930;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out931;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out928, out _out929, out _out930, out _out931);
                      _1511_recursiveGen = _out928;
                      _1512_recOwned = _out929;
                      _1513_recErased = _out930;
                      _1514_recIdents = _out931;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1511_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1512_recOwned;
                      isErased = _1513_recErased;
                      readIdents = _1514_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1515_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out932;
                      _out932 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1515_rhsType = _out932;
                      Dafny.ISequence<Dafny.Rune> _1516_recursiveGen;
                      bool _1517___v57;
                      bool _1518___v58;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1519_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out933;
                      bool _out934;
                      bool _out935;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out936;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, true, out _out933, out _out934, out _out935, out _out936);
                      _1516_recursiveGen = _out933;
                      _1517___v57 = _out934;
                      _1518___v58 = _out935;
                      _1519_recIdents = _out936;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32 as ::dafny_runtime::NumCast>::from("), _1516_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()).unwrap()"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1519_recIdents;
                    }
                  }
                } else if (_source54.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1520___mcc_h814 = _source54.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1521_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out937;
                    _out937 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                    _1521_rhsType = _out937;
                    Dafny.ISequence<Dafny.Rune> _1522_recursiveGen;
                    bool _1523___v52;
                    bool _1524___v53;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1525_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out938;
                    bool _out939;
                    bool _out940;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out941;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, true, out _out938, out _out939, out _out940, out _out941);
                    _1522_recursiveGen = _out938;
                    _1523___v52 = _out939;
                    _1524___v53 = _out940;
                    _1525_recIdents = _out941;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1521_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), _1522_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1525_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1526___mcc_h816 = _source54.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1527_recursiveGen;
                    bool _1528_recOwned;
                    bool _1529_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1530_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out942;
                    bool _out943;
                    bool _out944;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out945;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out942, out _out943, out _out944, out _out945);
                    _1527_recursiveGen = _out942;
                    _1528_recOwned = _out943;
                    _1529_recErased = _out944;
                    _1530_recIdents = _out945;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1527_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1528_recOwned;
                    isErased = _1529_recErased;
                    readIdents = _1530_recIdents;
                  }
                }
              } else if (_source53.is_Real) {
                DAST._IType _source57 = _538___mcc_h253;
                if (_source57.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1531___mcc_h818 = _source57.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1532___mcc_h819 = _source57.dtor_typeArgs;
                  DAST._IResolvedType _1533___mcc_h820 = _source57.dtor_resolved;
                  DAST._IResolvedType _source58 = _1533___mcc_h820;
                  if (_source58.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1534___mcc_h824 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1535_recursiveGen;
                      bool _1536_recOwned;
                      bool _1537_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1538_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out946;
                      bool _out947;
                      bool _out948;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out949;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out946, out _out947, out _out948, out _out949);
                      _1535_recursiveGen = _out946;
                      _1536_recOwned = _out947;
                      _1537_recErased = _out948;
                      _1538_recIdents = _out949;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1535_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1536_recOwned;
                      isErased = _1537_recErased;
                      readIdents = _1538_recIdents;
                    }
                  } else if (_source58.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1539___mcc_h826 = _source58.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1540_recursiveGen;
                      bool _1541_recOwned;
                      bool _1542_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1543_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out950;
                      bool _out951;
                      bool _out952;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out953;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out950, out _out951, out _out952, out _out953);
                      _1540_recursiveGen = _out950;
                      _1541_recOwned = _out951;
                      _1542_recErased = _out952;
                      _1543_recIdents = _out953;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1540_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1541_recOwned;
                      isErased = _1542_recErased;
                      readIdents = _1543_recIdents;
                    }
                  } else {
                    DAST._IType _1544___mcc_h828 = _source58.dtor_Newtype_a0;
                    DAST._IType _1545_b = _1544___mcc_h828;
                    {
                      if (object.Equals(_531_fromTpe, _1545_b)) {
                        Dafny.ISequence<Dafny.Rune> _1546_recursiveGen;
                        bool _1547_recOwned;
                        bool _1548_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1549_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out954;
                        bool _out955;
                        bool _out956;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out957;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out954, out _out955, out _out956, out _out957);
                        _1546_recursiveGen = _out954;
                        _1547_recOwned = _out955;
                        _1548_recErased = _out956;
                        _1549_recIdents = _out957;
                        Dafny.ISequence<Dafny.Rune> _1550_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out958;
                        _out958 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _1550_rhsType = _out958;
                        Dafny.ISequence<Dafny.Rune> _1551_uneraseFn;
                        _1551_uneraseFn = ((_1547_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1550_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1551_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1546_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1547_recOwned;
                        isErased = false;
                        readIdents = _1549_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out959;
                        bool _out960;
                        bool _out961;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out962;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1545_b), _1545_b, _530_toTpe), selfIdent, @params, mustOwn, out _out959, out _out960, out _out961, out _out962);
                        s = _out959;
                        isOwned = _out960;
                        isErased = _out961;
                        readIdents = _out962;
                      }
                    }
                  }
                } else if (_source57.is_Nullable) {
                  DAST._IType _1552___mcc_h830 = _source57.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1553_recursiveGen;
                    bool _1554_recOwned;
                    bool _1555_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1556_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out963;
                    bool _out964;
                    bool _out965;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out966;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out963, out _out964, out _out965, out _out966);
                    _1553_recursiveGen = _out963;
                    _1554_recOwned = _out964;
                    _1555_recErased = _out965;
                    _1556_recIdents = _out966;
                    if (!(_1554_recOwned)) {
                      _1553_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1553_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1553_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1555_recErased;
                    readIdents = _1556_recIdents;
                  }
                } else if (_source57.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1557___mcc_h832 = _source57.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1558_recursiveGen;
                    bool _1559_recOwned;
                    bool _1560_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1561_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out967;
                    bool _out968;
                    bool _out969;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out970;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out967, out _out968, out _out969, out _out970);
                    _1558_recursiveGen = _out967;
                    _1559_recOwned = _out968;
                    _1560_recErased = _out969;
                    _1561_recIdents = _out970;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1558_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1559_recOwned;
                    isErased = _1560_recErased;
                    readIdents = _1561_recIdents;
                  }
                } else if (_source57.is_Array) {
                  DAST._IType _1562___mcc_h834 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1563_recursiveGen;
                    bool _1564_recOwned;
                    bool _1565_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1566_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out971;
                    bool _out972;
                    bool _out973;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out974;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out971, out _out972, out _out973, out _out974);
                    _1563_recursiveGen = _out971;
                    _1564_recOwned = _out972;
                    _1565_recErased = _out973;
                    _1566_recIdents = _out974;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1563_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1564_recOwned;
                    isErased = _1565_recErased;
                    readIdents = _1566_recIdents;
                  }
                } else if (_source57.is_Seq) {
                  DAST._IType _1567___mcc_h836 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1568_recursiveGen;
                    bool _1569_recOwned;
                    bool _1570_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1571_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out975;
                    bool _out976;
                    bool _out977;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out978;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out975, out _out976, out _out977, out _out978);
                    _1568_recursiveGen = _out975;
                    _1569_recOwned = _out976;
                    _1570_recErased = _out977;
                    _1571_recIdents = _out978;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1568_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1569_recOwned;
                    isErased = _1570_recErased;
                    readIdents = _1571_recIdents;
                  }
                } else if (_source57.is_Set) {
                  DAST._IType _1572___mcc_h838 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1573_recursiveGen;
                    bool _1574_recOwned;
                    bool _1575_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1576_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out979;
                    bool _out980;
                    bool _out981;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out982;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out979, out _out980, out _out981, out _out982);
                    _1573_recursiveGen = _out979;
                    _1574_recOwned = _out980;
                    _1575_recErased = _out981;
                    _1576_recIdents = _out982;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1573_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1574_recOwned;
                    isErased = _1575_recErased;
                    readIdents = _1576_recIdents;
                  }
                } else if (_source57.is_Multiset) {
                  DAST._IType _1577___mcc_h840 = _source57.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1578_recursiveGen;
                    bool _1579_recOwned;
                    bool _1580_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1581_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out983;
                    bool _out984;
                    bool _out985;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out986;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out983, out _out984, out _out985, out _out986);
                    _1578_recursiveGen = _out983;
                    _1579_recOwned = _out984;
                    _1580_recErased = _out985;
                    _1581_recIdents = _out986;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1578_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1579_recOwned;
                    isErased = _1580_recErased;
                    readIdents = _1581_recIdents;
                  }
                } else if (_source57.is_Map) {
                  DAST._IType _1582___mcc_h842 = _source57.dtor_key;
                  DAST._IType _1583___mcc_h843 = _source57.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1584_recursiveGen;
                    bool _1585_recOwned;
                    bool _1586_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1587_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out987;
                    bool _out988;
                    bool _out989;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out990;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out987, out _out988, out _out989, out _out990);
                    _1584_recursiveGen = _out987;
                    _1585_recOwned = _out988;
                    _1586_recErased = _out989;
                    _1587_recIdents = _out990;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1584_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1585_recOwned;
                    isErased = _1586_recErased;
                    readIdents = _1587_recIdents;
                  }
                } else if (_source57.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1588___mcc_h846 = _source57.dtor_args;
                  DAST._IType _1589___mcc_h847 = _source57.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1590_recursiveGen;
                    bool _1591_recOwned;
                    bool _1592_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1593_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out991;
                    bool _out992;
                    bool _out993;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out994;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out991, out _out992, out _out993, out _out994);
                    _1590_recursiveGen = _out991;
                    _1591_recOwned = _out992;
                    _1592_recErased = _out993;
                    _1593_recIdents = _out994;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1590_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1591_recOwned;
                    isErased = _1592_recErased;
                    readIdents = _1593_recIdents;
                  }
                } else if (_source57.is_Primitive) {
                  DAST._IPrimitive _1594___mcc_h850 = _source57.dtor_Primitive_a0;
                  DAST._IPrimitive _source59 = _1594___mcc_h850;
                  if (_source59.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1595_recursiveGen;
                      bool _1596___v49;
                      bool _1597___v50;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1598_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out995;
                      bool _out996;
                      bool _out997;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out998;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, false, out _out995, out _out996, out _out997, out _out998);
                      _1595_recursiveGen = _out995;
                      _1596___v49 = _out996;
                      _1597___v50 = _out997;
                      _1598_recIdents = _out998;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), _1595_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1598_recIdents;
                    }
                  } else if (_source59.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1599_recursiveGen;
                      bool _1600_recOwned;
                      bool _1601_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1602_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out999;
                      bool _out1000;
                      bool _out1001;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1002;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out999, out _out1000, out _out1001, out _out1002);
                      _1599_recursiveGen = _out999;
                      _1600_recOwned = _out1000;
                      _1601_recErased = _out1001;
                      _1602_recIdents = _out1002;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1599_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1600_recOwned;
                      isErased = _1601_recErased;
                      readIdents = _1602_recIdents;
                    }
                  } else if (_source59.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1603_recursiveGen;
                      bool _1604_recOwned;
                      bool _1605_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1606_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1003;
                      bool _out1004;
                      bool _out1005;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1006;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1003, out _out1004, out _out1005, out _out1006);
                      _1603_recursiveGen = _out1003;
                      _1604_recOwned = _out1004;
                      _1605_recErased = _out1005;
                      _1606_recIdents = _out1006;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1603_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1604_recOwned;
                      isErased = _1605_recErased;
                      readIdents = _1606_recIdents;
                    }
                  } else if (_source59.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1607_recursiveGen;
                      bool _1608_recOwned;
                      bool _1609_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1610_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1007;
                      bool _out1008;
                      bool _out1009;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1010;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1007, out _out1008, out _out1009, out _out1010);
                      _1607_recursiveGen = _out1007;
                      _1608_recOwned = _out1008;
                      _1609_recErased = _out1009;
                      _1610_recIdents = _out1010;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1607_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1608_recOwned;
                      isErased = _1609_recErased;
                      readIdents = _1610_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1611_recursiveGen;
                      bool _1612_recOwned;
                      bool _1613_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1614_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1011;
                      bool _out1012;
                      bool _out1013;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1014;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1011, out _out1012, out _out1013, out _out1014);
                      _1611_recursiveGen = _out1011;
                      _1612_recOwned = _out1012;
                      _1613_recErased = _out1013;
                      _1614_recIdents = _out1014;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1611_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1612_recOwned;
                      isErased = _1613_recErased;
                      readIdents = _1614_recIdents;
                    }
                  }
                } else if (_source57.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1615___mcc_h852 = _source57.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1616_recursiveGen;
                    bool _1617_recOwned;
                    bool _1618_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1619_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1015;
                    bool _out1016;
                    bool _out1017;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1018;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1015, out _out1016, out _out1017, out _out1018);
                    _1616_recursiveGen = _out1015;
                    _1617_recOwned = _out1016;
                    _1618_recErased = _out1017;
                    _1619_recIdents = _out1018;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1616_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1617_recOwned;
                    isErased = _1618_recErased;
                    readIdents = _1619_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1620___mcc_h854 = _source57.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1621_recursiveGen;
                    bool _1622_recOwned;
                    bool _1623_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1624_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1019;
                    bool _out1020;
                    bool _out1021;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1022;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1019, out _out1020, out _out1021, out _out1022);
                    _1621_recursiveGen = _out1019;
                    _1622_recOwned = _out1020;
                    _1623_recErased = _out1021;
                    _1624_recIdents = _out1022;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1621_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1622_recOwned;
                    isErased = _1623_recErased;
                    readIdents = _1624_recIdents;
                  }
                }
              } else if (_source53.is_String) {
                DAST._IType _source60 = _538___mcc_h253;
                if (_source60.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1625___mcc_h856 = _source60.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1626___mcc_h857 = _source60.dtor_typeArgs;
                  DAST._IResolvedType _1627___mcc_h858 = _source60.dtor_resolved;
                  DAST._IResolvedType _source61 = _1627___mcc_h858;
                  if (_source61.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1628___mcc_h862 = _source61.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1629_recursiveGen;
                      bool _1630_recOwned;
                      bool _1631_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1632_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1023;
                      bool _out1024;
                      bool _out1025;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1026;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1023, out _out1024, out _out1025, out _out1026);
                      _1629_recursiveGen = _out1023;
                      _1630_recOwned = _out1024;
                      _1631_recErased = _out1025;
                      _1632_recIdents = _out1026;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1629_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1630_recOwned;
                      isErased = _1631_recErased;
                      readIdents = _1632_recIdents;
                    }
                  } else if (_source61.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1633___mcc_h864 = _source61.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1634_recursiveGen;
                      bool _1635_recOwned;
                      bool _1636_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1637_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1027;
                      bool _out1028;
                      bool _out1029;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1030;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1027, out _out1028, out _out1029, out _out1030);
                      _1634_recursiveGen = _out1027;
                      _1635_recOwned = _out1028;
                      _1636_recErased = _out1029;
                      _1637_recIdents = _out1030;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1634_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1635_recOwned;
                      isErased = _1636_recErased;
                      readIdents = _1637_recIdents;
                    }
                  } else {
                    DAST._IType _1638___mcc_h866 = _source61.dtor_Newtype_a0;
                    DAST._IType _1639_b = _1638___mcc_h866;
                    {
                      if (object.Equals(_531_fromTpe, _1639_b)) {
                        Dafny.ISequence<Dafny.Rune> _1640_recursiveGen;
                        bool _1641_recOwned;
                        bool _1642_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1643_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1031;
                        bool _out1032;
                        bool _out1033;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1034;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1031, out _out1032, out _out1033, out _out1034);
                        _1640_recursiveGen = _out1031;
                        _1641_recOwned = _out1032;
                        _1642_recErased = _out1033;
                        _1643_recIdents = _out1034;
                        Dafny.ISequence<Dafny.Rune> _1644_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1035;
                        _out1035 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _1644_rhsType = _out1035;
                        Dafny.ISequence<Dafny.Rune> _1645_uneraseFn;
                        _1645_uneraseFn = ((_1641_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1644_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1645_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1640_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1641_recOwned;
                        isErased = false;
                        readIdents = _1643_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1036;
                        bool _out1037;
                        bool _out1038;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1039;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1639_b), _1639_b, _530_toTpe), selfIdent, @params, mustOwn, out _out1036, out _out1037, out _out1038, out _out1039);
                        s = _out1036;
                        isOwned = _out1037;
                        isErased = _out1038;
                        readIdents = _out1039;
                      }
                    }
                  }
                } else if (_source60.is_Nullable) {
                  DAST._IType _1646___mcc_h868 = _source60.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1647_recursiveGen;
                    bool _1648_recOwned;
                    bool _1649_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1650_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1040;
                    bool _out1041;
                    bool _out1042;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1043;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1040, out _out1041, out _out1042, out _out1043);
                    _1647_recursiveGen = _out1040;
                    _1648_recOwned = _out1041;
                    _1649_recErased = _out1042;
                    _1650_recIdents = _out1043;
                    if (!(_1648_recOwned)) {
                      _1647_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1647_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1647_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1649_recErased;
                    readIdents = _1650_recIdents;
                  }
                } else if (_source60.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1651___mcc_h870 = _source60.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1652_recursiveGen;
                    bool _1653_recOwned;
                    bool _1654_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1655_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1044;
                    bool _out1045;
                    bool _out1046;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1047;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1044, out _out1045, out _out1046, out _out1047);
                    _1652_recursiveGen = _out1044;
                    _1653_recOwned = _out1045;
                    _1654_recErased = _out1046;
                    _1655_recIdents = _out1047;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1652_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1653_recOwned;
                    isErased = _1654_recErased;
                    readIdents = _1655_recIdents;
                  }
                } else if (_source60.is_Array) {
                  DAST._IType _1656___mcc_h872 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1657_recursiveGen;
                    bool _1658_recOwned;
                    bool _1659_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1660_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1048;
                    bool _out1049;
                    bool _out1050;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1051;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1048, out _out1049, out _out1050, out _out1051);
                    _1657_recursiveGen = _out1048;
                    _1658_recOwned = _out1049;
                    _1659_recErased = _out1050;
                    _1660_recIdents = _out1051;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1657_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1658_recOwned;
                    isErased = _1659_recErased;
                    readIdents = _1660_recIdents;
                  }
                } else if (_source60.is_Seq) {
                  DAST._IType _1661___mcc_h874 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1662_recursiveGen;
                    bool _1663_recOwned;
                    bool _1664_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1665_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1052;
                    bool _out1053;
                    bool _out1054;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1055;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1052, out _out1053, out _out1054, out _out1055);
                    _1662_recursiveGen = _out1052;
                    _1663_recOwned = _out1053;
                    _1664_recErased = _out1054;
                    _1665_recIdents = _out1055;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1662_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1663_recOwned;
                    isErased = _1664_recErased;
                    readIdents = _1665_recIdents;
                  }
                } else if (_source60.is_Set) {
                  DAST._IType _1666___mcc_h876 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1667_recursiveGen;
                    bool _1668_recOwned;
                    bool _1669_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1670_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1056;
                    bool _out1057;
                    bool _out1058;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1059;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1056, out _out1057, out _out1058, out _out1059);
                    _1667_recursiveGen = _out1056;
                    _1668_recOwned = _out1057;
                    _1669_recErased = _out1058;
                    _1670_recIdents = _out1059;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1667_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1668_recOwned;
                    isErased = _1669_recErased;
                    readIdents = _1670_recIdents;
                  }
                } else if (_source60.is_Multiset) {
                  DAST._IType _1671___mcc_h878 = _source60.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1672_recursiveGen;
                    bool _1673_recOwned;
                    bool _1674_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1675_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1060;
                    bool _out1061;
                    bool _out1062;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1063;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1060, out _out1061, out _out1062, out _out1063);
                    _1672_recursiveGen = _out1060;
                    _1673_recOwned = _out1061;
                    _1674_recErased = _out1062;
                    _1675_recIdents = _out1063;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1672_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1673_recOwned;
                    isErased = _1674_recErased;
                    readIdents = _1675_recIdents;
                  }
                } else if (_source60.is_Map) {
                  DAST._IType _1676___mcc_h880 = _source60.dtor_key;
                  DAST._IType _1677___mcc_h881 = _source60.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1678_recursiveGen;
                    bool _1679_recOwned;
                    bool _1680_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1681_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1064;
                    bool _out1065;
                    bool _out1066;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1067;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1064, out _out1065, out _out1066, out _out1067);
                    _1678_recursiveGen = _out1064;
                    _1679_recOwned = _out1065;
                    _1680_recErased = _out1066;
                    _1681_recIdents = _out1067;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1678_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1679_recOwned;
                    isErased = _1680_recErased;
                    readIdents = _1681_recIdents;
                  }
                } else if (_source60.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1682___mcc_h884 = _source60.dtor_args;
                  DAST._IType _1683___mcc_h885 = _source60.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1684_recursiveGen;
                    bool _1685_recOwned;
                    bool _1686_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1687_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1068;
                    bool _out1069;
                    bool _out1070;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1071;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1068, out _out1069, out _out1070, out _out1071);
                    _1684_recursiveGen = _out1068;
                    _1685_recOwned = _out1069;
                    _1686_recErased = _out1070;
                    _1687_recIdents = _out1071;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1684_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1685_recOwned;
                    isErased = _1686_recErased;
                    readIdents = _1687_recIdents;
                  }
                } else if (_source60.is_Primitive) {
                  DAST._IPrimitive _1688___mcc_h888 = _source60.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1689_recursiveGen;
                    bool _1690_recOwned;
                    bool _1691_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1692_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1072;
                    bool _out1073;
                    bool _out1074;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1075;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1072, out _out1073, out _out1074, out _out1075);
                    _1689_recursiveGen = _out1072;
                    _1690_recOwned = _out1073;
                    _1691_recErased = _out1074;
                    _1692_recIdents = _out1075;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1689_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1690_recOwned;
                    isErased = _1691_recErased;
                    readIdents = _1692_recIdents;
                  }
                } else if (_source60.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1693___mcc_h890 = _source60.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1694_recursiveGen;
                    bool _1695_recOwned;
                    bool _1696_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1697_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1076;
                    bool _out1077;
                    bool _out1078;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1079;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1076, out _out1077, out _out1078, out _out1079);
                    _1694_recursiveGen = _out1076;
                    _1695_recOwned = _out1077;
                    _1696_recErased = _out1078;
                    _1697_recIdents = _out1079;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1694_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1695_recOwned;
                    isErased = _1696_recErased;
                    readIdents = _1697_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1698___mcc_h892 = _source60.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1699_recursiveGen;
                    bool _1700_recOwned;
                    bool _1701_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1702_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1080;
                    bool _out1081;
                    bool _out1082;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1083;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1080, out _out1081, out _out1082, out _out1083);
                    _1699_recursiveGen = _out1080;
                    _1700_recOwned = _out1081;
                    _1701_recErased = _out1082;
                    _1702_recIdents = _out1083;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1699_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1700_recOwned;
                    isErased = _1701_recErased;
                    readIdents = _1702_recIdents;
                  }
                }
              } else if (_source53.is_Bool) {
                DAST._IType _source62 = _538___mcc_h253;
                if (_source62.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1703___mcc_h894 = _source62.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1704___mcc_h895 = _source62.dtor_typeArgs;
                  DAST._IResolvedType _1705___mcc_h896 = _source62.dtor_resolved;
                  DAST._IResolvedType _source63 = _1705___mcc_h896;
                  if (_source63.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1706___mcc_h900 = _source63.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1707_recursiveGen;
                      bool _1708_recOwned;
                      bool _1709_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1710_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1084;
                      bool _out1085;
                      bool _out1086;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1087;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1084, out _out1085, out _out1086, out _out1087);
                      _1707_recursiveGen = _out1084;
                      _1708_recOwned = _out1085;
                      _1709_recErased = _out1086;
                      _1710_recIdents = _out1087;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1707_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1708_recOwned;
                      isErased = _1709_recErased;
                      readIdents = _1710_recIdents;
                    }
                  } else if (_source63.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1711___mcc_h902 = _source63.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1712_recursiveGen;
                      bool _1713_recOwned;
                      bool _1714_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1715_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1088;
                      bool _out1089;
                      bool _out1090;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1091;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1088, out _out1089, out _out1090, out _out1091);
                      _1712_recursiveGen = _out1088;
                      _1713_recOwned = _out1089;
                      _1714_recErased = _out1090;
                      _1715_recIdents = _out1091;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1712_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1713_recOwned;
                      isErased = _1714_recErased;
                      readIdents = _1715_recIdents;
                    }
                  } else {
                    DAST._IType _1716___mcc_h904 = _source63.dtor_Newtype_a0;
                    DAST._IType _1717_b = _1716___mcc_h904;
                    {
                      if (object.Equals(_531_fromTpe, _1717_b)) {
                        Dafny.ISequence<Dafny.Rune> _1718_recursiveGen;
                        bool _1719_recOwned;
                        bool _1720_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1092;
                        bool _out1093;
                        bool _out1094;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1095;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1092, out _out1093, out _out1094, out _out1095);
                        _1718_recursiveGen = _out1092;
                        _1719_recOwned = _out1093;
                        _1720_recErased = _out1094;
                        _1721_recIdents = _out1095;
                        Dafny.ISequence<Dafny.Rune> _1722_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1096;
                        _out1096 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _1722_rhsType = _out1096;
                        Dafny.ISequence<Dafny.Rune> _1723_uneraseFn;
                        _1723_uneraseFn = ((_1719_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1722_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1723_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1718_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1719_recOwned;
                        isErased = false;
                        readIdents = _1721_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1097;
                        bool _out1098;
                        bool _out1099;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1100;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1717_b), _1717_b, _530_toTpe), selfIdent, @params, mustOwn, out _out1097, out _out1098, out _out1099, out _out1100);
                        s = _out1097;
                        isOwned = _out1098;
                        isErased = _out1099;
                        readIdents = _out1100;
                      }
                    }
                  }
                } else if (_source62.is_Nullable) {
                  DAST._IType _1724___mcc_h906 = _source62.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1725_recursiveGen;
                    bool _1726_recOwned;
                    bool _1727_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1728_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1101;
                    bool _out1102;
                    bool _out1103;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1104;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1101, out _out1102, out _out1103, out _out1104);
                    _1725_recursiveGen = _out1101;
                    _1726_recOwned = _out1102;
                    _1727_recErased = _out1103;
                    _1728_recIdents = _out1104;
                    if (!(_1726_recOwned)) {
                      _1725_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1725_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1725_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1727_recErased;
                    readIdents = _1728_recIdents;
                  }
                } else if (_source62.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1729___mcc_h908 = _source62.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1730_recursiveGen;
                    bool _1731_recOwned;
                    bool _1732_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1733_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1105;
                    bool _out1106;
                    bool _out1107;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1108;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1105, out _out1106, out _out1107, out _out1108);
                    _1730_recursiveGen = _out1105;
                    _1731_recOwned = _out1106;
                    _1732_recErased = _out1107;
                    _1733_recIdents = _out1108;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1730_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1731_recOwned;
                    isErased = _1732_recErased;
                    readIdents = _1733_recIdents;
                  }
                } else if (_source62.is_Array) {
                  DAST._IType _1734___mcc_h910 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1735_recursiveGen;
                    bool _1736_recOwned;
                    bool _1737_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1738_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1109;
                    bool _out1110;
                    bool _out1111;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1112;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1109, out _out1110, out _out1111, out _out1112);
                    _1735_recursiveGen = _out1109;
                    _1736_recOwned = _out1110;
                    _1737_recErased = _out1111;
                    _1738_recIdents = _out1112;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1735_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1736_recOwned;
                    isErased = _1737_recErased;
                    readIdents = _1738_recIdents;
                  }
                } else if (_source62.is_Seq) {
                  DAST._IType _1739___mcc_h912 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1740_recursiveGen;
                    bool _1741_recOwned;
                    bool _1742_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1743_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1113;
                    bool _out1114;
                    bool _out1115;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1116;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1113, out _out1114, out _out1115, out _out1116);
                    _1740_recursiveGen = _out1113;
                    _1741_recOwned = _out1114;
                    _1742_recErased = _out1115;
                    _1743_recIdents = _out1116;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1740_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1741_recOwned;
                    isErased = _1742_recErased;
                    readIdents = _1743_recIdents;
                  }
                } else if (_source62.is_Set) {
                  DAST._IType _1744___mcc_h914 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1745_recursiveGen;
                    bool _1746_recOwned;
                    bool _1747_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1748_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1117;
                    bool _out1118;
                    bool _out1119;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1120;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1117, out _out1118, out _out1119, out _out1120);
                    _1745_recursiveGen = _out1117;
                    _1746_recOwned = _out1118;
                    _1747_recErased = _out1119;
                    _1748_recIdents = _out1120;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1745_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1746_recOwned;
                    isErased = _1747_recErased;
                    readIdents = _1748_recIdents;
                  }
                } else if (_source62.is_Multiset) {
                  DAST._IType _1749___mcc_h916 = _source62.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1750_recursiveGen;
                    bool _1751_recOwned;
                    bool _1752_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1753_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1121;
                    bool _out1122;
                    bool _out1123;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1124;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1121, out _out1122, out _out1123, out _out1124);
                    _1750_recursiveGen = _out1121;
                    _1751_recOwned = _out1122;
                    _1752_recErased = _out1123;
                    _1753_recIdents = _out1124;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1750_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1751_recOwned;
                    isErased = _1752_recErased;
                    readIdents = _1753_recIdents;
                  }
                } else if (_source62.is_Map) {
                  DAST._IType _1754___mcc_h918 = _source62.dtor_key;
                  DAST._IType _1755___mcc_h919 = _source62.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1756_recursiveGen;
                    bool _1757_recOwned;
                    bool _1758_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1759_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1125;
                    bool _out1126;
                    bool _out1127;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1128;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1125, out _out1126, out _out1127, out _out1128);
                    _1756_recursiveGen = _out1125;
                    _1757_recOwned = _out1126;
                    _1758_recErased = _out1127;
                    _1759_recIdents = _out1128;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1756_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1757_recOwned;
                    isErased = _1758_recErased;
                    readIdents = _1759_recIdents;
                  }
                } else if (_source62.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1760___mcc_h922 = _source62.dtor_args;
                  DAST._IType _1761___mcc_h923 = _source62.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1762_recursiveGen;
                    bool _1763_recOwned;
                    bool _1764_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1765_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1129;
                    bool _out1130;
                    bool _out1131;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1132;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1129, out _out1130, out _out1131, out _out1132);
                    _1762_recursiveGen = _out1129;
                    _1763_recOwned = _out1130;
                    _1764_recErased = _out1131;
                    _1765_recIdents = _out1132;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1762_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1763_recOwned;
                    isErased = _1764_recErased;
                    readIdents = _1765_recIdents;
                  }
                } else if (_source62.is_Primitive) {
                  DAST._IPrimitive _1766___mcc_h926 = _source62.dtor_Primitive_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1767_recursiveGen;
                    bool _1768_recOwned;
                    bool _1769_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1770_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1133;
                    bool _out1134;
                    bool _out1135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1136;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1133, out _out1134, out _out1135, out _out1136);
                    _1767_recursiveGen = _out1133;
                    _1768_recOwned = _out1134;
                    _1769_recErased = _out1135;
                    _1770_recIdents = _out1136;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1767_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1768_recOwned;
                    isErased = _1769_recErased;
                    readIdents = _1770_recIdents;
                  }
                } else if (_source62.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1771___mcc_h928 = _source62.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1772_recursiveGen;
                    bool _1773_recOwned;
                    bool _1774_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1775_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1137;
                    bool _out1138;
                    bool _out1139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1140;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1137, out _out1138, out _out1139, out _out1140);
                    _1772_recursiveGen = _out1137;
                    _1773_recOwned = _out1138;
                    _1774_recErased = _out1139;
                    _1775_recIdents = _out1140;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1772_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1773_recOwned;
                    isErased = _1774_recErased;
                    readIdents = _1775_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1776___mcc_h930 = _source62.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1777_recursiveGen;
                    bool _1778_recOwned;
                    bool _1779_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1780_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1141;
                    bool _out1142;
                    bool _out1143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1144;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1141, out _out1142, out _out1143, out _out1144);
                    _1777_recursiveGen = _out1141;
                    _1778_recOwned = _out1142;
                    _1779_recErased = _out1143;
                    _1780_recIdents = _out1144;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1777_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1778_recOwned;
                    isErased = _1779_recErased;
                    readIdents = _1780_recIdents;
                  }
                }
              } else {
                DAST._IType _source64 = _538___mcc_h253;
                if (_source64.is_Path) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1781___mcc_h932 = _source64.dtor_Path_a0;
                  Dafny.ISequence<DAST._IType> _1782___mcc_h933 = _source64.dtor_typeArgs;
                  DAST._IResolvedType _1783___mcc_h934 = _source64.dtor_resolved;
                  DAST._IResolvedType _source65 = _1783___mcc_h934;
                  if (_source65.is_Datatype) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1784___mcc_h938 = _source65.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1785_recursiveGen;
                      bool _1786_recOwned;
                      bool _1787_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1145;
                      bool _out1146;
                      bool _out1147;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1148;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1145, out _out1146, out _out1147, out _out1148);
                      _1785_recursiveGen = _out1145;
                      _1786_recOwned = _out1146;
                      _1787_recErased = _out1147;
                      _1788_recIdents = _out1148;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1785_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1786_recOwned;
                      isErased = _1787_recErased;
                      readIdents = _1788_recIdents;
                    }
                  } else if (_source65.is_Trait) {
                    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1789___mcc_h940 = _source65.dtor_path;
                    {
                      Dafny.ISequence<Dafny.Rune> _1790_recursiveGen;
                      bool _1791_recOwned;
                      bool _1792_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1149;
                      bool _out1150;
                      bool _out1151;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1152;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1149, out _out1150, out _out1151, out _out1152);
                      _1790_recursiveGen = _out1149;
                      _1791_recOwned = _out1150;
                      _1792_recErased = _out1151;
                      _1793_recIdents = _out1152;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1790_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1791_recOwned;
                      isErased = _1792_recErased;
                      readIdents = _1793_recIdents;
                    }
                  } else {
                    DAST._IType _1794___mcc_h942 = _source65.dtor_Newtype_a0;
                    DAST._IType _1795_b = _1794___mcc_h942;
                    {
                      if (object.Equals(_531_fromTpe, _1795_b)) {
                        Dafny.ISequence<Dafny.Rune> _1796_recursiveGen;
                        bool _1797_recOwned;
                        bool _1798_recErased;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1799_recIdents;
                        Dafny.ISequence<Dafny.Rune> _out1153;
                        bool _out1154;
                        bool _out1155;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1156;
                        DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1153, out _out1154, out _out1155, out _out1156);
                        _1796_recursiveGen = _out1153;
                        _1797_recOwned = _out1154;
                        _1798_recErased = _out1155;
                        _1799_recIdents = _out1156;
                        Dafny.ISequence<Dafny.Rune> _1800_rhsType;
                        Dafny.ISequence<Dafny.Rune> _out1157;
                        _out1157 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                        _1800_rhsType = _out1157;
                        Dafny.ISequence<Dafny.Rune> _1801_uneraseFn;
                        _1801_uneraseFn = ((_1797_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1800_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1801_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1796_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                        isOwned = _1797_recOwned;
                        isErased = false;
                        readIdents = _1799_recIdents;
                      } else {
                        Dafny.ISequence<Dafny.Rune> _out1158;
                        bool _out1159;
                        bool _out1160;
                        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1161;
                        DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1795_b), _1795_b, _530_toTpe), selfIdent, @params, mustOwn, out _out1158, out _out1159, out _out1160, out _out1161);
                        s = _out1158;
                        isOwned = _out1159;
                        isErased = _out1160;
                        readIdents = _out1161;
                      }
                    }
                  }
                } else if (_source64.is_Nullable) {
                  DAST._IType _1802___mcc_h944 = _source64.dtor_Nullable_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1803_recursiveGen;
                    bool _1804_recOwned;
                    bool _1805_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1806_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1162;
                    bool _out1163;
                    bool _out1164;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1165;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1162, out _out1163, out _out1164, out _out1165);
                    _1803_recursiveGen = _out1162;
                    _1804_recOwned = _out1163;
                    _1805_recErased = _out1164;
                    _1806_recIdents = _out1165;
                    if (!(_1804_recOwned)) {
                      _1803_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1803_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                    }
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1803_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = _1805_recErased;
                    readIdents = _1806_recIdents;
                  }
                } else if (_source64.is_Tuple) {
                  Dafny.ISequence<DAST._IType> _1807___mcc_h946 = _source64.dtor_Tuple_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1808_recursiveGen;
                    bool _1809_recOwned;
                    bool _1810_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1811_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1166;
                    bool _out1167;
                    bool _out1168;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1169;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1166, out _out1167, out _out1168, out _out1169);
                    _1808_recursiveGen = _out1166;
                    _1809_recOwned = _out1167;
                    _1810_recErased = _out1168;
                    _1811_recIdents = _out1169;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1808_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1809_recOwned;
                    isErased = _1810_recErased;
                    readIdents = _1811_recIdents;
                  }
                } else if (_source64.is_Array) {
                  DAST._IType _1812___mcc_h948 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1813_recursiveGen;
                    bool _1814_recOwned;
                    bool _1815_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1816_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1170;
                    bool _out1171;
                    bool _out1172;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1173;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1170, out _out1171, out _out1172, out _out1173);
                    _1813_recursiveGen = _out1170;
                    _1814_recOwned = _out1171;
                    _1815_recErased = _out1172;
                    _1816_recIdents = _out1173;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1813_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1814_recOwned;
                    isErased = _1815_recErased;
                    readIdents = _1816_recIdents;
                  }
                } else if (_source64.is_Seq) {
                  DAST._IType _1817___mcc_h950 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1818_recursiveGen;
                    bool _1819_recOwned;
                    bool _1820_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1821_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1174;
                    bool _out1175;
                    bool _out1176;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1177;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1174, out _out1175, out _out1176, out _out1177);
                    _1818_recursiveGen = _out1174;
                    _1819_recOwned = _out1175;
                    _1820_recErased = _out1176;
                    _1821_recIdents = _out1177;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1818_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1819_recOwned;
                    isErased = _1820_recErased;
                    readIdents = _1821_recIdents;
                  }
                } else if (_source64.is_Set) {
                  DAST._IType _1822___mcc_h952 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1823_recursiveGen;
                    bool _1824_recOwned;
                    bool _1825_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1178;
                    bool _out1179;
                    bool _out1180;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1181;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1178, out _out1179, out _out1180, out _out1181);
                    _1823_recursiveGen = _out1178;
                    _1824_recOwned = _out1179;
                    _1825_recErased = _out1180;
                    _1826_recIdents = _out1181;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1823_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1824_recOwned;
                    isErased = _1825_recErased;
                    readIdents = _1826_recIdents;
                  }
                } else if (_source64.is_Multiset) {
                  DAST._IType _1827___mcc_h954 = _source64.dtor_element;
                  {
                    Dafny.ISequence<Dafny.Rune> _1828_recursiveGen;
                    bool _1829_recOwned;
                    bool _1830_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1831_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1182;
                    bool _out1183;
                    bool _out1184;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1185;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1182, out _out1183, out _out1184, out _out1185);
                    _1828_recursiveGen = _out1182;
                    _1829_recOwned = _out1183;
                    _1830_recErased = _out1184;
                    _1831_recIdents = _out1185;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1828_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1829_recOwned;
                    isErased = _1830_recErased;
                    readIdents = _1831_recIdents;
                  }
                } else if (_source64.is_Map) {
                  DAST._IType _1832___mcc_h956 = _source64.dtor_key;
                  DAST._IType _1833___mcc_h957 = _source64.dtor_value;
                  {
                    Dafny.ISequence<Dafny.Rune> _1834_recursiveGen;
                    bool _1835_recOwned;
                    bool _1836_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1837_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1186;
                    bool _out1187;
                    bool _out1188;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1189;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1186, out _out1187, out _out1188, out _out1189);
                    _1834_recursiveGen = _out1186;
                    _1835_recOwned = _out1187;
                    _1836_recErased = _out1188;
                    _1837_recIdents = _out1189;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1834_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1835_recOwned;
                    isErased = _1836_recErased;
                    readIdents = _1837_recIdents;
                  }
                } else if (_source64.is_Arrow) {
                  Dafny.ISequence<DAST._IType> _1838___mcc_h960 = _source64.dtor_args;
                  DAST._IType _1839___mcc_h961 = _source64.dtor_result;
                  {
                    Dafny.ISequence<Dafny.Rune> _1840_recursiveGen;
                    bool _1841_recOwned;
                    bool _1842_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1843_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1190;
                    bool _out1191;
                    bool _out1192;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1193;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1190, out _out1191, out _out1192, out _out1193);
                    _1840_recursiveGen = _out1190;
                    _1841_recOwned = _out1191;
                    _1842_recErased = _out1192;
                    _1843_recIdents = _out1193;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1840_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1841_recOwned;
                    isErased = _1842_recErased;
                    readIdents = _1843_recIdents;
                  }
                } else if (_source64.is_Primitive) {
                  DAST._IPrimitive _1844___mcc_h964 = _source64.dtor_Primitive_a0;
                  DAST._IPrimitive _source66 = _1844___mcc_h964;
                  if (_source66.is_Int) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1845_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1194;
                      _out1194 = DCOMP.COMP.GenType(_531_fromTpe, true, false);
                      _1845_rhsType = _out1194;
                      Dafny.ISequence<Dafny.Rune> _1846_recursiveGen;
                      bool _1847___v59;
                      bool _1848___v60;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1849_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1195;
                      bool _out1196;
                      bool _out1197;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1198;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, true, out _out1195, out _out1196, out _out1197, out _out1198);
                      _1846_recursiveGen = _out1195;
                      _1847___v59 = _out1196;
                      _1848___v60 = _out1197;
                      _1849_recIdents = _out1198;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1846_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as u32)"));
                      isOwned = true;
                      isErased = true;
                      readIdents = _1849_recIdents;
                    }
                  } else if (_source66.is_Real) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1850_recursiveGen;
                      bool _1851_recOwned;
                      bool _1852_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1853_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1199;
                      bool _out1200;
                      bool _out1201;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1202;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1199, out _out1200, out _out1201, out _out1202);
                      _1850_recursiveGen = _out1199;
                      _1851_recOwned = _out1200;
                      _1852_recErased = _out1201;
                      _1853_recIdents = _out1202;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1850_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1851_recOwned;
                      isErased = _1852_recErased;
                      readIdents = _1853_recIdents;
                    }
                  } else if (_source66.is_String) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1854_recursiveGen;
                      bool _1855_recOwned;
                      bool _1856_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1857_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1203;
                      bool _out1204;
                      bool _out1205;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1206;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1203, out _out1204, out _out1205, out _out1206);
                      _1854_recursiveGen = _out1203;
                      _1855_recOwned = _out1204;
                      _1856_recErased = _out1205;
                      _1857_recIdents = _out1206;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1854_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1855_recOwned;
                      isErased = _1856_recErased;
                      readIdents = _1857_recIdents;
                    }
                  } else if (_source66.is_Bool) {
                    {
                      Dafny.ISequence<Dafny.Rune> _1858_recursiveGen;
                      bool _1859_recOwned;
                      bool _1860_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1207;
                      bool _out1208;
                      bool _out1209;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1210;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1207, out _out1208, out _out1209, out _out1210);
                      _1858_recursiveGen = _out1207;
                      _1859_recOwned = _out1208;
                      _1860_recErased = _out1209;
                      _1861_recIdents = _out1210;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1858_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1859_recOwned;
                      isErased = _1860_recErased;
                      readIdents = _1861_recIdents;
                    }
                  } else {
                    {
                      Dafny.ISequence<Dafny.Rune> _1862_recursiveGen;
                      bool _1863_recOwned;
                      bool _1864_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1211;
                      bool _out1212;
                      bool _out1213;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1214;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1211, out _out1212, out _out1213, out _out1214);
                      _1862_recursiveGen = _out1211;
                      _1863_recOwned = _out1212;
                      _1864_recErased = _out1213;
                      _1865_recIdents = _out1214;
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1862_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                      isOwned = _1863_recOwned;
                      isErased = _1864_recErased;
                      readIdents = _1865_recIdents;
                    }
                  }
                } else if (_source64.is_Passthrough) {
                  Dafny.ISequence<Dafny.Rune> _1866___mcc_h966 = _source64.dtor_Passthrough_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1867_recursiveGen;
                    bool _1868_recOwned;
                    bool _1869_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1870_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1215;
                    bool _out1216;
                    bool _out1217;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1218;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1215, out _out1216, out _out1217, out _out1218);
                    _1867_recursiveGen = _out1215;
                    _1868_recOwned = _out1216;
                    _1869_recErased = _out1217;
                    _1870_recIdents = _out1218;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1867_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1868_recOwned;
                    isErased = _1869_recErased;
                    readIdents = _1870_recIdents;
                  }
                } else {
                  Dafny.ISequence<Dafny.Rune> _1871___mcc_h968 = _source64.dtor_TypeArg_a0;
                  {
                    Dafny.ISequence<Dafny.Rune> _1872_recursiveGen;
                    bool _1873_recOwned;
                    bool _1874_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1875_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1219;
                    bool _out1220;
                    bool _out1221;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1222;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1219, out _out1220, out _out1221, out _out1222);
                    _1872_recursiveGen = _out1219;
                    _1873_recOwned = _out1220;
                    _1874_recErased = _out1221;
                    _1875_recIdents = _out1222;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1872_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1873_recOwned;
                    isErased = _1874_recErased;
                    readIdents = _1875_recIdents;
                  }
                }
              }
            } else if (_source29.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1876___mcc_h970 = _source29.dtor_Passthrough_a0;
              DAST._IType _source67 = _538___mcc_h253;
              if (_source67.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1877___mcc_h974 = _source67.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1878___mcc_h975 = _source67.dtor_typeArgs;
                DAST._IResolvedType _1879___mcc_h976 = _source67.dtor_resolved;
                DAST._IResolvedType _source68 = _1879___mcc_h976;
                if (_source68.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1880___mcc_h980 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1881_recursiveGen;
                    bool _1882_recOwned;
                    bool _1883_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1223;
                    bool _out1224;
                    bool _out1225;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1226;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1223, out _out1224, out _out1225, out _out1226);
                    _1881_recursiveGen = _out1223;
                    _1882_recOwned = _out1224;
                    _1883_recErased = _out1225;
                    _1884_recIdents = _out1226;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1881_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1882_recOwned;
                    isErased = _1883_recErased;
                    readIdents = _1884_recIdents;
                  }
                } else if (_source68.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1885___mcc_h982 = _source68.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1886_recursiveGen;
                    bool _1887_recOwned;
                    bool _1888_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1889_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1227;
                    bool _out1228;
                    bool _out1229;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1230;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1227, out _out1228, out _out1229, out _out1230);
                    _1886_recursiveGen = _out1227;
                    _1887_recOwned = _out1228;
                    _1888_recErased = _out1229;
                    _1889_recIdents = _out1230;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1886_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1887_recOwned;
                    isErased = _1888_recErased;
                    readIdents = _1889_recIdents;
                  }
                } else {
                  DAST._IType _1890___mcc_h984 = _source68.dtor_Newtype_a0;
                  DAST._IType _1891_b = _1890___mcc_h984;
                  {
                    if (object.Equals(_531_fromTpe, _1891_b)) {
                      Dafny.ISequence<Dafny.Rune> _1892_recursiveGen;
                      bool _1893_recOwned;
                      bool _1894_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1895_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1231;
                      bool _out1232;
                      bool _out1233;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1234;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1231, out _out1232, out _out1233, out _out1234);
                      _1892_recursiveGen = _out1231;
                      _1893_recOwned = _out1232;
                      _1894_recErased = _out1233;
                      _1895_recIdents = _out1234;
                      Dafny.ISequence<Dafny.Rune> _1896_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1235;
                      _out1235 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1896_rhsType = _out1235;
                      Dafny.ISequence<Dafny.Rune> _1897_uneraseFn;
                      _1897_uneraseFn = ((_1893_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1896_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1897_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1892_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1893_recOwned;
                      isErased = false;
                      readIdents = _1895_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1236;
                      bool _out1237;
                      bool _out1238;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1239;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1891_b), _1891_b, _530_toTpe), selfIdent, @params, mustOwn, out _out1236, out _out1237, out _out1238, out _out1239);
                      s = _out1236;
                      isOwned = _out1237;
                      isErased = _out1238;
                      readIdents = _out1239;
                    }
                  }
                }
              } else if (_source67.is_Nullable) {
                DAST._IType _1898___mcc_h986 = _source67.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1899_recursiveGen;
                  bool _1900_recOwned;
                  bool _1901_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1240;
                  bool _out1241;
                  bool _out1242;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1243;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1240, out _out1241, out _out1242, out _out1243);
                  _1899_recursiveGen = _out1240;
                  _1900_recOwned = _out1241;
                  _1901_recErased = _out1242;
                  _1902_recIdents = _out1243;
                  if (!(_1900_recOwned)) {
                    _1899_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1899_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1899_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1901_recErased;
                  readIdents = _1902_recIdents;
                }
              } else if (_source67.is_Tuple) {
                Dafny.ISequence<DAST._IType> _1903___mcc_h988 = _source67.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1904_recursiveGen;
                  bool _1905_recOwned;
                  bool _1906_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1907_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1244;
                  bool _out1245;
                  bool _out1246;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1247;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1244, out _out1245, out _out1246, out _out1247);
                  _1904_recursiveGen = _out1244;
                  _1905_recOwned = _out1245;
                  _1906_recErased = _out1246;
                  _1907_recIdents = _out1247;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1904_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1905_recOwned;
                  isErased = _1906_recErased;
                  readIdents = _1907_recIdents;
                }
              } else if (_source67.is_Array) {
                DAST._IType _1908___mcc_h990 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1909_recursiveGen;
                  bool _1910_recOwned;
                  bool _1911_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1912_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1248;
                  bool _out1249;
                  bool _out1250;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1251;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1248, out _out1249, out _out1250, out _out1251);
                  _1909_recursiveGen = _out1248;
                  _1910_recOwned = _out1249;
                  _1911_recErased = _out1250;
                  _1912_recIdents = _out1251;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1909_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1910_recOwned;
                  isErased = _1911_recErased;
                  readIdents = _1912_recIdents;
                }
              } else if (_source67.is_Seq) {
                DAST._IType _1913___mcc_h992 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1914_recursiveGen;
                  bool _1915_recOwned;
                  bool _1916_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1917_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1252;
                  bool _out1253;
                  bool _out1254;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1255;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1252, out _out1253, out _out1254, out _out1255);
                  _1914_recursiveGen = _out1252;
                  _1915_recOwned = _out1253;
                  _1916_recErased = _out1254;
                  _1917_recIdents = _out1255;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1914_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1915_recOwned;
                  isErased = _1916_recErased;
                  readIdents = _1917_recIdents;
                }
              } else if (_source67.is_Set) {
                DAST._IType _1918___mcc_h994 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1919_recursiveGen;
                  bool _1920_recOwned;
                  bool _1921_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1922_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1256;
                  bool _out1257;
                  bool _out1258;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1259;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1256, out _out1257, out _out1258, out _out1259);
                  _1919_recursiveGen = _out1256;
                  _1920_recOwned = _out1257;
                  _1921_recErased = _out1258;
                  _1922_recIdents = _out1259;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1919_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1920_recOwned;
                  isErased = _1921_recErased;
                  readIdents = _1922_recIdents;
                }
              } else if (_source67.is_Multiset) {
                DAST._IType _1923___mcc_h996 = _source67.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _1924_recursiveGen;
                  bool _1925_recOwned;
                  bool _1926_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1927_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1260;
                  bool _out1261;
                  bool _out1262;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1263;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1260, out _out1261, out _out1262, out _out1263);
                  _1924_recursiveGen = _out1260;
                  _1925_recOwned = _out1261;
                  _1926_recErased = _out1262;
                  _1927_recIdents = _out1263;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1924_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1925_recOwned;
                  isErased = _1926_recErased;
                  readIdents = _1927_recIdents;
                }
              } else if (_source67.is_Map) {
                DAST._IType _1928___mcc_h998 = _source67.dtor_key;
                DAST._IType _1929___mcc_h999 = _source67.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _1930_recursiveGen;
                  bool _1931_recOwned;
                  bool _1932_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1933_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1264;
                  bool _out1265;
                  bool _out1266;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1267;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1264, out _out1265, out _out1266, out _out1267);
                  _1930_recursiveGen = _out1264;
                  _1931_recOwned = _out1265;
                  _1932_recErased = _out1266;
                  _1933_recIdents = _out1267;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1930_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1931_recOwned;
                  isErased = _1932_recErased;
                  readIdents = _1933_recIdents;
                }
              } else if (_source67.is_Arrow) {
                Dafny.ISequence<DAST._IType> _1934___mcc_h1002 = _source67.dtor_args;
                DAST._IType _1935___mcc_h1003 = _source67.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _1936_recursiveGen;
                  bool _1937_recOwned;
                  bool _1938_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1939_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1268;
                  bool _out1269;
                  bool _out1270;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1271;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1268, out _out1269, out _out1270, out _out1271);
                  _1936_recursiveGen = _out1268;
                  _1937_recOwned = _out1269;
                  _1938_recErased = _out1270;
                  _1939_recIdents = _out1271;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1936_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1937_recOwned;
                  isErased = _1938_recErased;
                  readIdents = _1939_recIdents;
                }
              } else if (_source67.is_Primitive) {
                DAST._IPrimitive _1940___mcc_h1006 = _source67.dtor_Primitive_a0;
                DAST._IPrimitive _source69 = _1940___mcc_h1006;
                if (_source69.is_Int) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1941_rhsType;
                    Dafny.ISequence<Dafny.Rune> _out1272;
                    _out1272 = DCOMP.COMP.GenType(_531_fromTpe, true, false);
                    _1941_rhsType = _out1272;
                    Dafny.ISequence<Dafny.Rune> _1942_recursiveGen;
                    bool _1943___v55;
                    bool _1944___v56;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1945_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1273;
                    bool _out1274;
                    bool _out1275;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1276;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, true, out _out1273, out _out1274, out _out1275, out _out1276);
                    _1942_recursiveGen = _out1273;
                    _1943___v55 = _out1274;
                    _1944___v56 = _out1275;
                    _1945_recIdents = _out1276;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from("), _1942_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                    isOwned = true;
                    isErased = true;
                    readIdents = _1945_recIdents;
                  }
                } else if (_source69.is_Real) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1946_recursiveGen;
                    bool _1947_recOwned;
                    bool _1948_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1277;
                    bool _out1278;
                    bool _out1279;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1280;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1277, out _out1278, out _out1279, out _out1280);
                    _1946_recursiveGen = _out1277;
                    _1947_recOwned = _out1278;
                    _1948_recErased = _out1279;
                    _1949_recIdents = _out1280;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1946_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1947_recOwned;
                    isErased = _1948_recErased;
                    readIdents = _1949_recIdents;
                  }
                } else if (_source69.is_String) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1950_recursiveGen;
                    bool _1951_recOwned;
                    bool _1952_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1953_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1281;
                    bool _out1282;
                    bool _out1283;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1284;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1281, out _out1282, out _out1283, out _out1284);
                    _1950_recursiveGen = _out1281;
                    _1951_recOwned = _out1282;
                    _1952_recErased = _out1283;
                    _1953_recIdents = _out1284;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1950_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1951_recOwned;
                    isErased = _1952_recErased;
                    readIdents = _1953_recIdents;
                  }
                } else if (_source69.is_Bool) {
                  {
                    Dafny.ISequence<Dafny.Rune> _1954_recursiveGen;
                    bool _1955_recOwned;
                    bool _1956_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1957_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1285;
                    bool _out1286;
                    bool _out1287;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1288;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1285, out _out1286, out _out1287, out _out1288);
                    _1954_recursiveGen = _out1285;
                    _1955_recOwned = _out1286;
                    _1956_recErased = _out1287;
                    _1957_recIdents = _out1288;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1954_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1955_recOwned;
                    isErased = _1956_recErased;
                    readIdents = _1957_recIdents;
                  }
                } else {
                  {
                    Dafny.ISequence<Dafny.Rune> _1958_recursiveGen;
                    bool _1959_recOwned;
                    bool _1960_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1289;
                    bool _out1290;
                    bool _out1291;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1292;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1289, out _out1290, out _out1291, out _out1292);
                    _1958_recursiveGen = _out1289;
                    _1959_recOwned = _out1290;
                    _1960_recErased = _out1291;
                    _1961_recIdents = _out1292;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1958_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1959_recOwned;
                    isErased = _1960_recErased;
                    readIdents = _1961_recIdents;
                  }
                }
              } else if (_source67.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1962___mcc_h1008 = _source67.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1963_recursiveGen;
                  bool _1964___v63;
                  bool _1965___v64;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1966_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1293;
                  bool _out1294;
                  bool _out1295;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1296;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, true, out _out1293, out _out1294, out _out1295, out _out1296);
                  _1963_recursiveGen = _out1293;
                  _1964___v63 = _out1294;
                  _1965___v64 = _out1295;
                  _1966_recIdents = _out1296;
                  Dafny.ISequence<Dafny.Rune> _1967_toTpeGen;
                  Dafny.ISequence<Dafny.Rune> _out1297;
                  _out1297 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                  _1967_toTpeGen = _out1297;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _1963_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), _1967_toTpeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = true;
                  readIdents = _1966_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _1968___mcc_h1010 = _source67.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1969_recursiveGen;
                  bool _1970_recOwned;
                  bool _1971_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1298;
                  bool _out1299;
                  bool _out1300;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1301;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1298, out _out1299, out _out1300, out _out1301);
                  _1969_recursiveGen = _out1298;
                  _1970_recOwned = _out1299;
                  _1971_recErased = _out1300;
                  _1972_recIdents = _out1301;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1969_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _1970_recOwned;
                  isErased = _1971_recErased;
                  readIdents = _1972_recIdents;
                }
              }
            } else {
              Dafny.ISequence<Dafny.Rune> _1973___mcc_h1012 = _source29.dtor_TypeArg_a0;
              DAST._IType _source70 = _538___mcc_h253;
              if (_source70.is_Path) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1974___mcc_h1016 = _source70.dtor_Path_a0;
                Dafny.ISequence<DAST._IType> _1975___mcc_h1017 = _source70.dtor_typeArgs;
                DAST._IResolvedType _1976___mcc_h1018 = _source70.dtor_resolved;
                DAST._IResolvedType _source71 = _1976___mcc_h1018;
                if (_source71.is_Datatype) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1977___mcc_h1022 = _source71.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1978_recursiveGen;
                    bool _1979_recOwned;
                    bool _1980_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1981_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1302;
                    bool _out1303;
                    bool _out1304;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1305;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1302, out _out1303, out _out1304, out _out1305);
                    _1978_recursiveGen = _out1302;
                    _1979_recOwned = _out1303;
                    _1980_recErased = _out1304;
                    _1981_recIdents = _out1305;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1978_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1979_recOwned;
                    isErased = _1980_recErased;
                    readIdents = _1981_recIdents;
                  }
                } else if (_source71.is_Trait) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1982___mcc_h1024 = _source71.dtor_path;
                  {
                    Dafny.ISequence<Dafny.Rune> _1983_recursiveGen;
                    bool _1984_recOwned;
                    bool _1985_recErased;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1986_recIdents;
                    Dafny.ISequence<Dafny.Rune> _out1306;
                    bool _out1307;
                    bool _out1308;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1309;
                    DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1306, out _out1307, out _out1308, out _out1309);
                    _1983_recursiveGen = _out1306;
                    _1984_recOwned = _out1307;
                    _1985_recErased = _out1308;
                    _1986_recIdents = _out1309;
                    s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1983_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                    isOwned = _1984_recOwned;
                    isErased = _1985_recErased;
                    readIdents = _1986_recIdents;
                  }
                } else {
                  DAST._IType _1987___mcc_h1026 = _source71.dtor_Newtype_a0;
                  DAST._IType _1988_b = _1987___mcc_h1026;
                  {
                    if (object.Equals(_531_fromTpe, _1988_b)) {
                      Dafny.ISequence<Dafny.Rune> _1989_recursiveGen;
                      bool _1990_recOwned;
                      bool _1991_recErased;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1992_recIdents;
                      Dafny.ISequence<Dafny.Rune> _out1310;
                      bool _out1311;
                      bool _out1312;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1313;
                      DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1310, out _out1311, out _out1312, out _out1313);
                      _1989_recursiveGen = _out1310;
                      _1990_recOwned = _out1311;
                      _1991_recErased = _out1312;
                      _1992_recIdents = _out1313;
                      Dafny.ISequence<Dafny.Rune> _1993_rhsType;
                      Dafny.ISequence<Dafny.Rune> _out1314;
                      _out1314 = DCOMP.COMP.GenType(_530_toTpe, true, false);
                      _1993_rhsType = _out1314;
                      Dafny.ISequence<Dafny.Rune> _1994_uneraseFn;
                      _1994_uneraseFn = ((_1990_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
                      s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1993_rhsType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::DafnyUnerasable<_>>::")), _1994_uneraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1989_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                      isOwned = _1990_recOwned;
                      isErased = false;
                      readIdents = _1992_recIdents;
                    } else {
                      Dafny.ISequence<Dafny.Rune> _out1315;
                      bool _out1316;
                      bool _out1317;
                      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1318;
                      DCOMP.COMP.GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_532_expr, _531_fromTpe, _1988_b), _1988_b, _530_toTpe), selfIdent, @params, mustOwn, out _out1315, out _out1316, out _out1317, out _out1318);
                      s = _out1315;
                      isOwned = _out1316;
                      isErased = _out1317;
                      readIdents = _out1318;
                    }
                  }
                }
              } else if (_source70.is_Nullable) {
                DAST._IType _1995___mcc_h1028 = _source70.dtor_Nullable_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _1996_recursiveGen;
                  bool _1997_recOwned;
                  bool _1998_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1999_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1319;
                  bool _out1320;
                  bool _out1321;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1322;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1319, out _out1320, out _out1321, out _out1322);
                  _1996_recursiveGen = _out1319;
                  _1997_recOwned = _out1320;
                  _1998_recErased = _out1321;
                  _1999_recIdents = _out1322;
                  if (!(_1997_recOwned)) {
                    _1996_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(_1996_recursiveGen, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                  }
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Some("), _1996_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
                  isOwned = true;
                  isErased = _1998_recErased;
                  readIdents = _1999_recIdents;
                }
              } else if (_source70.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2000___mcc_h1030 = _source70.dtor_Tuple_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2001_recursiveGen;
                  bool _2002_recOwned;
                  bool _2003_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2004_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1323;
                  bool _out1324;
                  bool _out1325;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1326;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1323, out _out1324, out _out1325, out _out1326);
                  _2001_recursiveGen = _out1323;
                  _2002_recOwned = _out1324;
                  _2003_recErased = _out1325;
                  _2004_recIdents = _out1326;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2001_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2002_recOwned;
                  isErased = _2003_recErased;
                  readIdents = _2004_recIdents;
                }
              } else if (_source70.is_Array) {
                DAST._IType _2005___mcc_h1032 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2006_recursiveGen;
                  bool _2007_recOwned;
                  bool _2008_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1327;
                  bool _out1328;
                  bool _out1329;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1330;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1327, out _out1328, out _out1329, out _out1330);
                  _2006_recursiveGen = _out1327;
                  _2007_recOwned = _out1328;
                  _2008_recErased = _out1329;
                  _2009_recIdents = _out1330;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2006_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2007_recOwned;
                  isErased = _2008_recErased;
                  readIdents = _2009_recIdents;
                }
              } else if (_source70.is_Seq) {
                DAST._IType _2010___mcc_h1034 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2011_recursiveGen;
                  bool _2012_recOwned;
                  bool _2013_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2014_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1331;
                  bool _out1332;
                  bool _out1333;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1334;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1331, out _out1332, out _out1333, out _out1334);
                  _2011_recursiveGen = _out1331;
                  _2012_recOwned = _out1332;
                  _2013_recErased = _out1333;
                  _2014_recIdents = _out1334;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2011_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2012_recOwned;
                  isErased = _2013_recErased;
                  readIdents = _2014_recIdents;
                }
              } else if (_source70.is_Set) {
                DAST._IType _2015___mcc_h1036 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2016_recursiveGen;
                  bool _2017_recOwned;
                  bool _2018_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2019_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1335;
                  bool _out1336;
                  bool _out1337;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1338;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1335, out _out1336, out _out1337, out _out1338);
                  _2016_recursiveGen = _out1335;
                  _2017_recOwned = _out1336;
                  _2018_recErased = _out1337;
                  _2019_recIdents = _out1338;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2016_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2017_recOwned;
                  isErased = _2018_recErased;
                  readIdents = _2019_recIdents;
                }
              } else if (_source70.is_Multiset) {
                DAST._IType _2020___mcc_h1038 = _source70.dtor_element;
                {
                  Dafny.ISequence<Dafny.Rune> _2021_recursiveGen;
                  bool _2022_recOwned;
                  bool _2023_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2024_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1339;
                  bool _out1340;
                  bool _out1341;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1342;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1339, out _out1340, out _out1341, out _out1342);
                  _2021_recursiveGen = _out1339;
                  _2022_recOwned = _out1340;
                  _2023_recErased = _out1341;
                  _2024_recIdents = _out1342;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2021_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2022_recOwned;
                  isErased = _2023_recErased;
                  readIdents = _2024_recIdents;
                }
              } else if (_source70.is_Map) {
                DAST._IType _2025___mcc_h1040 = _source70.dtor_key;
                DAST._IType _2026___mcc_h1041 = _source70.dtor_value;
                {
                  Dafny.ISequence<Dafny.Rune> _2027_recursiveGen;
                  bool _2028_recOwned;
                  bool _2029_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2030_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1343;
                  bool _out1344;
                  bool _out1345;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1346;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1343, out _out1344, out _out1345, out _out1346);
                  _2027_recursiveGen = _out1343;
                  _2028_recOwned = _out1344;
                  _2029_recErased = _out1345;
                  _2030_recIdents = _out1346;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2027_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2028_recOwned;
                  isErased = _2029_recErased;
                  readIdents = _2030_recIdents;
                }
              } else if (_source70.is_Arrow) {
                Dafny.ISequence<DAST._IType> _2031___mcc_h1044 = _source70.dtor_args;
                DAST._IType _2032___mcc_h1045 = _source70.dtor_result;
                {
                  Dafny.ISequence<Dafny.Rune> _2033_recursiveGen;
                  bool _2034_recOwned;
                  bool _2035_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2036_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1347;
                  bool _out1348;
                  bool _out1349;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1350;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1347, out _out1348, out _out1349, out _out1350);
                  _2033_recursiveGen = _out1347;
                  _2034_recOwned = _out1348;
                  _2035_recErased = _out1349;
                  _2036_recIdents = _out1350;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2033_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2034_recOwned;
                  isErased = _2035_recErased;
                  readIdents = _2036_recIdents;
                }
              } else if (_source70.is_Primitive) {
                DAST._IPrimitive _2037___mcc_h1048 = _source70.dtor_Primitive_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2038_recursiveGen;
                  bool _2039_recOwned;
                  bool _2040_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2041_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1351;
                  bool _out1352;
                  bool _out1353;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1354;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1351, out _out1352, out _out1353, out _out1354);
                  _2038_recursiveGen = _out1351;
                  _2039_recOwned = _out1352;
                  _2040_recErased = _out1353;
                  _2041_recIdents = _out1354;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2038_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2039_recOwned;
                  isErased = _2040_recErased;
                  readIdents = _2041_recIdents;
                }
              } else if (_source70.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _2042___mcc_h1050 = _source70.dtor_Passthrough_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2043_recursiveGen;
                  bool _2044_recOwned;
                  bool _2045_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2046_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1355;
                  bool _out1356;
                  bool _out1357;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1358;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1355, out _out1356, out _out1357, out _out1358);
                  _2043_recursiveGen = _out1355;
                  _2044_recOwned = _out1356;
                  _2045_recErased = _out1357;
                  _2046_recIdents = _out1358;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2043_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2044_recOwned;
                  isErased = _2045_recErased;
                  readIdents = _2046_recIdents;
                }
              } else {
                Dafny.ISequence<Dafny.Rune> _2047___mcc_h1052 = _source70.dtor_TypeArg_a0;
                {
                  Dafny.ISequence<Dafny.Rune> _2048_recursiveGen;
                  bool _2049_recOwned;
                  bool _2050_recErased;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2051_recIdents;
                  Dafny.ISequence<Dafny.Rune> _out1359;
                  bool _out1360;
                  bool _out1361;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1362;
                  DCOMP.COMP.GenExpr(_532_expr, selfIdent, @params, mustOwn, out _out1359, out _out1360, out _out1361, out _out1362);
                  _2048_recursiveGen = _out1359;
                  _2049_recOwned = _out1360;
                  _2050_recErased = _out1361;
                  _2051_recIdents = _out1362;
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2048_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* conversion not yet implemented */)"));
                  isOwned = _2049_recOwned;
                  isErased = _2050_recErased;
                  readIdents = _2051_recIdents;
                }
              }
            }
          }
        }
      } else if (_source22.is_SeqValue) {
        Dafny.ISequence<DAST._IExpression> _2052___mcc_h22 = _source22.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2053_exprs = _2052___mcc_h22;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2054_generatedValues;
          _2054_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2055_i;
          _2055_i = BigInteger.Zero;
          bool _2056_allErased;
          _2056_allErased = true;
          while ((_2055_i) < (new BigInteger((_2053_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2057_recursiveGen;
            bool _2058___v66;
            bool _2059_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2060_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1363;
            bool _out1364;
            bool _out1365;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1366;
            DCOMP.COMP.GenExpr((_2053_exprs).Select(_2055_i), selfIdent, @params, true, out _out1363, out _out1364, out _out1365, out _out1366);
            _2057_recursiveGen = _out1363;
            _2058___v66 = _out1364;
            _2059_isErased = _out1365;
            _2060_recIdents = _out1366;
            _2056_allErased = (_2056_allErased) && (_2059_isErased);
            _2054_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2054_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2057_recursiveGen, _2059_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2060_recIdents);
            _2055_i = (_2055_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2055_i = BigInteger.Zero;
          while ((_2055_i) < (new BigInteger((_2054_generatedValues).Count))) {
            if ((_2055_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2061_gen;
            _2061_gen = ((_2054_generatedValues).Select(_2055_i)).dtor__0;
            if ((((_2054_generatedValues).Select(_2055_i)).dtor__1) && (!(_2056_allErased))) {
              _2061_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2061_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2061_gen);
            _2055_i = (_2055_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isOwned = true;
          isErased = _2056_allErased;
        }
      } else if (_source22.is_SetValue) {
        Dafny.ISequence<DAST._IExpression> _2062___mcc_h23 = _source22.dtor_elements;
        Dafny.ISequence<DAST._IExpression> _2063_exprs = _2062___mcc_h23;
        {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>> _2064_generatedValues;
          _2064_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements();
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2065_i;
          _2065_i = BigInteger.Zero;
          bool _2066_allErased;
          _2066_allErased = true;
          while ((_2065_i) < (new BigInteger((_2063_exprs).Count))) {
            Dafny.ISequence<Dafny.Rune> _2067_recursiveGen;
            bool _2068___v67;
            bool _2069_isErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2070_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1367;
            bool _out1368;
            bool _out1369;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1370;
            DCOMP.COMP.GenExpr((_2063_exprs).Select(_2065_i), selfIdent, @params, true, out _out1367, out _out1368, out _out1369, out _out1370);
            _2067_recursiveGen = _out1367;
            _2068___v67 = _out1368;
            _2069_isErased = _out1369;
            _2070_recIdents = _out1370;
            _2066_allErased = (_2066_allErased) && (_2069_isErased);
            _2064_generatedValues = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.Concat(_2064_generatedValues, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, bool>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, bool>.create(_2067_recursiveGen, _2069_isErased)));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2070_recIdents);
            _2065_i = (_2065_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec![");
          _2065_i = BigInteger.Zero;
          while ((_2065_i) < (new BigInteger((_2064_generatedValues).Count))) {
            if ((_2065_i).Sign == 1) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2071_gen;
            _2071_gen = ((_2064_generatedValues).Select(_2065_i)).dtor__0;
            if ((((_2064_generatedValues).Select(_2065_i)).dtor__1) && (!(_2066_allErased))) {
              _2071_gen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::unerase_owned("), _2071_gen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2071_gen);
            _2065_i = (_2065_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("].into_iter().collect::<std::collections::HashSet<_>>()"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_This) {
        {
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _source72 = selfIdent;
          if (_source72.is_Some) {
            Dafny.ISequence<Dafny.Rune> _2072___mcc_h1054 = _source72.dtor_Some_a0;
            Dafny.ISequence<Dafny.Rune> _2073_id = _2072___mcc_h1054;
            {
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(_2073_id, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
                isOwned = true;
              } else {
                if ((_2073_id).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                  s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
                } else {
                  s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2073_id);
                }
                isOwned = false;
              }
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2073_id);
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
        DAST._IExpression _2074___mcc_h24 = _source22.dtor_cond;
        DAST._IExpression _2075___mcc_h25 = _source22.dtor_thn;
        DAST._IExpression _2076___mcc_h26 = _source22.dtor_els;
        DAST._IExpression _2077_f = _2076___mcc_h26;
        DAST._IExpression _2078_t = _2075___mcc_h25;
        DAST._IExpression _2079_cond = _2074___mcc_h24;
        {
          Dafny.ISequence<Dafny.Rune> _2080_condString;
          bool _2081___v68;
          bool _2082_condErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2083_recIdentsCond;
          Dafny.ISequence<Dafny.Rune> _out1371;
          bool _out1372;
          bool _out1373;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1374;
          DCOMP.COMP.GenExpr(_2079_cond, selfIdent, @params, true, out _out1371, out _out1372, out _out1373, out _out1374);
          _2080_condString = _out1371;
          _2081___v68 = _out1372;
          _2082_condErased = _out1373;
          _2083_recIdentsCond = _out1374;
          if (!(_2082_condErased)) {
            _2080_condString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2080_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          Dafny.ISequence<Dafny.Rune> _2084___v69;
          bool _2085_tHasToBeOwned;
          bool _2086___v70;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2087___v71;
          Dafny.ISequence<Dafny.Rune> _out1375;
          bool _out1376;
          bool _out1377;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1378;
          DCOMP.COMP.GenExpr(_2078_t, selfIdent, @params, mustOwn, out _out1375, out _out1376, out _out1377, out _out1378);
          _2084___v69 = _out1375;
          _2085_tHasToBeOwned = _out1376;
          _2086___v70 = _out1377;
          _2087___v71 = _out1378;
          Dafny.ISequence<Dafny.Rune> _2088_fString;
          bool _2089_fOwned;
          bool _2090_fErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2091_recIdentsF;
          Dafny.ISequence<Dafny.Rune> _out1379;
          bool _out1380;
          bool _out1381;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1382;
          DCOMP.COMP.GenExpr(_2077_f, selfIdent, @params, _2085_tHasToBeOwned, out _out1379, out _out1380, out _out1381, out _out1382);
          _2088_fString = _out1379;
          _2089_fOwned = _out1380;
          _2090_fErased = _out1381;
          _2091_recIdentsF = _out1382;
          Dafny.ISequence<Dafny.Rune> _2092_tString;
          bool _2093___v72;
          bool _2094_tErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2095_recIdentsT;
          Dafny.ISequence<Dafny.Rune> _out1383;
          bool _out1384;
          bool _out1385;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1386;
          DCOMP.COMP.GenExpr(_2078_t, selfIdent, @params, _2089_fOwned, out _out1383, out _out1384, out _out1385, out _out1386);
          _2092_tString = _out1383;
          _2093___v72 = _out1384;
          _2094_tErased = _out1385;
          _2095_recIdentsT = _out1386;
          if ((!(_2090_fErased)) || (!(_2094_tErased))) {
            if (_2090_fErased) {
              _2088_fString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2088_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2094_tErased) {
              _2092_tString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2092_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(if "), _2080_condString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2092_tString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n} else {\n")), _2088_fString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})"));
          isOwned = _2089_fOwned;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2083_recIdentsCond, _2095_recIdentsT), _2091_recIdentsF);
          isErased = (_2090_fErased) || (_2094_tErased);
        }
      } else if (_source22.is_UnOp) {
        DAST._IUnaryOp _2096___mcc_h27 = _source22.dtor_unOp;
        DAST._IExpression _2097___mcc_h28 = _source22.dtor_expr;
        DAST._IUnaryOp _source73 = _2096___mcc_h27;
        if (_source73.is_Not) {
          DAST._IExpression _2098_e = _2097___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2099_recursiveGen;
            bool _2100___v73;
            bool _2101_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2102_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1387;
            bool _out1388;
            bool _out1389;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1390;
            DCOMP.COMP.GenExpr(_2098_e, selfIdent, @params, true, out _out1387, out _out1388, out _out1389, out _out1390);
            _2099_recursiveGen = _out1387;
            _2100___v73 = _out1388;
            _2101_recErased = _out1389;
            _2102_recIdents = _out1390;
            if (!(_2101_recErased)) {
              _2099_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2099_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!("), _2099_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2102_recIdents;
            isErased = true;
          }
        } else if (_source73.is_BitwiseNot) {
          DAST._IExpression _2103_e = _2097___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2104_recursiveGen;
            bool _2105___v74;
            bool _2106_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2107_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1391;
            bool _out1392;
            bool _out1393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1394;
            DCOMP.COMP.GenExpr(_2103_e, selfIdent, @params, true, out _out1391, out _out1392, out _out1393, out _out1394);
            _2104_recursiveGen = _out1391;
            _2105___v74 = _out1392;
            _2106_recErased = _out1393;
            _2107_recIdents = _out1394;
            if (!(_2106_recErased)) {
              _2104_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2104_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~("), _2104_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = true;
            readIdents = _2107_recIdents;
            isErased = true;
          }
        } else {
          DAST._IExpression _2108_e = _2097___mcc_h28;
          {
            Dafny.ISequence<Dafny.Rune> _2109_recursiveGen;
            bool _2110_recOwned;
            bool _2111_recErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2112_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1395;
            bool _out1396;
            bool _out1397;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1398;
            DCOMP.COMP.GenExpr(_2108_e, selfIdent, @params, false, out _out1395, out _out1396, out _out1397, out _out1398);
            _2109_recursiveGen = _out1395;
            _2110_recOwned = _out1396;
            _2111_recErased = _out1397;
            _2112_recIdents = _out1398;
            if (!(_2111_recErased)) {
              Dafny.ISequence<Dafny.Rune> _2113_eraseFn;
              _2113_eraseFn = ((_2110_recOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2109_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2113_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2109_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2109_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").len())"));
            isOwned = true;
            readIdents = _2112_recIdents;
            isErased = true;
          }
        }
      } else if (_source22.is_BinOp) {
        Dafny.ISequence<Dafny.Rune> _2114___mcc_h29 = _source22.dtor_op;
        DAST._IExpression _2115___mcc_h30 = _source22.dtor_left;
        DAST._IExpression _2116___mcc_h31 = _source22.dtor_right;
        DAST._IExpression _2117_r = _2116___mcc_h31;
        DAST._IExpression _2118_l = _2115___mcc_h30;
        Dafny.ISequence<Dafny.Rune> _2119_op = _2114___mcc_h29;
        {
          Dafny.ISequence<Dafny.Rune> _2120_left;
          bool _2121___v75;
          bool _2122_leftErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2123_recIdentsL;
          Dafny.ISequence<Dafny.Rune> _out1399;
          bool _out1400;
          bool _out1401;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1402;
          DCOMP.COMP.GenExpr(_2118_l, selfIdent, @params, true, out _out1399, out _out1400, out _out1401, out _out1402);
          _2120_left = _out1399;
          _2121___v75 = _out1400;
          _2122_leftErased = _out1401;
          _2123_recIdentsL = _out1402;
          Dafny.ISequence<Dafny.Rune> _2124_right;
          bool _2125___v76;
          bool _2126_rightErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2127_recIdentsR;
          Dafny.ISequence<Dafny.Rune> _out1403;
          bool _out1404;
          bool _out1405;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1406;
          DCOMP.COMP.GenExpr(_2117_r, selfIdent, @params, true, out _out1403, out _out1404, out _out1405, out _out1406);
          _2124_right = _out1403;
          _2125___v76 = _out1404;
          _2126_rightErased = _out1405;
          _2127_recIdentsR = _out1406;
          if (!(_2122_leftErased)) {
            _2120_left = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2120_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if (!(_2126_rightErased)) {
            _2124_right = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2124_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          if ((_2119_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division("), _2120_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2124_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else if ((_2119_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo("), _2120_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")), _2124_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2120_left), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2119_op), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), _2124_right), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          isOwned = true;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2123_recIdentsL, _2127_recIdentsR);
          isErased = true;
        }
      } else if (_source22.is_ArrayLen) {
        DAST._IExpression _2128___mcc_h32 = _source22.dtor_expr;
        DAST._IExpression _2129_expr = _2128___mcc_h32;
        {
          Dafny.ISequence<Dafny.Rune> _2130_recursiveGen;
          bool _2131___v77;
          bool _2132_recErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2133_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1407;
          bool _out1408;
          bool _out1409;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1410;
          DCOMP.COMP.GenExpr(_2129_expr, selfIdent, @params, true, out _out1407, out _out1408, out _out1409, out _out1410);
          _2130_recursiveGen = _out1407;
          _2131___v77 = _out1408;
          _2132_recErased = _out1409;
          _2133_recIdents = _out1410;
          if (!(_2132_recErased)) {
            _2130_recursiveGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2130_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigInt::from(("), _2130_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow().len())"));
          isOwned = true;
          readIdents = _2133_recIdents;
          isErased = true;
        }
      } else if (_source22.is_Select) {
        DAST._IExpression _2134___mcc_h33 = _source22.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2135___mcc_h34 = _source22.dtor_field;
        bool _2136___mcc_h35 = _source22.dtor_isConstant;
        bool _2137___mcc_h36 = _source22.dtor_onDatatype;
        DAST._IExpression _source74 = _2134___mcc_h33;
        if (_source74.is_Literal) {
          DAST._ILiteral _2138___mcc_h37 = _source74.dtor_Literal_a0;
          bool _2139_isDatatype = _2137___mcc_h36;
          bool _2140_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2141_field = _2135___mcc_h34;
          DAST._IExpression _2142_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2143_onString;
            bool _2144_onOwned;
            bool _2145_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2146_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1411;
            bool _out1412;
            bool _out1413;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1414;
            DCOMP.COMP.GenExpr(_2142_on, selfIdent, @params, false, out _out1411, out _out1412, out _out1413, out _out1414);
            _2143_onString = _out1411;
            _2144_onOwned = _out1412;
            _2145_onErased = _out1413;
            _2146_recIdents = _out1414;
            if (!(_2145_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2147_eraseFn;
              _2147_eraseFn = ((_2144_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2143_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2147_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2143_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2139_isDatatype) || (_2140_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2143_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2141_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2140_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2143_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2141_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2146_recIdents;
          }
        } else if (_source74.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2148___mcc_h39 = _source74.dtor_Ident_a0;
          bool _2149_isDatatype = _2137___mcc_h36;
          bool _2150_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2151_field = _2135___mcc_h34;
          DAST._IExpression _2152_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2153_onString;
            bool _2154_onOwned;
            bool _2155_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2156_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1415;
            bool _out1416;
            bool _out1417;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1418;
            DCOMP.COMP.GenExpr(_2152_on, selfIdent, @params, false, out _out1415, out _out1416, out _out1417, out _out1418);
            _2153_onString = _out1415;
            _2154_onOwned = _out1416;
            _2155_onErased = _out1417;
            _2156_recIdents = _out1418;
            if (!(_2155_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2157_eraseFn;
              _2157_eraseFn = ((_2154_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2153_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2157_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2153_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2149_isDatatype) || (_2150_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2153_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2151_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2150_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2153_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2151_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2156_recIdents;
          }
        } else if (_source74.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2158___mcc_h41 = _source74.dtor_Companion_a0;
          bool _2159_isDatatype = _2137___mcc_h36;
          bool _2160_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2161_field = _2135___mcc_h34;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2162_c = _2158___mcc_h41;
          {
            Dafny.ISequence<Dafny.Rune> _2163_onString;
            bool _2164_onOwned;
            bool _2165_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2166_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1419;
            bool _out1420;
            bool _out1421;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1422;
            DCOMP.COMP.GenExpr(DAST.Expression.create_Companion(_2162_c), selfIdent, @params, false, out _out1419, out _out1420, out _out1421, out _out1422);
            _2163_onString = _out1419;
            _2164_onOwned = _out1420;
            _2165_onErased = _out1421;
            _2166_recIdents = _out1422;
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2163_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2161_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
            isOwned = true;
            isErased = false;
            readIdents = _2166_recIdents;
          }
        } else if (_source74.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2167___mcc_h43 = _source74.dtor_Tuple_a0;
          bool _2168_isDatatype = _2137___mcc_h36;
          bool _2169_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2170_field = _2135___mcc_h34;
          DAST._IExpression _2171_on = _2134___mcc_h33;
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
        } else if (_source74.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2177___mcc_h45 = _source74.dtor_path;
          Dafny.ISequence<DAST._IExpression> _2178___mcc_h46 = _source74.dtor_args;
          bool _2179_isDatatype = _2137___mcc_h36;
          bool _2180_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2181_field = _2135___mcc_h34;
          DAST._IExpression _2182_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2183_onString;
            bool _2184_onOwned;
            bool _2185_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2186_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1427;
            bool _out1428;
            bool _out1429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1430;
            DCOMP.COMP.GenExpr(_2182_on, selfIdent, @params, false, out _out1427, out _out1428, out _out1429, out _out1430);
            _2183_onString = _out1427;
            _2184_onOwned = _out1428;
            _2185_onErased = _out1429;
            _2186_recIdents = _out1430;
            if (!(_2185_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2187_eraseFn;
              _2187_eraseFn = ((_2184_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2183_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2187_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2183_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2179_isDatatype) || (_2180_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2183_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2181_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2180_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2183_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2181_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2186_recIdents;
          }
        } else if (_source74.is_NewArray) {
          Dafny.ISequence<DAST._IExpression> _2188___mcc_h49 = _source74.dtor_dims;
          bool _2189_isDatatype = _2137___mcc_h36;
          bool _2190_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2191_field = _2135___mcc_h34;
          DAST._IExpression _2192_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2193_onString;
            bool _2194_onOwned;
            bool _2195_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2196_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1431;
            bool _out1432;
            bool _out1433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1434;
            DCOMP.COMP.GenExpr(_2192_on, selfIdent, @params, false, out _out1431, out _out1432, out _out1433, out _out1434);
            _2193_onString = _out1431;
            _2194_onOwned = _out1432;
            _2195_onErased = _out1433;
            _2196_recIdents = _out1434;
            if (!(_2195_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2197_eraseFn;
              _2197_eraseFn = ((_2194_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2193_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2197_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2193_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2189_isDatatype) || (_2190_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2193_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2191_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2190_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2193_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2191_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2196_recIdents;
          }
        } else if (_source74.is_DatatypeValue) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2198___mcc_h51 = _source74.dtor_path;
          Dafny.ISequence<Dafny.Rune> _2199___mcc_h52 = _source74.dtor_variant;
          bool _2200___mcc_h53 = _source74.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2201___mcc_h54 = _source74.dtor_contents;
          bool _2202_isDatatype = _2137___mcc_h36;
          bool _2203_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2204_field = _2135___mcc_h34;
          DAST._IExpression _2205_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2206_onString;
            bool _2207_onOwned;
            bool _2208_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2209_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1435;
            bool _out1436;
            bool _out1437;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1438;
            DCOMP.COMP.GenExpr(_2205_on, selfIdent, @params, false, out _out1435, out _out1436, out _out1437, out _out1438);
            _2206_onString = _out1435;
            _2207_onOwned = _out1436;
            _2208_onErased = _out1437;
            _2209_recIdents = _out1438;
            if (!(_2208_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2210_eraseFn;
              _2210_eraseFn = ((_2207_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2206_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2210_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2206_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2202_isDatatype) || (_2203_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2206_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2204_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2203_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2206_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2204_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2209_recIdents;
          }
        } else if (_source74.is_Convert) {
          DAST._IExpression _2211___mcc_h59 = _source74.dtor_value;
          DAST._IType _2212___mcc_h60 = _source74.dtor_from;
          DAST._IType _2213___mcc_h61 = _source74.dtor_typ;
          bool _2214_isDatatype = _2137___mcc_h36;
          bool _2215_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2216_field = _2135___mcc_h34;
          DAST._IExpression _2217_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2218_onString;
            bool _2219_onOwned;
            bool _2220_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2221_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1439;
            bool _out1440;
            bool _out1441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1442;
            DCOMP.COMP.GenExpr(_2217_on, selfIdent, @params, false, out _out1439, out _out1440, out _out1441, out _out1442);
            _2218_onString = _out1439;
            _2219_onOwned = _out1440;
            _2220_onErased = _out1441;
            _2221_recIdents = _out1442;
            if (!(_2220_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2222_eraseFn;
              _2222_eraseFn = ((_2219_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2218_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2222_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2218_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2214_isDatatype) || (_2215_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2218_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2216_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2215_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2218_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2216_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2221_recIdents;
          }
        } else if (_source74.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2223___mcc_h65 = _source74.dtor_elements;
          bool _2224_isDatatype = _2137___mcc_h36;
          bool _2225_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2226_field = _2135___mcc_h34;
          DAST._IExpression _2227_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2228_onString;
            bool _2229_onOwned;
            bool _2230_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2231_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1443;
            bool _out1444;
            bool _out1445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1446;
            DCOMP.COMP.GenExpr(_2227_on, selfIdent, @params, false, out _out1443, out _out1444, out _out1445, out _out1446);
            _2228_onString = _out1443;
            _2229_onOwned = _out1444;
            _2230_onErased = _out1445;
            _2231_recIdents = _out1446;
            if (!(_2230_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2232_eraseFn;
              _2232_eraseFn = ((_2229_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2228_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2232_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2228_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2224_isDatatype) || (_2225_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2228_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2226_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2225_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2228_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2226_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2231_recIdents;
          }
        } else if (_source74.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2233___mcc_h67 = _source74.dtor_elements;
          bool _2234_isDatatype = _2137___mcc_h36;
          bool _2235_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2236_field = _2135___mcc_h34;
          DAST._IExpression _2237_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2238_onString;
            bool _2239_onOwned;
            bool _2240_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2241_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1447;
            bool _out1448;
            bool _out1449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1450;
            DCOMP.COMP.GenExpr(_2237_on, selfIdent, @params, false, out _out1447, out _out1448, out _out1449, out _out1450);
            _2238_onString = _out1447;
            _2239_onOwned = _out1448;
            _2240_onErased = _out1449;
            _2241_recIdents = _out1450;
            if (!(_2240_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2242_eraseFn;
              _2242_eraseFn = ((_2239_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2238_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2242_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2238_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2234_isDatatype) || (_2235_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2238_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2236_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2235_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2238_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2236_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2241_recIdents;
          }
        } else if (_source74.is_This) {
          bool _2243_isDatatype = _2137___mcc_h36;
          bool _2244_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2245_field = _2135___mcc_h34;
          DAST._IExpression _2246_on = _2134___mcc_h33;
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
        } else if (_source74.is_Ite) {
          DAST._IExpression _2252___mcc_h69 = _source74.dtor_cond;
          DAST._IExpression _2253___mcc_h70 = _source74.dtor_thn;
          DAST._IExpression _2254___mcc_h71 = _source74.dtor_els;
          bool _2255_isDatatype = _2137___mcc_h36;
          bool _2256_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2257_field = _2135___mcc_h34;
          DAST._IExpression _2258_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2259_onString;
            bool _2260_onOwned;
            bool _2261_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2262_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1455;
            bool _out1456;
            bool _out1457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1458;
            DCOMP.COMP.GenExpr(_2258_on, selfIdent, @params, false, out _out1455, out _out1456, out _out1457, out _out1458);
            _2259_onString = _out1455;
            _2260_onOwned = _out1456;
            _2261_onErased = _out1457;
            _2262_recIdents = _out1458;
            if (!(_2261_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2263_eraseFn;
              _2263_eraseFn = ((_2260_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2259_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2263_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2259_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2255_isDatatype) || (_2256_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2259_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2257_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2256_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2259_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2257_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2262_recIdents;
          }
        } else if (_source74.is_UnOp) {
          DAST._IUnaryOp _2264___mcc_h75 = _source74.dtor_unOp;
          DAST._IExpression _2265___mcc_h76 = _source74.dtor_expr;
          bool _2266_isDatatype = _2137___mcc_h36;
          bool _2267_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2268_field = _2135___mcc_h34;
          DAST._IExpression _2269_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2270_onString;
            bool _2271_onOwned;
            bool _2272_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2273_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1459;
            bool _out1460;
            bool _out1461;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1462;
            DCOMP.COMP.GenExpr(_2269_on, selfIdent, @params, false, out _out1459, out _out1460, out _out1461, out _out1462);
            _2270_onString = _out1459;
            _2271_onOwned = _out1460;
            _2272_onErased = _out1461;
            _2273_recIdents = _out1462;
            if (!(_2272_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2274_eraseFn;
              _2274_eraseFn = ((_2271_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2270_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2274_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2270_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2266_isDatatype) || (_2267_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2270_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2268_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2267_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2270_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2268_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2273_recIdents;
          }
        } else if (_source74.is_BinOp) {
          Dafny.ISequence<Dafny.Rune> _2275___mcc_h79 = _source74.dtor_op;
          DAST._IExpression _2276___mcc_h80 = _source74.dtor_left;
          DAST._IExpression _2277___mcc_h81 = _source74.dtor_right;
          bool _2278_isDatatype = _2137___mcc_h36;
          bool _2279_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2280_field = _2135___mcc_h34;
          DAST._IExpression _2281_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2282_onString;
            bool _2283_onOwned;
            bool _2284_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2285_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1463;
            bool _out1464;
            bool _out1465;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1466;
            DCOMP.COMP.GenExpr(_2281_on, selfIdent, @params, false, out _out1463, out _out1464, out _out1465, out _out1466);
            _2282_onString = _out1463;
            _2283_onOwned = _out1464;
            _2284_onErased = _out1465;
            _2285_recIdents = _out1466;
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
        } else if (_source74.is_ArrayLen) {
          DAST._IExpression _2287___mcc_h85 = _source74.dtor_expr;
          bool _2288_isDatatype = _2137___mcc_h36;
          bool _2289_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2290_field = _2135___mcc_h34;
          DAST._IExpression _2291_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2292_onString;
            bool _2293_onOwned;
            bool _2294_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2295_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1467;
            bool _out1468;
            bool _out1469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1470;
            DCOMP.COMP.GenExpr(_2291_on, selfIdent, @params, false, out _out1467, out _out1468, out _out1469, out _out1470);
            _2292_onString = _out1467;
            _2293_onOwned = _out1468;
            _2294_onErased = _out1469;
            _2295_recIdents = _out1470;
            if (!(_2294_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2296_eraseFn;
              _2296_eraseFn = ((_2293_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2292_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2296_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2292_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2288_isDatatype) || (_2289_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2292_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2290_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2289_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2292_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2290_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2295_recIdents;
          }
        } else if (_source74.is_Select) {
          DAST._IExpression _2297___mcc_h87 = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2298___mcc_h88 = _source74.dtor_field;
          bool _2299___mcc_h89 = _source74.dtor_isConstant;
          bool _2300___mcc_h90 = _source74.dtor_onDatatype;
          bool _2301_isDatatype = _2137___mcc_h36;
          bool _2302_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2303_field = _2135___mcc_h34;
          DAST._IExpression _2304_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2305_onString;
            bool _2306_onOwned;
            bool _2307_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2308_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1471;
            bool _out1472;
            bool _out1473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1474;
            DCOMP.COMP.GenExpr(_2304_on, selfIdent, @params, false, out _out1471, out _out1472, out _out1473, out _out1474);
            _2305_onString = _out1471;
            _2306_onOwned = _out1472;
            _2307_onErased = _out1473;
            _2308_recIdents = _out1474;
            if (!(_2307_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2309_eraseFn;
              _2309_eraseFn = ((_2306_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2305_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2309_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2305_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2301_isDatatype) || (_2302_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2305_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2303_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2302_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2305_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2303_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2308_recIdents;
          }
        } else if (_source74.is_SelectFn) {
          DAST._IExpression _2310___mcc_h95 = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2311___mcc_h96 = _source74.dtor_field;
          bool _2312___mcc_h97 = _source74.dtor_onDatatype;
          bool _2313___mcc_h98 = _source74.dtor_isStatic;
          BigInteger _2314___mcc_h99 = _source74.dtor_arity;
          bool _2315_isDatatype = _2137___mcc_h36;
          bool _2316_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2317_field = _2135___mcc_h34;
          DAST._IExpression _2318_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2319_onString;
            bool _2320_onOwned;
            bool _2321_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2322_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1475;
            bool _out1476;
            bool _out1477;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1478;
            DCOMP.COMP.GenExpr(_2318_on, selfIdent, @params, false, out _out1475, out _out1476, out _out1477, out _out1478);
            _2319_onString = _out1475;
            _2320_onOwned = _out1476;
            _2321_onErased = _out1477;
            _2322_recIdents = _out1478;
            if (!(_2321_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2323_eraseFn;
              _2323_eraseFn = ((_2320_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2319_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2323_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2319_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2315_isDatatype) || (_2316_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2319_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2317_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2316_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2319_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2317_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2322_recIdents;
          }
        } else if (_source74.is_Index) {
          DAST._IExpression _2324___mcc_h105 = _source74.dtor_expr;
          bool _2325___mcc_h106 = _source74.dtor_isArray;
          Dafny.ISequence<DAST._IExpression> _2326___mcc_h107 = _source74.dtor_indices;
          bool _2327_isDatatype = _2137___mcc_h36;
          bool _2328_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2329_field = _2135___mcc_h34;
          DAST._IExpression _2330_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2331_onString;
            bool _2332_onOwned;
            bool _2333_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2334_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1479;
            bool _out1480;
            bool _out1481;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1482;
            DCOMP.COMP.GenExpr(_2330_on, selfIdent, @params, false, out _out1479, out _out1480, out _out1481, out _out1482);
            _2331_onString = _out1479;
            _2332_onOwned = _out1480;
            _2333_onErased = _out1481;
            _2334_recIdents = _out1482;
            if (!(_2333_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2335_eraseFn;
              _2335_eraseFn = ((_2332_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2331_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2335_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2331_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2327_isDatatype) || (_2328_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2331_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2329_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2328_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2331_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2329_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2334_recIdents;
          }
        } else if (_source74.is_IndexRange) {
          DAST._IExpression _2336___mcc_h111 = _source74.dtor_expr;
          bool _2337___mcc_h112 = _source74.dtor_isArray;
          DAST._IOptional<DAST._IExpression> _2338___mcc_h113 = _source74.dtor_low;
          DAST._IOptional<DAST._IExpression> _2339___mcc_h114 = _source74.dtor_high;
          bool _2340_isDatatype = _2137___mcc_h36;
          bool _2341_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2342_field = _2135___mcc_h34;
          DAST._IExpression _2343_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2344_onString;
            bool _2345_onOwned;
            bool _2346_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2347_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1483;
            bool _out1484;
            bool _out1485;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1486;
            DCOMP.COMP.GenExpr(_2343_on, selfIdent, @params, false, out _out1483, out _out1484, out _out1485, out _out1486);
            _2344_onString = _out1483;
            _2345_onOwned = _out1484;
            _2346_onErased = _out1485;
            _2347_recIdents = _out1486;
            if (!(_2346_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2348_eraseFn;
              _2348_eraseFn = ((_2345_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2344_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2348_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2344_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2340_isDatatype) || (_2341_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2344_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2342_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2341_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2344_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2342_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2347_recIdents;
          }
        } else if (_source74.is_TupleSelect) {
          DAST._IExpression _2349___mcc_h119 = _source74.dtor_expr;
          BigInteger _2350___mcc_h120 = _source74.dtor_index;
          bool _2351_isDatatype = _2137___mcc_h36;
          bool _2352_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2353_field = _2135___mcc_h34;
          DAST._IExpression _2354_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2355_onString;
            bool _2356_onOwned;
            bool _2357_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2358_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1487;
            bool _out1488;
            bool _out1489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1490;
            DCOMP.COMP.GenExpr(_2354_on, selfIdent, @params, false, out _out1487, out _out1488, out _out1489, out _out1490);
            _2355_onString = _out1487;
            _2356_onOwned = _out1488;
            _2357_onErased = _out1489;
            _2358_recIdents = _out1490;
            if (!(_2357_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2359_eraseFn;
              _2359_eraseFn = ((_2356_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2355_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2359_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2355_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2351_isDatatype) || (_2352_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2355_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2353_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2352_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2355_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2353_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2358_recIdents;
          }
        } else if (_source74.is_Call) {
          DAST._IExpression _2360___mcc_h123 = _source74.dtor_on;
          Dafny.ISequence<Dafny.Rune> _2361___mcc_h124 = _source74.dtor_name;
          Dafny.ISequence<DAST._IType> _2362___mcc_h125 = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2363___mcc_h126 = _source74.dtor_args;
          bool _2364_isDatatype = _2137___mcc_h36;
          bool _2365_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2366_field = _2135___mcc_h34;
          DAST._IExpression _2367_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2368_onString;
            bool _2369_onOwned;
            bool _2370_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2371_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1491;
            bool _out1492;
            bool _out1493;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1494;
            DCOMP.COMP.GenExpr(_2367_on, selfIdent, @params, false, out _out1491, out _out1492, out _out1493, out _out1494);
            _2368_onString = _out1491;
            _2369_onOwned = _out1492;
            _2370_onErased = _out1493;
            _2371_recIdents = _out1494;
            if (!(_2370_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2372_eraseFn;
              _2372_eraseFn = ((_2369_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2368_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2372_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2368_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2364_isDatatype) || (_2365_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2368_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2366_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2365_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2368_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2366_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2371_recIdents;
          }
        } else if (_source74.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2373___mcc_h131 = _source74.dtor_params;
          DAST._IType _2374___mcc_h132 = _source74.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2375___mcc_h133 = _source74.dtor_body;
          bool _2376_isDatatype = _2137___mcc_h36;
          bool _2377_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2378_field = _2135___mcc_h34;
          DAST._IExpression _2379_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2380_onString;
            bool _2381_onOwned;
            bool _2382_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2383_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1495;
            bool _out1496;
            bool _out1497;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1498;
            DCOMP.COMP.GenExpr(_2379_on, selfIdent, @params, false, out _out1495, out _out1496, out _out1497, out _out1498);
            _2380_onString = _out1495;
            _2381_onOwned = _out1496;
            _2382_onErased = _out1497;
            _2383_recIdents = _out1498;
            if (!(_2382_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2384_eraseFn;
              _2384_eraseFn = ((_2381_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2380_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2384_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2380_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2376_isDatatype) || (_2377_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2380_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2378_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2377_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2380_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2378_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2383_recIdents;
          }
        } else if (_source74.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2385___mcc_h137 = _source74.dtor_name;
          DAST._IType _2386___mcc_h138 = _source74.dtor_typ;
          DAST._IExpression _2387___mcc_h139 = _source74.dtor_value;
          DAST._IExpression _2388___mcc_h140 = _source74.dtor_iifeBody;
          bool _2389_isDatatype = _2137___mcc_h36;
          bool _2390_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2391_field = _2135___mcc_h34;
          DAST._IExpression _2392_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2393_onString;
            bool _2394_onOwned;
            bool _2395_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2396_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1499;
            bool _out1500;
            bool _out1501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1502;
            DCOMP.COMP.GenExpr(_2392_on, selfIdent, @params, false, out _out1499, out _out1500, out _out1501, out _out1502);
            _2393_onString = _out1499;
            _2394_onOwned = _out1500;
            _2395_onErased = _out1501;
            _2396_recIdents = _out1502;
            if (!(_2395_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2397_eraseFn;
              _2397_eraseFn = ((_2394_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2393_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2397_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2393_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2389_isDatatype) || (_2390_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2393_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2391_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2390_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2393_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2391_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2396_recIdents;
          }
        } else if (_source74.is_Apply) {
          DAST._IExpression _2398___mcc_h145 = _source74.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2399___mcc_h146 = _source74.dtor_args;
          bool _2400_isDatatype = _2137___mcc_h36;
          bool _2401_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2402_field = _2135___mcc_h34;
          DAST._IExpression _2403_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2404_onString;
            bool _2405_onOwned;
            bool _2406_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2407_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1503;
            bool _out1504;
            bool _out1505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1506;
            DCOMP.COMP.GenExpr(_2403_on, selfIdent, @params, false, out _out1503, out _out1504, out _out1505, out _out1506);
            _2404_onString = _out1503;
            _2405_onOwned = _out1504;
            _2406_onErased = _out1505;
            _2407_recIdents = _out1506;
            if (!(_2406_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2408_eraseFn;
              _2408_eraseFn = ((_2405_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2404_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2408_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2404_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2400_isDatatype) || (_2401_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2404_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2402_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2401_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2404_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2402_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2407_recIdents;
          }
        } else if (_source74.is_TypeTest) {
          DAST._IExpression _2409___mcc_h149 = _source74.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2410___mcc_h150 = _source74.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2411___mcc_h151 = _source74.dtor_variant;
          bool _2412_isDatatype = _2137___mcc_h36;
          bool _2413_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2414_field = _2135___mcc_h34;
          DAST._IExpression _2415_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2416_onString;
            bool _2417_onOwned;
            bool _2418_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2419_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1507;
            bool _out1508;
            bool _out1509;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1510;
            DCOMP.COMP.GenExpr(_2415_on, selfIdent, @params, false, out _out1507, out _out1508, out _out1509, out _out1510);
            _2416_onString = _out1507;
            _2417_onOwned = _out1508;
            _2418_onErased = _out1509;
            _2419_recIdents = _out1510;
            if (!(_2418_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2420_eraseFn;
              _2420_eraseFn = ((_2417_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2416_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2420_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2416_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2412_isDatatype) || (_2413_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2416_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2414_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2413_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2416_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2414_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2419_recIdents;
          }
        } else {
          DAST._IType _2421___mcc_h155 = _source74.dtor_typ;
          bool _2422_isDatatype = _2137___mcc_h36;
          bool _2423_isConstant = _2136___mcc_h35;
          Dafny.ISequence<Dafny.Rune> _2424_field = _2135___mcc_h34;
          DAST._IExpression _2425_on = _2134___mcc_h33;
          {
            Dafny.ISequence<Dafny.Rune> _2426_onString;
            bool _2427_onOwned;
            bool _2428_onErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2429_recIdents;
            Dafny.ISequence<Dafny.Rune> _out1511;
            bool _out1512;
            bool _out1513;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1514;
            DCOMP.COMP.GenExpr(_2425_on, selfIdent, @params, false, out _out1511, out _out1512, out _out1513, out _out1514);
            _2426_onString = _out1511;
            _2427_onOwned = _out1512;
            _2428_onErased = _out1513;
            _2429_recIdents = _out1514;
            if (!(_2428_onErased)) {
              Dafny.ISequence<Dafny.Rune> _2430_eraseFn;
              _2430_eraseFn = ((_2427_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
              _2426_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2430_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2426_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if ((_2422_isDatatype) || (_2423_isConstant)) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2426_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2424_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()"));
              if (_2423_isConstant) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
              }
              if (mustOwn) {
                s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
                isOwned = true;
              } else {
                isOwned = false;
              }
            } else {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&(("), _2426_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".r#")), _2424_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".borrow()))"));
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
              isOwned = true;
            }
            isErased = false;
            readIdents = _2429_recIdents;
          }
        }
      } else if (_source22.is_SelectFn) {
        DAST._IExpression _2431___mcc_h157 = _source22.dtor_expr;
        Dafny.ISequence<Dafny.Rune> _2432___mcc_h158 = _source22.dtor_field;
        bool _2433___mcc_h159 = _source22.dtor_onDatatype;
        bool _2434___mcc_h160 = _source22.dtor_isStatic;
        BigInteger _2435___mcc_h161 = _source22.dtor_arity;
        BigInteger _2436_arity = _2435___mcc_h161;
        bool _2437_isStatic = _2434___mcc_h160;
        bool _2438_isDatatype = _2433___mcc_h159;
        Dafny.ISequence<Dafny.Rune> _2439_field = _2432___mcc_h158;
        DAST._IExpression _2440_on = _2431___mcc_h157;
        {
          Dafny.ISequence<Dafny.Rune> _2441_onString;
          bool _2442_onOwned;
          bool _2443___v78;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2444_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1515;
          bool _out1516;
          bool _out1517;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1518;
          DCOMP.COMP.GenExpr(_2440_on, selfIdent, @params, false, out _out1515, out _out1516, out _out1517, out _out1518);
          _2441_onString = _out1515;
          _2442_onOwned = _out1516;
          _2443___v78 = _out1517;
          _2444_recIdents = _out1518;
          if (_2437_isStatic) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2441_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _2439_field);
          } else {
            s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2441_onString), ((_2442_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
            Dafny.ISequence<Dafny.Rune> _2445_args;
            _2445_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            BigInteger _2446_i;
            _2446_i = BigInteger.Zero;
            while ((_2446_i) < (_2436_arity)) {
              if ((_2446_i).Sign == 1) {
                _2445_args = Dafny.Sequence<Dafny.Rune>.Concat(_2445_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2445_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2445_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), DCOMP.__default.natToString(_2446_i));
              _2446_i = (_2446_i) + (BigInteger.One);
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2445_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), _2439_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2445_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
            s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = true;
          readIdents = _2444_recIdents;
        }
      } else if (_source22.is_Index) {
        DAST._IExpression _2447___mcc_h162 = _source22.dtor_expr;
        bool _2448___mcc_h163 = _source22.dtor_isArray;
        Dafny.ISequence<DAST._IExpression> _2449___mcc_h164 = _source22.dtor_indices;
        Dafny.ISequence<DAST._IExpression> _2450_indices = _2449___mcc_h164;
        bool _2451_isArray = _2448___mcc_h163;
        DAST._IExpression _2452_on = _2447___mcc_h162;
        {
          Dafny.ISequence<Dafny.Rune> _2453_onString;
          bool _2454_onOwned;
          bool _2455_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2456_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1519;
          bool _out1520;
          bool _out1521;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1522;
          DCOMP.COMP.GenExpr(_2452_on, selfIdent, @params, false, out _out1519, out _out1520, out _out1521, out _out1522);
          _2453_onString = _out1519;
          _2454_onOwned = _out1520;
          _2455_onErased = _out1521;
          _2456_recIdents = _out1522;
          readIdents = _2456_recIdents;
          if (!(_2455_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2457_eraseFn;
            _2457_eraseFn = ((_2454_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2453_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2457_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2453_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2453_onString;
          BigInteger _2458_i;
          _2458_i = BigInteger.Zero;
          while ((_2458_i) < (new BigInteger((_2450_indices).Count))) {
            Dafny.ISequence<Dafny.Rune> _2459_idx;
            bool _2460___v79;
            bool _2461_idxErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2462_recIdentsIdx;
            Dafny.ISequence<Dafny.Rune> _out1523;
            bool _out1524;
            bool _out1525;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1526;
            DCOMP.COMP.GenExpr((_2450_indices).Select(_2458_i), selfIdent, @params, true, out _out1523, out _out1524, out _out1525, out _out1526);
            _2459_idx = _out1523;
            _2460___v79 = _out1524;
            _2461_idxErased = _out1525;
            _2462_recIdentsIdx = _out1526;
            if (!(_2461_idxErased)) {
              _2459_idx = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2459_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
            if (_2451_isArray) {
              s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
            }
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[<usize as ::dafny_runtime::NumCast>::from(")), _2459_idx), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()]"));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2462_recIdentsIdx);
            _2458_i = (_2458_i) + (BigInteger.One);
          }
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(&"), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            isOwned = false;
          }
          isErased = _2455_onErased;
        }
      } else if (_source22.is_IndexRange) {
        DAST._IExpression _2463___mcc_h165 = _source22.dtor_expr;
        bool _2464___mcc_h166 = _source22.dtor_isArray;
        DAST._IOptional<DAST._IExpression> _2465___mcc_h167 = _source22.dtor_low;
        DAST._IOptional<DAST._IExpression> _2466___mcc_h168 = _source22.dtor_high;
        DAST._IOptional<DAST._IExpression> _2467_high = _2466___mcc_h168;
        DAST._IOptional<DAST._IExpression> _2468_low = _2465___mcc_h167;
        bool _2469_isArray = _2464___mcc_h166;
        DAST._IExpression _2470_on = _2463___mcc_h165;
        {
          Dafny.ISequence<Dafny.Rune> _2471_onString;
          bool _2472_onOwned;
          bool _2473_onErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2474_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1527;
          bool _out1528;
          bool _out1529;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1530;
          DCOMP.COMP.GenExpr(_2470_on, selfIdent, @params, false, out _out1527, out _out1528, out _out1529, out _out1530);
          _2471_onString = _out1527;
          _2472_onOwned = _out1528;
          _2473_onErased = _out1529;
          _2474_recIdents = _out1530;
          readIdents = _2474_recIdents;
          if (!(_2473_onErased)) {
            Dafny.ISequence<Dafny.Rune> _2475_eraseFn;
            _2475_eraseFn = ((_2472_onOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("erase")));
            _2471_onString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::"), _2475_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2471_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          s = _2471_onString;
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2476_lowString;
          _2476_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source75 = _2468_low;
          if (_source75.is_Some) {
            DAST._IExpression _2477___mcc_h1055 = _source75.dtor_Some_a0;
            DAST._IExpression _2478_l = _2477___mcc_h1055;
            {
              Dafny.ISequence<Dafny.Rune> _2479_lString;
              bool _2480___v80;
              bool _2481_lErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2482_recIdentsL;
              Dafny.ISequence<Dafny.Rune> _out1531;
              bool _out1532;
              bool _out1533;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1534;
              DCOMP.COMP.GenExpr(_2478_l, selfIdent, @params, true, out _out1531, out _out1532, out _out1533, out _out1534);
              _2479_lString = _out1531;
              _2480___v80 = _out1532;
              _2481_lErased = _out1533;
              _2482_recIdentsL = _out1534;
              if (!(_2481_lErased)) {
                _2479_lString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2479_lString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2476_lowString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2479_lString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2482_recIdentsL);
            }
          } else {
          }
          DAST._IOptional<Dafny.ISequence<Dafny.Rune>> _2483_highString;
          _2483_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None();
          DAST._IOptional<DAST._IExpression> _source76 = _2467_high;
          if (_source76.is_Some) {
            DAST._IExpression _2484___mcc_h1056 = _source76.dtor_Some_a0;
            DAST._IExpression _2485_h = _2484___mcc_h1056;
            {
              Dafny.ISequence<Dafny.Rune> _2486_hString;
              bool _2487___v81;
              bool _2488_hErased;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2489_recIdentsH;
              Dafny.ISequence<Dafny.Rune> _out1535;
              bool _out1536;
              bool _out1537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1538;
              DCOMP.COMP.GenExpr(_2485_h, selfIdent, @params, true, out _out1535, out _out1536, out _out1537, out _out1538);
              _2486_hString = _out1535;
              _2487___v81 = _out1536;
              _2488_hErased = _out1537;
              _2489_recIdentsH = _out1538;
              if (!(_2488_hErased)) {
                _2486_hString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyErasable::erase_owned("), _2486_hString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              }
              _2483_highString = DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_Some(_2486_hString);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2489_recIdentsH);
            }
          } else {
          }
          if (_2469_isArray) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").borrow()"));
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source77) => {
            if (_source77.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2490___mcc_h1057 = _source77.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2490___mcc_h1057, _pat_let0_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let0_0, _2491_l => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2491_l), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2476_lowString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..")), ((System.Func<DAST._IOptional<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>>)((_source78) => {
            if (_source78.is_Some) {
              Dafny.ISequence<Dafny.Rune> _2492___mcc_h1058 = _source78.dtor_Some_a0;
              return Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_2492___mcc_h1058, _pat_let1_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let1_0, _2493_h => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), _2493_h), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))));
            } else {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
          }))(_2483_highString)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
          isErased = _2473_onErased;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".to_vec())"));
          isOwned = true;
        }
      } else if (_source22.is_TupleSelect) {
        DAST._IExpression _2494___mcc_h169 = _source22.dtor_expr;
        BigInteger _2495___mcc_h170 = _source22.dtor_index;
        BigInteger _2496_idx = _2495___mcc_h170;
        DAST._IExpression _2497_on = _2494___mcc_h169;
        {
          Dafny.ISequence<Dafny.Rune> _2498_onString;
          bool _2499___v82;
          bool _2500_tupErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2501_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1539;
          bool _out1540;
          bool _out1541;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1542;
          DCOMP.COMP.GenExpr(_2497_on, selfIdent, @params, false, out _out1539, out _out1540, out _out1541, out _out1542);
          _2498_onString = _out1539;
          _2499___v82 = _out1540;
          _2500_tupErased = _out1541;
          _2501_recIdents = _out1542;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2498_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").")), DCOMP.__default.natToString(_2496_idx));
          if (mustOwn) {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone()"));
            isOwned = true;
          } else {
            s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), s);
            isOwned = false;
          }
          isErased = _2500_tupErased;
          readIdents = _2501_recIdents;
        }
      } else if (_source22.is_Call) {
        DAST._IExpression _2502___mcc_h171 = _source22.dtor_on;
        Dafny.ISequence<Dafny.Rune> _2503___mcc_h172 = _source22.dtor_name;
        Dafny.ISequence<DAST._IType> _2504___mcc_h173 = _source22.dtor_typeArgs;
        Dafny.ISequence<DAST._IExpression> _2505___mcc_h174 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2506_args = _2505___mcc_h174;
        Dafny.ISequence<DAST._IType> _2507_typeArgs = _2504___mcc_h173;
        Dafny.ISequence<Dafny.Rune> _2508_name = _2503___mcc_h172;
        DAST._IExpression _2509_on = _2502___mcc_h171;
        {
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2510_typeArgString;
          _2510_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          if ((new BigInteger((_2507_typeArgs).Count)) >= (BigInteger.One)) {
            BigInteger _2511_typeI;
            _2511_typeI = BigInteger.Zero;
            _2510_typeArgString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<");
            while ((_2511_typeI) < (new BigInteger((_2507_typeArgs).Count))) {
              if ((_2511_typeI).Sign == 1) {
                _2510_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2510_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              Dafny.ISequence<Dafny.Rune> _2512_typeString;
              Dafny.ISequence<Dafny.Rune> _out1543;
              _out1543 = DCOMP.COMP.GenType((_2507_typeArgs).Select(_2511_typeI), false, false);
              _2512_typeString = _out1543;
              _2510_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2510_typeArgString, _2512_typeString);
              _2511_typeI = (_2511_typeI) + (BigInteger.One);
            }
            _2510_typeArgString = Dafny.Sequence<Dafny.Rune>.Concat(_2510_typeArgString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
          Dafny.ISequence<Dafny.Rune> _2513_argString;
          _2513_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2514_i;
          _2514_i = BigInteger.Zero;
          while ((_2514_i) < (new BigInteger((_2506_args).Count))) {
            if ((_2514_i).Sign == 1) {
              _2513_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2513_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2515_argExpr;
            bool _2516_isOwned;
            bool _2517_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2518_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1544;
            bool _out1545;
            bool _out1546;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1547;
            DCOMP.COMP.GenExpr((_2506_args).Select(_2514_i), selfIdent, @params, false, out _out1544, out _out1545, out _out1546, out _out1547);
            _2515_argExpr = _out1544;
            _2516_isOwned = _out1545;
            _2517_argErased = _out1546;
            _2518_argIdents = _out1547;
            if (_2516_isOwned) {
              _2515_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2515_argExpr);
            }
            _2513_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2513_argString, _2515_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2518_argIdents);
            _2514_i = (_2514_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2519_enclosingString;
          bool _2520___v83;
          bool _2521___v84;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2522_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1548;
          bool _out1549;
          bool _out1550;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1551;
          DCOMP.COMP.GenExpr(_2509_on, selfIdent, @params, false, out _out1548, out _out1549, out _out1550, out _out1551);
          _2519_enclosingString = _out1548;
          _2520___v83 = _out1549;
          _2521___v84 = _out1550;
          _2522_recIdents = _out1551;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2522_recIdents);
          DAST._IExpression _source79 = _2509_on;
          if (_source79.is_Literal) {
            DAST._ILiteral _2523___mcc_h1059 = _source79.dtor_Literal_a0;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Ident) {
            Dafny.ISequence<Dafny.Rune> _2524___mcc_h1061 = _source79.dtor_Ident_a0;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2525___mcc_h1063 = _source79.dtor_Companion_a0;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2519_enclosingString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), (_2508_name));
            }
          } else if (_source79.is_Tuple) {
            Dafny.ISequence<DAST._IExpression> _2526___mcc_h1065 = _source79.dtor_Tuple_a0;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_New) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2527___mcc_h1067 = _source79.dtor_path;
            Dafny.ISequence<DAST._IExpression> _2528___mcc_h1068 = _source79.dtor_args;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_NewArray) {
            Dafny.ISequence<DAST._IExpression> _2529___mcc_h1071 = _source79.dtor_dims;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_DatatypeValue) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2530___mcc_h1073 = _source79.dtor_path;
            Dafny.ISequence<Dafny.Rune> _2531___mcc_h1074 = _source79.dtor_variant;
            bool _2532___mcc_h1075 = _source79.dtor_isCo;
            Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2533___mcc_h1076 = _source79.dtor_contents;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Convert) {
            DAST._IExpression _2534___mcc_h1081 = _source79.dtor_value;
            DAST._IType _2535___mcc_h1082 = _source79.dtor_from;
            DAST._IType _2536___mcc_h1083 = _source79.dtor_typ;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_SeqValue) {
            Dafny.ISequence<DAST._IExpression> _2537___mcc_h1087 = _source79.dtor_elements;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_SetValue) {
            Dafny.ISequence<DAST._IExpression> _2538___mcc_h1089 = _source79.dtor_elements;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_This) {
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Ite) {
            DAST._IExpression _2539___mcc_h1091 = _source79.dtor_cond;
            DAST._IExpression _2540___mcc_h1092 = _source79.dtor_thn;
            DAST._IExpression _2541___mcc_h1093 = _source79.dtor_els;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_UnOp) {
            DAST._IUnaryOp _2542___mcc_h1097 = _source79.dtor_unOp;
            DAST._IExpression _2543___mcc_h1098 = _source79.dtor_expr;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_BinOp) {
            Dafny.ISequence<Dafny.Rune> _2544___mcc_h1101 = _source79.dtor_op;
            DAST._IExpression _2545___mcc_h1102 = _source79.dtor_left;
            DAST._IExpression _2546___mcc_h1103 = _source79.dtor_right;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_ArrayLen) {
            DAST._IExpression _2547___mcc_h1107 = _source79.dtor_expr;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Select) {
            DAST._IExpression _2548___mcc_h1109 = _source79.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2549___mcc_h1110 = _source79.dtor_field;
            bool _2550___mcc_h1111 = _source79.dtor_isConstant;
            bool _2551___mcc_h1112 = _source79.dtor_onDatatype;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_SelectFn) {
            DAST._IExpression _2552___mcc_h1117 = _source79.dtor_expr;
            Dafny.ISequence<Dafny.Rune> _2553___mcc_h1118 = _source79.dtor_field;
            bool _2554___mcc_h1119 = _source79.dtor_onDatatype;
            bool _2555___mcc_h1120 = _source79.dtor_isStatic;
            BigInteger _2556___mcc_h1121 = _source79.dtor_arity;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Index) {
            DAST._IExpression _2557___mcc_h1127 = _source79.dtor_expr;
            bool _2558___mcc_h1128 = _source79.dtor_isArray;
            Dafny.ISequence<DAST._IExpression> _2559___mcc_h1129 = _source79.dtor_indices;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_IndexRange) {
            DAST._IExpression _2560___mcc_h1133 = _source79.dtor_expr;
            bool _2561___mcc_h1134 = _source79.dtor_isArray;
            DAST._IOptional<DAST._IExpression> _2562___mcc_h1135 = _source79.dtor_low;
            DAST._IOptional<DAST._IExpression> _2563___mcc_h1136 = _source79.dtor_high;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_TupleSelect) {
            DAST._IExpression _2564___mcc_h1141 = _source79.dtor_expr;
            BigInteger _2565___mcc_h1142 = _source79.dtor_index;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Call) {
            DAST._IExpression _2566___mcc_h1145 = _source79.dtor_on;
            Dafny.ISequence<Dafny.Rune> _2567___mcc_h1146 = _source79.dtor_name;
            Dafny.ISequence<DAST._IType> _2568___mcc_h1147 = _source79.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _2569___mcc_h1148 = _source79.dtor_args;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2570___mcc_h1153 = _source79.dtor_params;
            DAST._IType _2571___mcc_h1154 = _source79.dtor_retType;
            Dafny.ISequence<DAST._IStatement> _2572___mcc_h1155 = _source79.dtor_body;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_IIFE) {
            Dafny.ISequence<Dafny.Rune> _2573___mcc_h1159 = _source79.dtor_name;
            DAST._IType _2574___mcc_h1160 = _source79.dtor_typ;
            DAST._IExpression _2575___mcc_h1161 = _source79.dtor_value;
            DAST._IExpression _2576___mcc_h1162 = _source79.dtor_iifeBody;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_Apply) {
            DAST._IExpression _2577___mcc_h1167 = _source79.dtor_expr;
            Dafny.ISequence<DAST._IExpression> _2578___mcc_h1168 = _source79.dtor_args;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else if (_source79.is_TypeTest) {
            DAST._IExpression _2579___mcc_h1171 = _source79.dtor_on;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2580___mcc_h1172 = _source79.dtor_dType;
            Dafny.ISequence<Dafny.Rune> _2581___mcc_h1173 = _source79.dtor_variant;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          } else {
            DAST._IType _2582___mcc_h1177 = _source79.dtor_typ;
            {
              _2519_enclosingString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _2519_enclosingString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").r#")), (_2508_name));
            }
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2519_enclosingString, _2510_typeArgString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2513_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_Lambda) {
        Dafny.ISequence<DAST._IFormal> _2583___mcc_h175 = _source22.dtor_params;
        DAST._IType _2584___mcc_h176 = _source22.dtor_retType;
        Dafny.ISequence<DAST._IStatement> _2585___mcc_h177 = _source22.dtor_body;
        Dafny.ISequence<DAST._IStatement> _2586_body = _2585___mcc_h177;
        DAST._IType _2587_retType = _2584___mcc_h176;
        Dafny.ISequence<DAST._IFormal> _2588_params = _2583___mcc_h175;
        {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2589_paramNames;
          _2589_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
          BigInteger _2590_i;
          _2590_i = BigInteger.Zero;
          while ((_2590_i) < (new BigInteger((_2588_params).Count))) {
            _2589_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2589_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(((_2588_params).Select(_2590_i)).dtor_name));
            _2590_i = (_2590_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2591_recursiveGen;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2592_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1552;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1553;
          DCOMP.COMP.GenStmts(_2586_body, DAST.Optional<Dafny.ISequence<Dafny.Rune>>.create_None(), _2589_paramNames, true, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), out _out1552, out _out1553);
          _2591_recursiveGen = _out1552;
          _2592_recIdents = _out1553;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          Dafny.ISequence<Dafny.Rune> _2593_allReadCloned;
          _2593_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          while (!(_2592_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
            Dafny.ISequence<Dafny.Rune> _2594_next;
            foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_1 in (_2592_recIdents).Elements) {
              _2594_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_1;
              if ((_2592_recIdents).Contains(_2594_next)) {
                goto after__ASSIGN_SUCH_THAT_1;
              }
            }
            throw new System.Exception("assign-such-that search produced no value (line 1757)");
          after__ASSIGN_SUCH_THAT_1:;
            if (!((_2589_paramNames).Contains(_2594_next))) {
              _2593_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2593_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let r#")), _2594_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = r#")), _2594_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2594_next));
            }
            _2592_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2592_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2594_next));
          }
          Dafny.ISequence<Dafny.Rune> _2595_paramsString;
          _2595_paramsString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          _2590_i = BigInteger.Zero;
          while ((_2590_i) < (new BigInteger((_2588_params).Count))) {
            if ((_2590_i).Sign == 1) {
              _2595_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(_2595_paramsString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2596_typStr;
            Dafny.ISequence<Dafny.Rune> _out1554;
            _out1554 = DCOMP.COMP.GenType(((_2588_params).Select(_2590_i)).dtor_typ, false, true);
            _2596_typStr = _out1554;
            _2595_paramsString = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2595_paramsString, ((_2588_params).Select(_2590_i)).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": &")), _2596_typStr);
            _2590_i = (_2590_i) + (BigInteger.One);
          }
          Dafny.ISequence<Dafny.Rune> _2597_retTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1555;
          _out1555 = DCOMP.COMP.GenType(_2587_retType, false, true);
          _2597_retTypeGen = _out1555;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::FunctionWrapper({\n"), _2593_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::boxed::Box::new(move |")), _2595_paramsString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| -> ")), _2597_retTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), _2591_recursiveGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n})})"));
          isOwned = true;
          isErased = true;
        }
      } else if (_source22.is_IIFE) {
        Dafny.ISequence<Dafny.Rune> _2598___mcc_h178 = _source22.dtor_name;
        DAST._IType _2599___mcc_h179 = _source22.dtor_typ;
        DAST._IExpression _2600___mcc_h180 = _source22.dtor_value;
        DAST._IExpression _2601___mcc_h181 = _source22.dtor_iifeBody;
        DAST._IExpression _2602_iifeBody = _2601___mcc_h181;
        DAST._IExpression _2603_value = _2600___mcc_h180;
        DAST._IType _2604_tpe = _2599___mcc_h179;
        Dafny.ISequence<Dafny.Rune> _2605_name = _2598___mcc_h178;
        {
          Dafny.ISequence<Dafny.Rune> _2606_valueGen;
          bool _2607_valueOwned;
          bool _2608_valueErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2609_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1556;
          bool _out1557;
          bool _out1558;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1559;
          DCOMP.COMP.GenExpr(_2603_value, selfIdent, @params, false, out _out1556, out _out1557, out _out1558, out _out1559);
          _2606_valueGen = _out1556;
          _2607_valueOwned = _out1557;
          _2608_valueErased = _out1558;
          _2609_recIdents = _out1559;
          if (_2608_valueErased) {
            Dafny.ISequence<Dafny.Rune> _2610_eraseFn;
            _2610_eraseFn = ((_2607_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
            _2606_valueGen = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyUnerasable::<_>::"), _2610_eraseFn), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2606_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
          readIdents = _2609_recIdents;
          Dafny.ISequence<Dafny.Rune> _2611_valueTypeGen;
          Dafny.ISequence<Dafny.Rune> _out1560;
          _out1560 = DCOMP.COMP.GenType(_2604_tpe, false, true);
          _2611_valueTypeGen = _out1560;
          Dafny.ISequence<Dafny.Rune> _2612_bodyGen;
          bool _2613_bodyOwned;
          bool _2614_bodyErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2615_bodyIdents;
          Dafny.ISequence<Dafny.Rune> _out1561;
          bool _out1562;
          bool _out1563;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1564;
          DCOMP.COMP.GenExpr(_2602_iifeBody, selfIdent, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(@params, ((_2607_valueOwned) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_2605_name))))), mustOwn, out _out1561, out _out1562, out _out1563, out _out1564);
          _2612_bodyGen = _out1561;
          _2613_bodyOwned = _out1562;
          _2614_bodyErased = _out1563;
          _2615_bodyIdents = _out1564;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2615_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_2605_name))));
          Dafny.ISequence<Dafny.Rune> _2616_eraseFn;
          _2616_eraseFn = ((_2607_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase_owned")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unerase")));
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet r#"), (_2605_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((_2607_valueOwned) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")))), _2611_valueTypeGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2606_valueGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n")), _2612_bodyGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n}"));
          isOwned = _2613_bodyOwned;
          isErased = _2614_bodyErased;
        }
      } else if (_source22.is_Apply) {
        DAST._IExpression _2617___mcc_h182 = _source22.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _2618___mcc_h183 = _source22.dtor_args;
        Dafny.ISequence<DAST._IExpression> _2619_args = _2618___mcc_h183;
        DAST._IExpression _2620_func = _2617___mcc_h182;
        {
          Dafny.ISequence<Dafny.Rune> _2621_funcString;
          bool _2622___v87;
          bool _2623_funcErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2624_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1565;
          bool _out1566;
          bool _out1567;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1568;
          DCOMP.COMP.GenExpr(_2620_func, selfIdent, @params, false, out _out1565, out _out1566, out _out1567, out _out1568);
          _2621_funcString = _out1565;
          _2622___v87 = _out1566;
          _2623_funcErased = _out1567;
          _2624_recIdents = _out1568;
          readIdents = _2624_recIdents;
          Dafny.ISequence<Dafny.Rune> _2625_argString;
          _2625_argString = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
          BigInteger _2626_i;
          _2626_i = BigInteger.Zero;
          while ((_2626_i) < (new BigInteger((_2619_args).Count))) {
            if ((_2626_i).Sign == 1) {
              _2625_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2625_argString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
            }
            Dafny.ISequence<Dafny.Rune> _2627_argExpr;
            bool _2628_isOwned;
            bool _2629_argErased;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2630_argIdents;
            Dafny.ISequence<Dafny.Rune> _out1569;
            bool _out1570;
            bool _out1571;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1572;
            DCOMP.COMP.GenExpr((_2619_args).Select(_2626_i), selfIdent, @params, false, out _out1569, out _out1570, out _out1571, out _out1572);
            _2627_argExpr = _out1569;
            _2628_isOwned = _out1570;
            _2629_argErased = _out1571;
            _2630_argIdents = _out1572;
            if (_2628_isOwned) {
              _2627_argExpr = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), _2627_argExpr);
            }
            _2625_argString = Dafny.Sequence<Dafny.Rune>.Concat(_2625_argString, _2627_argExpr);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2630_argIdents);
            _2626_i = (_2626_i) + (BigInteger.One);
          }
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), _2621_funcString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2625_argString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("))"));
          isOwned = true;
          isErased = false;
        }
      } else if (_source22.is_TypeTest) {
        DAST._IExpression _2631___mcc_h184 = _source22.dtor_on;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2632___mcc_h185 = _source22.dtor_dType;
        Dafny.ISequence<Dafny.Rune> _2633___mcc_h186 = _source22.dtor_variant;
        Dafny.ISequence<Dafny.Rune> _2634_variant = _2633___mcc_h186;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2635_dType = _2632___mcc_h185;
        DAST._IExpression _2636_on = _2631___mcc_h184;
        {
          Dafny.ISequence<Dafny.Rune> _2637_exprGen;
          bool _2638___v88;
          bool _2639_exprErased;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2640_recIdents;
          Dafny.ISequence<Dafny.Rune> _out1573;
          bool _out1574;
          bool _out1575;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out1576;
          DCOMP.COMP.GenExpr(_2636_on, selfIdent, @params, false, out _out1573, out _out1574, out _out1575, out _out1576);
          _2637_exprGen = _out1573;
          _2638___v88 = _out1574;
          _2639_exprErased = _out1575;
          _2640_recIdents = _out1576;
          Dafny.ISequence<Dafny.Rune> _2641_dTypePath;
          Dafny.ISequence<Dafny.Rune> _out1577;
          _out1577 = DCOMP.COMP.GenPath(_2635_dType);
          _2641_dTypePath = _out1577;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!("), _2637_exprGen), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".as_ref(), ")), _2641_dTypePath), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::r#")), _2634_variant), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. })"));
          isOwned = true;
          isErased = true;
          readIdents = _2640_recIdents;
        }
      } else {
        DAST._IType _2642___mcc_h187 = _source22.dtor_typ;
        DAST._IType _2643_typ = _2642___mcc_h187;
        {
          Dafny.ISequence<Dafny.Rune> _2644_typString;
          Dafny.ISequence<Dafny.Rune> _out1578;
          _out1578 = DCOMP.COMP.GenType(_2643_typ, false, false);
          _2644_typString = _out1578;
          s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _2644_typString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()"));
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
      BigInteger _2645_i;
      _2645_i = BigInteger.Zero;
      while ((_2645_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2646_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        Dafny.ISequence<Dafny.Rune> _out1579;
        _out1579 = DCOMP.COMP.GenModule((p).Select(_2645_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2646_generated = _out1579;
        if ((_2645_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2646_generated);
        _2645_i = (_2645_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName) {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2647_i;
      _2647_i = BigInteger.Zero;
      while ((_2647_i) < (new BigInteger((fullName).Count))) {
        if ((_2647_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (fullName).Select(_2647_i));
        _2647_i = (_2647_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
  }
} // end of namespace DCOMP

